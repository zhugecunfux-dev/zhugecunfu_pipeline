import json
from datetime import datetime
from pathlib import Path
from model_calling import ModelCalling
from lean_verifier import LeanVerifier
from safe_writer import ThreadSafeJSONLWriter
from concurrent.futures import ThreadPoolExecutor, as_completed
from utils.text_extractor import extract_lean_code, _parse_json_response
import config


# Load input file (from formalization output)
input_file = config.PROVING_INPUT_FILE
data = []

with open(str(input_file), 'r', encoding='utf-8') as f:
    for line in f:
        data.append(json.loads(line))

# Replicate input for multiple proving attempts
my_input = []
for _ in range(config.PROVING_REPETITIONS):
    for d in data:
        my_input.append(d)

# Initialize Lean verifier
leanverifier = LeanVerifier(config.LEAN_SERVER_URL)

# Initialize prover model
system_prompt = '''You are an expert in mathematics and Lean 4.'''
prover = ModelCalling(
    config.PROVER_MODEL_NAME,
    url=config.PROVER_BASE_URL,
    system_prompt=system_prompt,
    params=config.PROVER_PARAMS
)

# Setup output file
config.PROVING_OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
output_file = config.PROVING_OUTPUT_DIR / f"proof_{datetime.now().strftime('%Y%m%d_%H%M%S')}.jsonl"
jsonwriter = ThreadSafeJSONLWriter(str(output_file))


def prove(id,informal, formal):
    rtn = {
        'success': False,
        'id': id,
        'informal': informal,
        'lean_code': "",
    }

    try:
        user_prompt = f'''
Think about and solve the following problem step by step in Lean 4.
DO NOT modify the Lean code except that replace `sorry` accordingly.
If there is a `solution` variable, ensure that 
    - Solve the question first
    - Do not put the set in the theorem in solution variable
    - the plugged value is in the simplest form
    - DO NOT use the built-in Lean 4 functions

{informal}

{formal}
    '''

        extra_user_prompt = ""

        for _ in range(config.MAX_PROVING_ATTEMPTS):

            print('user prompt: ')
            print(user_prompt + extra_user_prompt)
            print('\n'*5)

            prover_response = prover.model_call(user_prompt + extra_user_prompt)
          
            lean_code = extract_lean_code(prover_response['response'])

            if lean_code == "": continue


            lean_verification = leanverifier.verify_code(lean_code)

            is_valid = lean_verification['is_valid']
            no_sorries = lean_verification['no_sorries']

            if is_valid and no_sorries: 
                rtn['success'] = True
                rtn['lean_code'] = lean_code
                break
            
            result = lean_verification['raw_result']['messages']
            error_dict = dict()
            for msg in result:
                if msg['severity'] == 'error':
                    error_dict = msg
                    break
            
            correct_until = error_dict['pos']['line']

            lean_code = lean_code.strip()
            lean_code_lines = lean_code.split('\n')
            idx = 0
            while lean_code_lines[idx].find('import') != -1: idx +=1
            while lean_code_lines[idx] == '': idx += 1
            lean_code = '\n'.join(lean_code_lines[:idx + correct_until])

            extra_user_prompt = ""

            extra_user_prompt += "Previous generation with error: \n\n"
            extra_user_prompt += f"{lean_code} \n\n"
            extra_user_prompt += "Error messages: \n\n"
            extra_user_prompt += f"{error_dict['data']}"
    except Exception as e:
        print(str(e))


    return rtn



with ThreadPoolExecutor(max_workers=config.PROVING_MAX_WORKERS) as executor:
    futures = [executor.submit(prove, d['id'], d['nl_problem'], d['formal']) for d in my_input]

    cnt = 0
    for future in as_completed(futures):
        my_result = future.result()
        jsonwriter.write(my_result)
        print("Problem " + str(cnt) + " DONE!")
        cnt+=1
