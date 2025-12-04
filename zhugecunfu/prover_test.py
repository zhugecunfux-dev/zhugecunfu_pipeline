import json
import os
import sys


from datetime import datetime
from dotenv import load_dotenv
from pathlib import Path
from model_calling import ModelCalling
from lean_verifier import LeanVerifier
from safe_writer import ThreadSafeJSONLWriter
from question_formalizer_v0 import QuestionFormalizer
from concurrent.futures import ThreadPoolExecutor, as_completed
from utils.text_extractor import extract_lean_code,_parse_json_response


input_file = r"/mnt/disk0/t00917290/imo_autoformalization/main/mayi/competition_data/output/1127/lean_1127_20251127_091212.jsonl"
data = []

with open(input_file, 'r', encoding = 'utf-8') as f:
    for line in f:
        data.append(json.loads(line))

my_input = []
for _ in range(8):
    for d in data:
        my_input.append(d)


LEAN_SERVER_URL="http://localhost:14457"
leanverifier = LeanVerifier(LEAN_SERVER_URL)

system_prompt = '''You are an expert in mathematics and Lean 4.'''

prover = ModelCalling("kimina_72b", url = "http://localhost:13421/v1", system_prompt = system_prompt)


output_file = r"/mnt/disk0/t00917290/imo_autoformalization/main/mayi/competition_data/result/1127/proof_1127_"
output_file += datetime.now().strftime("%Y%m%d_%H%M%S")
output_file += ".jsonl"
jsonwriter = ThreadSafeJSONLWriter(output_file)


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

        for _ in range(2):

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



with ThreadPoolExecutor(max_workers=8) as executor:
    futures = [executor.submit(prove, d['id'], d['nl_problem'], d['formal']) for d in my_input]

    cnt = 0
    for future in as_completed(futures):
        my_result = future.result()
        jsonwriter.write(my_result)
        print("Problem " + str(cnt) + " DONE!")
        cnt+=1
