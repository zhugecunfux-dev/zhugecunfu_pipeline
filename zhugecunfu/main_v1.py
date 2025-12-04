import json
import os
from datetime import datetime
from dotenv import load_dotenv
from pathlib import Path
from model_calling import ModelCalling
from lean_verifier import LeanVerifier
from safe_writer import ThreadSafeJSONLWriter
from question_formalizer_v1 import QuestionFormalizer
import config



env_path = Path(__file__).parent / ".env"
load_dotenv(dotenv_path=env_path)
url = os.getenv('YOUR_LOCAL_URL')


def read_md_as_text(file_path):
    """Read markdown file as plain text"""
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    return content


# Load system prompts from config
formalizer_system_prompt = read_md_as_text(config.FORMALIZER_PROMPT_PATH)
semantic_system_prompt = read_md_as_text(config.SEMANTIC_CHECKER_PROMPT_PATH)

# Initialize models
formalizer = ModelCalling(
    config.FORMALIZER_MODEL_NAME,
    url=config.FORMALIZER_BASE_URL,
    system_prompt=formalizer_system_prompt,
    params=config.FORMALIZER_PARAMS
)

leanverifier = LeanVerifier(config.LEAN_SERVER_URL)

semantic_checker = ModelCalling(
    config.SEMANTIC_CHECKER_MODEL_NAME,
    url=config.SEMANTIC_CHECKER_BASE_URL,
    system_prompt=semantic_system_prompt,
    params=config.SEMANTIC_CHECKER_PARAMS
)


# Pipeline parameters
params = dict()
params['max_lean_generation'] = config.MAX_LEAN_GENERATION
params['max_full_check'] = config.MAX_FULL_CHECK

# Setup output file
config.FORMALIZATION_OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
output_file = config.FORMALIZATION_OUTPUT_DIR / f"formalization_{datetime.now().strftime('%Y%m%d_%H%M%S')}.jsonl"
jsonwriter = ThreadSafeJSONLWriter(str(output_file))

# Load input file
file_path = config.FORMALIZATION_INPUT_FILE
informals = []

thm_to_id = dict()

with open(file_path, 'r', encoding = 'utf-8') as f:
    for line in f:
        thm = json.loads(line)
        # if thm['id'] != 'c706': continue
        informals.append(thm['nl_problem'])
        thm_to_id[thm['nl_problem']] = thm['id']



questionformalizer = QuestionFormalizer(informals, formalizer, leanverifier,semantic_checker, jsonwriter,params)



questionformalizer.formalize_all()


data = []
with open(str(output_file),'r',encoding='utf-8') as f:
    for line in f:
        data.append(json.loads(line))

data = [{'id':thm_to_id[thm['informal']], 'nl_problem':thm['informal'], 'formal':thm['formal']} for thm in data]

with open(str(output_file),'w',encoding='utf-8') as f:
    for d in data:
        f.write(json.dumps(d,ensure_ascii=False) + '\n')



# informal = '''A graph is defined in polar coordinates by $r = \\cos \\theta + \\frac{1}{2}.$  Find the smallest $x$-coordinate of any point on this graph.'''
# print(questionformalizer.formalize_single(informal)['formal'])
