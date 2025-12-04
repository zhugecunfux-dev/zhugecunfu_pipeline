import json
import os



from datetime import datetime
from dotenv import load_dotenv
from pathlib import Path
from model_calling import ModelCalling
from lean_verifier import LeanVerifier
from safe_writer import ThreadSafeJSONLWriter
from question_formalizer_v1 import QuestionFormalizer



env_path = Path(__file__).parent / ".env"
load_dotenv(dotenv_path=env_path)
url = os.getenv('GOEDEL_BASE_URL')


def read_md_as_text(file_path):
    """Read markdown file as plain text"""
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    return content


params = dict()


file_path = r"/mnt/disk0/t00917290/imo_autoformalization/main/mayi/prompts/system_prompt_formalizer.md"
system_prompt = read_md_as_text(file_path)

formalizer = ModelCalling("goedel_v3",url="http://localhost:13425/v1",system_prompt = system_prompt)

LEAN_SERVER_URL="http://localhost:14457"
leanverifier = LeanVerifier(LEAN_SERVER_URL)


file_path = r"/mnt/disk0/t00917290/imo_autoformalization/main/mayi/prompts/system_prompt_semantic.md"
system_prompt = read_md_as_text(file_path)
params['temperature'] = 0.5
params['use_json'] = True

semantic_checker = ModelCalling("Qwen3_critic",url="http://localhost:13424/v1",system_prompt = system_prompt, params = params)


params = dict()
params['max_lean_generation'] = 5
params['max_full_check'] = 7


output_file = r"/mnt/disk0/t00917290/imo_autoformalization/main/mayi/competition_data/output/1127/lean_1127_"
output_file += datetime.now().strftime("%Y%m%d_%H%M%S")
output_file += ".jsonl"
jsonwriter = ThreadSafeJSONLWriter(output_file)





file_path = r"/mnt/disk0/t00917290/imo_autoformalization/main/mayi/competition_data/source/lean_1127.jsonl"
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
with open(output_file,'r',encoding='utf-8') as f:
    for line in f:
        data.append(json.loads(line))

data = [{'id':thm_to_id[thm['informal']], 'nl_problem':thm['informal'], 'formal':thm['formal']} for thm in data]

with open(output_file,'w',encoding='utf-8') as f:
    for d in data:
        f.write(json.dumps(d,ensure_ascii=False) + '\n')



# informal = '''A graph is defined in polar coordinates by $r = \\cos \\theta + \\frac{1}{2}.$  Find the smallest $x$-coordinate of any point on this graph.'''
# print(questionformalizer.formalize_single(informal)['formal'])