from openai import OpenAI

import json

class ModelCalling:

    def __init__(self, model = None, key = "None", url = None, params = dict(), system_prompt = ""):

        self.model = model
        self.key = key
        self.url = url
        self.params = params
        self.system_prompt = system_prompt

        self.client = OpenAI(
            api_key=self.key,
            base_url=self.url,
            timeout=180.0,
            max_retries=2
        )


    def model_call(self, query):
        
        messages = [
            {"role": "system", "content": self.system_prompt},
            {"role": "user", "content": query}
        ]

        rtn = {
                "success": False,
                "response": ""
            }
        
        try:
            request_params = {
                "model": self.model,
                "messages": messages,
                "temperature": self.params.get('temperature', 0.6),
                "max_tokens": self.params.get('max_tokens', 16384),
                "top_p": self.params.get('top_p', 0.95),
                "extra_body": {"top_k": self.params.get('top_k', 20),},
            }

            if self.params.get('use_json',False): request_params['response_format'] = {"type": "json_object"}
            
            chat_response = self.client.chat.completions.create(**request_params)

            # chat_response = self.client.chat.completions.create(
            #     model=self.model,
            #     messages=messages,
            #     max_tokens=self.params.get('max_tokens', 16384),
            #     temperature=self.params.get('temperature', 0.6),
            #     top_p=self.params.get('top_p', 0.95),
            #     timeout=180,
            #     extra_body={
            #         "top_k": self.params.get('top_k', 20),
            #     },
            #     # response_format = {"type": "json_object"}
            # )

            response_text = chat_response.choices[0].message.content
            rtn['success'] = True
            # if self.params.get('use_json',False): response_text = json.loads(response_text)
            rtn['response'] = response_text
        
        except Exception as e:
            print(e)
            rtn['response'] = str(e)
        
        finally:
            return rtn


if __name__ == "__main__":

    import json
    import os



    from datetime import datetime
    from dotenv import load_dotenv
    from pathlib import Path
    from model_calling import ModelCalling
    from lean_verifier import LeanVerifier
    from safe_writer import ThreadSafeJSONLWriter
    from question_formalizer_v0 import QuestionFormalizer



    env_path = Path(__file__).parent / ".env"
    load_dotenv(dotenv_path=env_path)
    url = os.getenv('GOEDEL_BASE_URL')


    def read_md_as_text(file_path):
        """Read markdown file as plain text"""
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        return content
    
    prompt_file = r"/mnt/disk0/t00917290/imo_autoformalization/main/mayi/prompts/test.md"

    system_prompt = read_md_as_text(prompt_file)

    formalizer = ModelCalling("Qwen3_coder",url="http://localhost:13423/v1",system_prompt = system_prompt)

    informal = '''
Let $(a_n)_{n \\ge 0}$ be a strictly increasing sequence of positive integers such that:\n* For all $k \\ge 1$, $a_k$ divides $2(a_0 + a_1 + \\dots + a_{k - 1})$.\n* For each prime $p$, there exists some $k$ such that $p$ divides $a_k$.\n\nProve that for any positive integer $n$, there exists some $k$ such that $n$ divides $a_k$.
'''

    user_prompt = f'''
Rephrase the following math question.

{informal}

Put the output in the following format.

<statement> the rephrased math statement </statement>

'''


    result = formalizer.model_call(user_prompt)

    print(result['response'])