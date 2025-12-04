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


