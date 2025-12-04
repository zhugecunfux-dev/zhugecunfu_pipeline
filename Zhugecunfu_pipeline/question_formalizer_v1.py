from utils.text_extractor import extract_lean_code,_parse_json_response
from concurrent.futures import ThreadPoolExecutor, as_completed
from model_calling import ModelCalling
from lean_verifier import LeanVerifier
from safe_writer import ThreadSafeJSONLWriter

class QuestionFormalizer:

    def __init__(self, informals, formalizer, lean_verifier, semantic_checker, jsonwriter, params = dict()):

        self.informals = informals
        self.formalizer = formalizer
        self.lean_verifier = lean_verifier
        self.semantic_checker = semantic_checker
        self.params = params
        self.jsonwriter = jsonwriter


    def check_content_correspondence(self, informal, formal):

        try:
            user_prompt = (
                f"Please judge whether the following informal mathematical problem and Lean code correspond in mathematical content.\n\n"
                f"Informal problem:\n{informal}\n\n"
                f"Lean code:\n{formal}\n\n"
                f"Provide your answer in EXACTLY this JSON format:\n"
                f'{{"correspondence": true, "reason": "explanation"}}\n'
                f'OR\n'
                f'{{"correspondence": false, "reason": "detailed explanation of the mismatch"}}\n\n'
                f"IMPORTANT: Output ONLY valid JSON, no additional text."
            )
            
            semantic_checker_response = self.semantic_checker.model_call(user_prompt)
            
            if not semantic_checker_response['success']:
                return -1, "API call failed"
            
            response = semantic_checker_response['response']


            json_data = _parse_json_response(response)
            if json_data and "correspondence" in json_data:
                corresponds = json_data["correspondence"]
                error_reason = json_data.get("reason", "")
                
                # Handle various "none" representations
                if error_reason.lower() in ['none', 'n/a', 'null', 'no error', '']:
                    error_reason = ""
                
                status = 1 if corresponds else 0
                return status, error_reason

        
        except Exception as e:
            print(str(e))
        
        return -1, "Failed to parse response"
    

    def formalize(self,informal, semantic_comments):

        user_prompt = (
            f"Please autoformalize the following natural language problem statement in Lean 4. "
            f"The natural language statement is: \n\n"
            f"{informal}\n\n"
        )

        user_prompt += semantic_comments

        max_lean_generation = self.params.get('max_lean_generation', 5)

        while max_lean_generation > 0:
            max_lean_generation -= 1

            formalizer_response = self.formalizer.model_call(user_prompt)

            formal = extract_lean_code(formalizer_response['response'])

            if formal == "": continue

            lean_verification = self.lean_verifier.verify_code(formal)
            is_valid = lean_verification['is_valid']

            if is_valid: return formal

            msgs = lean_verification['raw_result']['messages']
            error_dict = dict()
            for msg in msgs:
                if msg['severity'] == 'error':
                    error_dict = msg
                    break
            
            correct_until = error_dict['pos']['line']

            lean_code_lines = formal.split('\n')
            lean_code_lines = [line for line in lean_code_lines if line != '']
            incorrect_formal = '\n'.join(lean_code_lines[:correct_until])

            if extra_lean_user_prompt == "":
                extra_lean_user_prompt += "Previous generations have the following syntax errors.\nRewrite the Lean code to avoid the errors.\n\n"

            user_prompt += "Lean code: \n\n" + incorrect_formal + '\n\n'
            user_prompt += "Error: \n\n" + error_dict['data'] + '\n\n'
        


    def formalize_single(self, informal):

        rtn = {
            "success": False,
            "informal": informal,
            "formal": ""
        }
        try:

            user_prompt = (
                f"Please autoformalize the following natural language problem statement in Lean 4. "
                f"The natural language statement is: \n\n"
                f"{informal}\n\n"
            )

            max_lean_generation = self.params.get('max_lean_generation', 5)
            max_full_check = self.params.get('max_full_check', 5)

            extra_semantic_user_prompt = ''
            num_full_check = max_full_check

            while num_full_check > 0:

                num_full_check -= 1

                extra_lean_user_prompt = ""
                num_lean_generation = max_lean_generation

                while num_lean_generation > 0:

                    num_lean_generation -= 1

                    # print(user_prompt+ extra_semantic_user_prompt + extra_lean_user_prompt)


                    formalizer_response = self.formalizer.model_call(user_prompt+ extra_semantic_user_prompt + extra_lean_user_prompt)


                    formal = extract_lean_code(formalizer_response['response'])

                    if formal == "": continue

                    lean_verification = self.lean_verifier.verify_code(formal)
                    is_valid = lean_verification['is_valid']

                    if is_valid:
                        rtn['formal'] = formal
                        break

                    msgs = lean_verification['raw_result']['messages']
                    error_dict = dict()
                    for msg in msgs:
                        if msg['severity'] == 'error':
                            error_dict = msg
                            break
                    
                    correct_until = error_dict['pos']['line']

                    lean_code_lines = formal.split('\n')
                    lean_code_lines = [line for line in lean_code_lines if line != '']
                    incorrect_formal = '\n'.join(lean_code_lines[:correct_until])

                    if extra_lean_user_prompt == "":
                        extra_lean_user_prompt += "Previous generations have the following syntax errors.\nRewrite the Lean code to avoid the errors.\n\n"

                    extra_lean_user_prompt += "Lean code: \n\n" + incorrect_formal + '\n\n'
                    extra_lean_user_prompt += "Error: \n\n" + error_dict['data'] + '\n\n'
                
                if num_lean_generation == 0: break


                check_pass, reason = self.check_content_correspondence(informal, rtn['formal'])

                if check_pass == -1: continue

                if check_pass == 1:
                    rtn ['success'] = True
                    break

                if extra_semantic_user_prompt == "":
                    extra_semantic_user_prompt += "Previous generations have the following semantic comment.\nIf the comment is correct, rewrite the Lean code accordingly; otherwise, keep the ignore the comment.\n\n"
                
                extra_semantic_user_prompt += "Lean code: \n\n" + rtn['formal'] + '\n\n'
                extra_semantic_user_prompt += "Error: \n\n" + reason + '\n\n'



        
        except Exception as e:
            print(str(e))

        return rtn


    def formalize_all(self):
        
        with ThreadPoolExecutor(max_workers=100) as executor:
            futures = [executor.submit(self.formalize_single, informal) for informal in self.informals]

            cnt = 0
            for future in as_completed(futures):
                my_result = future.result()
                self.jsonwriter.write(my_result)
                print("Problem " + str(cnt) + " DONE!")
                cnt+=1

    def formalize_all_seq(self):

        cnt = 0
        for informal in self.informals:
            my_result = self.formalize_single(informal)
            self.jsonwriter.write(my_result)
            print("Problem " + str(cnt) + " DONE!")
            cnt+=1
        
                

