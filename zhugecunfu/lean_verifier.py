import sys 

from kimina_client import KiminaClient, Snippet

class LeanVerifier:

    def __init__(self, api_url: str = None):
        self.client = KiminaClient(api_url=api_url) 

    def verify_code(self, lean_code: str):

        rtn = {
                "is_valid": False,
                "no_sorries": False,
                "raw_result": None,
            }

        try:

            snippets = [Snippet(id=str(idx), code=proof) for idx, proof in enumerate([lean_code])]
            timeout = 60
            compilation_result = self.client.check(
                snips=snippets,
                timeout=timeout,
                max_workers=10,
            )

            results = compilation_result.results[0].response

            is_valid = True

            if 'messages' in results:
                for msg in results['messages']:
                    if msg['severity'] == 'error': is_valid = False

            rtn['no_sorries'] = not ('sorries' in results)
            
            rtn["is_valid"] = is_valid
            rtn["raw_result"] = results
        
        except Exception as e:
            print(e)

        finally:
            return rtn
