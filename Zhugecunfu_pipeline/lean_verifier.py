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


if __name__ == "__main__":
    
    
    import json

    # file_name = r"/mnt/disk0/t00917290/imo_autoformalization/main/mayi/competition_data/result/1118/submission_1118.jsonl"

    # data = []
    # with open(file_name, 'r', encoding = 'utf-8') as f:
    #     for line in f:
    #         data.append(json.loads(line))

    LEAN_SERVER_URL="http://localhost:14457"
    # LEAN_SERVER_URL="http://localhost:14000"
    leanverifier = LeanVerifier(LEAN_SERVER_URL)

    # n = len(data)
    # cnt = 0
    # for d in data:
    #     # if d['id'] != "c21": continue
    #     lean_verification = leanverifier.verify_code(d['formal_code'])
    #     # print(lean_verification['raw_result'])
    #     if lean_verification['is_valid'] and lean_verification['no_sorries']: cnt += 1

    # print(cnt, ' / ', n)

    # sys.exit()

    lean_code = '''
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

noncomputable def solution : Set ℝ := Set.Iio (-2) ∪ Set.Ioo 0 1 ∪ Set.Ioo 2 4



theorem  question89_18_135 (r : ℝ) :
    r ∈ solution ↔ (r ≠ 0 ∧ r ≠ 1 ∧ r ≠ 4 ∧ (1 : ℝ)/r > (1 : ℝ)/(r-1) + (1 : ℝ)/(r-4)) := by
  rw [solution]
  by_cases hr: r > 4
  . constructor
    <;> intro h
    simp at h
    rcases h with h|h
    rcases h with h|h
    nlinarith
    nlinarith
    nlinarith
    obtain ⟨h1,h2,h3,h4⟩ := h
    have : (r - 1) * (r - 4) > r * (r - 4) + r * (r - 1) := by
      have hr1 : r > 0 := by linarith
      have hr2 : r - 1 > 0 := by linarith
      have hr3 : r - 4 > 0 := by linarith
      have h := calc
        (r - 1) * (r - 4) / (r * (r - 1) * (r - 4))
            = 1 / r := by field_simp
        _ > 1 / (r - 1) + 1 / (r - 4) := h4
        _ = (r * (r - 4) + r * (r - 1)) / (r * (r - 1) * (r - 4)) := by field_simp
      have hr4 : r * (r - 1) * (r - 4) > 0 := by positivity
      have : (r - 1) * (r - 4) / (r * (r - 1) * (r - 4)) * (r * (r - 1) * (r - 4)) >
         (r * (r - 4) + r * (r - 1)) / (r * (r - 1) * (r - 4)) * (r * (r - 1) * (r - 4)) := by
        apply mul_lt_mul_of_pos_right h hr4
      have hr5 : r * (r - 1) * (r - 4) ≠ 0 := by linarith
      rw [div_mul_cancel₀ _ hr5, div_mul_cancel₀ _ hr5] at this
      exact this
    have : 4 > r ^ 2 := by
      have h1: (r-1)*(r-4) = r^2-5*r+4 := by
        ring
      have h2: r * (r - 4) + r * (r - 1) = 2*r^2 - 5*r := by
        ring
      rw [h1,h2] at this
      nlinarith
    nlinarith
  . push_neg at hr
    by_cases hr1 : r > 1
    . constructor
      <;> intro h
      simp at h
      rcases h with h|h
      rcases h with h|h
      nlinarith
      nlinarith
      constructor
      linarith
      constructor
      linarith
      constructor
      linarith
      obtain ⟨h1,h2⟩ := h
      by_contra hc
      push_neg at hc
      have hr1 : r > 0 := by linarith
      have hr2 : r - 1 > 0 := by linarith
      have hr3 : r - 4 < 0 := by linarith
      have h1 : r ≠ 0 := by linarith
      have h2 : r - 1 ≠ 0 := by linarith
      have h3 : r - 4 ≠ 0 := by linarith
      have : (r - 1) * (r - 4) ≥ r * (r - 4) + r * (r - 1) := by
        have h := calc
          (r - 1) * (r - 4) / (r * (r - 1) * (r - 4))
              = 1 / r := by field_simp
          _ ≤  1 / (r - 1) + 1 / (r - 4) := hc
          _ = (r * (r - 4) + r * (r - 1)) / (r * (r - 1) * (r - 4)) := by field_simp
        have hr4 : r * (r - 1) * (r - 4) ≤ 0 := by
          have : r * (r - 1) * (r - 4) < 0 := mul_neg_of_pos_of_neg (mul_pos hr1 hr2) hr3
          linarith
        have := mul_le_mul_of_nonpos_right h hr4
        have this₁ : r * (r - 1) * (r - 4) < 0 := mul_neg_of_pos_of_neg (mul_pos hr1 hr2) hr3
        have this₂ : r * (r - 1) * (r - 4) ≠ 0 := by nlinarith
        rw [div_mul_cancel₀ _ this₂, div_mul_cancel₀ _ this₂] at this
        linarith
      have : 4 ≥ r^2 := by
        have h1: (r-1)*(r-4) = r^2-5*r+4 := by
          ring
        have h2: r * (r - 4) + r * (r - 1) = 2*r^2 - 5*r := by
          ring
        rw [h1,h2] at this
        nlinarith
      nlinarith
      obtain ⟨h1,h2,h3,h4⟩ := h
      have hr1 : r > 0 := by linarith
      have hr2 : r - 1 > 0 := by linarith
      have hr_3 : r < 4 := by exact Ne.lt_of_le h3 hr
      have hr3 : r - 4 < 0 := by
        by_cases temp: r < 4
        linarith
        push_neg at temp
        linarith
      have : (r - 1) * (r - 4) < r * (r - 4) + r * (r - 1) := by
        have h1 : r ≠ 0 := by linarith
        have h2 : r - 1 ≠ 0 := by linarith
        have h3 : r - 4 ≠ 0 := by linarith
        have h := calc
          (r - 1) * (r - 4) / (r * (r - 1) * (r - 4))
              = 1 / r := by
              field_simp
          _ > 1 / (r - 1) + 1 / (r - 4) := h4
          _ = (r * (r - 4) + r * (r - 1)) / (r * (r - 1) * (r - 4)) := by field_simp
        have hr4 : r * (r - 1) * (r - 4) < 0 := by
          apply mul_neg_of_pos_of_neg
          · apply mul_pos hr1 hr2
          · exact hr3
        have : (r - 1) * (r - 4) / (r * (r - 1) * (r - 4)) * (r * (r - 1) * (r - 4)) <
          (r * (r - 4) + r * (r - 1)) / (r * (r - 1) * (r - 4)) * (r * (r - 1) * (r - 4)) := by
          apply mul_lt_mul_of_neg_right h hr4
        have hr5 : r * (r - 1) * (r - 4) ≠ 0 := by linarith
        rw [div_mul_cancel₀ _ hr5, div_mul_cancel₀ _ hr5] at this
        exact this
      have : 4 < r ^ 2 := by
        have h1: (r-1)*(r-4) = r^2-5*r+4 := by
          ring
        have h2: r * (r - 4) + r * (r - 1) = 2*r^2 - 5*r := by
          ring
        rw [h1,h2] at this
        nlinarith
      simp
      apply Or.inr
      have : r < -2 ∨ 2 < r := by
        by_contra h
        push_neg at h
        have : r ^ 2 ≤ 4 := by nlinarith [sq_nonneg r, sq_nonneg (r - 2), sq_nonneg (r + 2)]
        linarith
      rcases this with h|h
      linarith
      exact And.intro h hr_3
    push_neg at hr1
    by_cases hr2 : r > 0
    . constructor
      <;> intro h
      simp at h
      rcases h with h|h
      rcases h with h|h
      nlinarith
      constructor
      linarith
      constructor
      linarith
      constructor
      linarith
      by_contra hc
      push_neg at hc
      have hr1 : r > 0 := by linarith
      have hr2 : r - 1 < 0 := by linarith
      have hr3 : r - 4 < 0 := by linarith
      have h1 : r ≠ 0 := by linarith
      have h2 : r - 1 ≠ 0 := by linarith
      have h3 : r - 4 ≠ 0 := by linarith
      have : (r - 1) * (r - 4) ≤ r * (r - 4) + r * (r - 1) := by
        have h := calc
          (r - 1) * (r - 4) / (r * (r - 1) * (r - 4))
              = 1 / r := by field_simp
          _ ≤  1 / (r - 1) + 1 / (r - 4) := hc
          _ = (r * (r - 4) + r * (r - 1)) / (r * (r - 1) * (r - 4)) := by field_simp
        have hr4 : r * (r - 1) * (r - 4) ≥ 0 := by
          nlinarith [sq_nonneg (r - 1), sq_nonneg (r - 4)]
        have := mul_le_mul_of_nonneg_right h hr4
        have this₁ : r * (r - 1) * (r - 4) > 0 := by 
          nlinarith [sq_nonneg (r - 1), sq_nonneg (r - 4)]
        have this₂ : r * (r - 1) * (r - 4) ≠ 0 := by nlinarith
        rw [div_mul_cancel₀ _ this₂, div_mul_cancel₀ _ this₂] at this
        linarith
      have : 4 ≥ r^2 := by
        have h1: (r-1)*(r-4) = r^2-5*r+4 := by
          ring
        have h2: r * (r - 4) + r * (r - 1) = 2*r^2 - 5*r := by
          ring
        rw [h1,h2] at this
        nlinarith
      nlinarith
      nlinarith
      obtain ⟨h1,h2,h3,h4⟩ := h
      have hr1₁ : r > 0 := by linarith
      have hr_2 : r < 1 := by exact Ne.lt_of_le h2 hr1
      have hr2 : r - 1 < 0 := by linarith
      simp
      apply Or.inl
      apply Or.inr
      constructor
      linarith
      assumption
    push_neg at hr2
    constructor
    <;> intro h
    simp at h
    rcases h with h|h
    rcases h with h|h
    constructor
    linarith
    constructor
    linarith
    constructor
    linarith
    by_contra hc
    push_neg at hc
    have hr1 : r ≤ 0 := by linarith
    have hr2 : r - 1 < 0 := by linarith
    have hr3 : r - 4 < 0 := by linarith
    have h1 : r ≠ 0 := by linarith
    have h2 : r - 1 ≠ 0 := by linarith
    have h3 : r - 4 ≠ 0 := by linarith
    have : (r - 1) * (r - 4) ≥ r * (r - 4) + r * (r - 1) := by
      have h := calc
        (r - 1) * (r - 4) / (r * (r - 1) * (r - 4))
            = 1 / r := by field_simp
        _ ≤  1 / (r - 1) + 1 / (r - 4) := hc
        _ = (r * (r - 4) + r * (r - 1)) / (r * (r - 1) * (r - 4)) := by field_simp
      have hr4 : r * (r - 1) * (r - 4) ≤ 0 := by
        nlinarith [sq_nonneg (r - 1), sq_nonneg (r - 4)]
      have := mul_le_mul_of_nonpos_right h hr4
      have this₁ : r * (r - 1) * (r - 4) < 0 := by 
          nlinarith [sq_nonneg (r - 1), sq_nonneg (r - 4)]
      have this₂ : r * (r - 1) * (r - 4) ≠ 0 := by nlinarith
      rw [div_mul_cancel₀ _ this₂, div_mul_cancel₀ _ this₂] at this
      linarith
    have : 4 ≥ r^2 := by
      have h1: (r-1)*(r-4) = r^2-5*r+4 := by
        ring
      have h2: r * (r - 4) + r * (r - 1) = 2*r^2 - 5*r := by
        ring
      rw [h1,h2] at this
      nlinarith
    nlinarith
    nlinarith
    nlinarith
    obtain ⟨h1,h2,h3,h4⟩ := h
    have hr1 : r < 0 := by
      exact Ne.lt_of_le h1 hr2
    have hr2 : r - 1 < 0 := by linarith
    have hr_3 : r < 4 := by exact Ne.lt_of_le h3 hr
    have hr3 : r - 4 < 0 := by
      by_cases temp: r < 4
      linarith
      push_neg at temp
      linarith
    have : (r - 1) * (r - 4) < r * (r - 4) + r * (r - 1) := by
      have h1 : r ≠ 0 := by linarith
      have h2 : r - 1 ≠ 0 := by linarith
      have h3 : r - 4 ≠ 0 := by linarith
      have h := calc
        (r - 1) * (r - 4) / (r * (r - 1) * (r - 4))
            = 1 / r := by
            field_simp
        _ > 1 / (r - 1) + 1 / (r - 4) := h4
        _ = (r * (r - 4) + r * (r - 1)) / (r * (r - 1) * (r - 4)) := by field_simp
      have hr4 : r * (r - 1) * (r - 4) < 0 := by
        nlinarith [sq_nonneg (r - 1), sq_nonneg (r - 4)]
      have : (r - 1) * (r - 4) / (r * (r - 1) * (r - 4)) * (r * (r - 1) * (r - 4)) <
        (r * (r - 4) + r * (r - 1)) / (r * (r - 1) * (r - 4)) * (r * (r - 1) * (r - 4)) := by
        apply mul_lt_mul_of_neg_right h hr4
      have hr5 : r * (r - 1) * (r - 4) ≠ 0 := by linarith
      rw [div_mul_cancel₀ _ hr5, div_mul_cancel₀ _ hr5] at this
      exact this
    have : 4 < r ^ 2 := by
      have h1: (r-1)*(r-4) = r^2-5*r+4 := by
        ring
      have h2: r * (r - 4) + r * (r - 1) = 2*r^2 - 5*r := by
        ring
      rw [h1,h2] at this
      nlinarith
    simp
    apply Or.inl
    apply Or.inl
    have : r < -2 ∨ 2 < r := by
      by_contra h
      push_neg at h
      have : r ^ 2 ≤ 4 := by nlinarith [sq_nonneg r, sq_nonneg (r - 2), sq_nonneg (r + 2)]
      linarith
    rcases this with h|h
    assumption
    nlinarith

'''

    lean_verification = leanverifier.verify_code(lean_code)

    print(lean_verification)

    # result = lean_verification['raw_result']['messages']

    # print(result)

    # error_dict = dict()
    # for msg in result:
    #     if msg['severity'] == 'error':
    #         error_dict = msg
    #         break
    
    # correct_until = error_dict['pos']['line']

    # lean_code = lean_code.strip()
    # lean_code_lines = lean_code.split('\n')
    # idx = 0
    # while lean_code_lines[idx].find('import') != -1: idx +=1
    # while lean_code_lines[idx] == '': idx += 1
    # lean_code = '\n'.join(lean_code_lines[:idx + correct_until])

    # print(lean_code)
    # print(error_dict['data'])
