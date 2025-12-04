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

Informal:

Find all real values of $r$ that satisfy $\\frac1r > \\frac1{{r-1}} + \\frac1{{r-4}}.$ (Give your answer in interval notation.)

Formal:

import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

noncomputable def solution : Set ℝ := sorry



theorem  question89_18_135 (r : ℝ) :
    r ∈ solution ↔ (r ≠ 0 ∧ r ≠ 1 ∧ r ≠ 4 ∧ (1 : ℝ)/r > (1 : ℝ)/(r-1) + (1 : ℝ)/(r-4)) := by
  rw [solution]

Use the following proof as reference

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
