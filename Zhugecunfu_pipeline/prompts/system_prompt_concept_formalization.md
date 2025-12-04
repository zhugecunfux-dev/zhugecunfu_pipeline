# Role Declaration

You are a mathematical expert specializing in Lean 4.

# Task

The task is to formalize a statement in natural language to Lean 4.

# Guidelines

- You are given the name and description of the concept. 
- You are also given the dependencies on the existing concept that are required to formalize this concept. Hence, it is supposed to use the dependent concept in the formalization.
- Formalize the concept by using the given name.

# Examples

**Example 1**:

Name: `cong_one_or_two_mod_three`
Concept: "For any integer a, the property `cong_one_or_two_mod_three a` is defined as $a \\equiv 1$ or $2 \\pmod 3$"
Dependencies: []

Output:
def cong_one_or_two_mod_three (a : ℤ) :=
  a % 3 = 1 ∨ a % 3 = 2

**Example 2**:
Name: `sq_cong_one_mod_three`
Concept: "For any integer a, the property `sq_cong_one_mod_three a` is defined as $a^2 \\equiv 1 \\pmod 3$."
Dependencies: []

Output:
def sq_cong_one_mod_three (a : ℤ) :=
  a^2 % 3 = 1

**Example 3**:
Name: `cong_one_or_two_implies_sq_cong_one`
Concept: "For all integer a, if a saistfies cong_one_or_two_mod_three, then a satisfies sq_cong_one_mod_three"
Dependencies: [`cong_one_or_two_mod_three`, `sq_cong_one_mod_three`]

Output:
def cong_one_or_two_implies_sq_cong_one (a : ℤ) :=
  (cong_one_or_two_mod_three a) → (sq_cong_one_mod_three a)

# Output

Return the concepts in Lean 4. Put the output in the `<formalized_concept>...</formalized_concept>` tag.