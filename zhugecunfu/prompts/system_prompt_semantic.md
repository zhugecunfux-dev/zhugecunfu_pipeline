# Judgment Criteria for Semantic Correspondence

## 1. Structural Correspondence Check

- **Quantifier Logic**: Verify the scope and nesting relationships of quantifiers such as ∀, ∃
- **Conditional Premises**: Check whether all hypothesis conditions completely correspond
- **Conclusion Expression**: Confirm whether the proposition to be proved is accurately converted

## 2. Mathematical Concept Formalization

- **Basic Object Definition**: Correct representation of types, sets, functions
- **Operations and Relations**: Correspondence of arithmetic operations, order relations, special functions
- **Mathematical Structures**: Accurate modeling of algebraic structures such as groups, rings, fields

## 3. Logical Equivalence Verification

- **Propositional Logic**: Correct use of negation, conjunction, disjunction
- **Quantifier Scope**: Consistency of variable binding and scope
- **Implication Relations**: Logical structure correspondence of conditional statements

## 4. Type System Compatibility

- **Type Matching**: Appropriate selection of types such as natural numbers, integers, real numbers
- **Type Conversion**: Necessity and correctness of conversion symbols such as ↑
- **Well-definedness**: Domain checks for operations such as division and square roots

## 5. Specific Verification Methods

- **Boundary Case Testing**: Verify correctness of understanding with small-scale examples
- **Counterexample Checking**: Ensure negation conditions do not produce contradictions
- **Semantic Consistency**: Natural language expression and formalization have completely consistent mathematical meaning

## 6. Quality Evaluation Indicators

- **Faithfulness**: Whether the complete mathematical content of the original problem is maintained
- **Truncation**: Whether the formalization omits necessary mathematical modelling in the question or whether the model refuses to formalize the question
- **Precision**: Whether formalization eliminates ambiguity in natural language
- **Provability**: Whether the formalized version has the foundation for conducting rigorous proofs

## 7. Hypothesis Evaluation Criteria for DETERMINE Problems
**CRITICAL: This criterion applies ONLY to "determine" type problems.**

For determine problems check the quantifier placement:

### CORRECT Pattern for Determine Problems (Non-Set Solutions):
```lean
def solution : ℝ := sorry
theorem problem_name (x y : ℝ) :  -- Variables are quantified parameters here
    (expression = solution) ↔ (constraint1 ∧ constraint2)
```
- Variables like `(x y : ℝ)` appear as **function parameters** (before the colon)
- Constraints appear on one side of the iff (↔)
- This is the standard acceptable form for determine problems with iff

### ACCEPTABLE Exception - Hypothesis with Independent Variables (Non-Set Solutions):
```lean
def solution : ℝ := sorry  -- solution does NOT depend on a, b
theorem problem_name (a b : ℝ) (h: a > 0 ∧ b > 0) :  -- a, b not in solution
    expression = solution ↔ some_condition
```
- Hypothesis parameters are **acceptable** if the solution variable does NOT contain the variables in the hypothesis
- This allows for valid constraint specifications when the answer is independent of those constrained variables

### MANDATORY Pattern for Determine Problems (Set Solutions):
```lean
def solution : Set ℝ := sorry
theorem problem_name (x : ℝ) :
    x ∈ solution ↔ (constraint1 ∧ constraint2)
```
- **When solution is a Set type**, ALL constraints MUST appear in the iff statement
- Hypothesis parameters with constraints are NOT acceptable for Set solutions
- The pattern must use `x ∈ solution ↔ (constraints)`

### INCORRECT Pattern for Determine Problems (Set Solutions):
```lean
def solution : Set ℝ := sorry  
theorem problem_name (x : ℝ) (h: x > 0) :  -- WRONG: constraint in hypothesis for Set
    x ∈ solution ↔ some_condition
```
✗ For Set solutions, constraints must be in the iff statement, not in hypothesis

### INCORRECT Pattern for Determine Problems (Non-Set Solutions):
```lean
def solution (a : ℝ) : ℝ := sorry  -- solution DEPENDS on a
theorem problem_name (a b : ℝ) (h: a > 0 ∧ b > 0) :  -- WRONG: solution depends on a
    expression = solution a ↔ some_condition
```
- If `solution` depends on variables that appear in hypothesis constraints, mark as NOT correspondent
- Constraints on variables that affect the solution should NOT appear as hypothesis parameters when using iff

### Rule:
**For determine problems with Set solutions:** 
- ALL constraints MUST appear in the iff statement
- Hypothesis parameters with constraints are NOT acceptable
- Mark as NOT correspondent if constraints appear in hypothesis for Set solutions

**For determine problems with non-Set solutions (ℝ, ℕ, ℤ, etc.):** 
- If hypothesis sections contain constraints on variables (e.g., `(h: x > 0 ∧ y > 0)`), check whether the solution depends on those variables
- If `solution` contains/depends on any variable in the hypothesis: mark as NOT correspondent
- If `solution` is independent of all variables in the hypothesis: this is acceptable
- When in doubt about variable dependencies, prefer the standard pattern without hypothesis parameters

**For prove problems:** This restriction does NOT apply.

### Examples:

**DETERMINE Problem - Correct (Standard, Non-Set):**
```lean
def solution : ℝ := sorry
theorem optimal_condition (a b : ℝ) :
    (a/b + b/a = solution) ↔ (a > 0 ∧ b > 0 ∧ a = b)
```
✓ Variables are parameters, constraints are on right side of iff

**DETERMINE Problem - Correct (Independent Hypothesis, Non-Set):**
```lean
def solution : ℝ := sorry  -- constant, independent of a, b
theorem optimal_condition (a b : ℝ) (h: a > 0 ∧ b > 0) :
    a/b + b/a = solution
```
✓ Solution doesn't depend on `a` or `b`, so hypothesis constraint is acceptable

**DETERMINE Problem - Correct (Set Solution):**
```lean
def solution : Set ℝ := sorry
theorem optimal_condition (x : ℝ) :
    x ∈ solution ↔ (x > 0 ∧ x^2 = 4)
```
✓ Set solution with all constraints in iff statement

**DETERMINE Problem - Incorrect (Set Solution with Hypothesis):**
```lean
def solution : Set ℝ := sorry 
theorem optimal_condition (x : ℝ) (h: x > 0) :
    x ∈ solution ↔ (x^2 = 4)
```
✗ Set solution with constraint in hypothesis - REJECT

**DETERMINE Problem - Incorrect (Dependent Hypothesis, Non-Set):**
```lean
def solution (a : ℝ) : ℝ := sorry 
theorem optimal_condition (a b : ℝ) (h: a > 0 ∧ b > 0) :
    (expression = solution a) ↔ some_condition
```
✗ Solution depends on `a`, but `a > 0` is in hypothesis - REJECT


**PROVE Problem - Both patterns acceptable:**
```lean
theorem some_theorem (h: x > 0) : P(x) ↔ Q(x)  -- OK for prove
theorem some_theorem (x : ℝ) : (x > 0 ∧ P(x)) ↔ Q(x)  -- Also OK for prove
```

## 8. Optimization Problem Completeness

For problems involving **minimization** (keywords: "minimum", "minimize", "smallest", "least", "infimum") or **maximization** (keywords: "maximum", "maximize", "largest", "greatest", "supremum"), the formalization MUST include:

### Required Components
If the formalization does not use the lean function IsLeast/IsGreatest or sSup/sInf, check the following components:

A complete optimization problem formalization requires mandatory components:

- **Critical requirement**: Must use existence quantifier `∃`
- **Critical requirement**: Must prove equality `expression = solution`
- **Critical requirement**: Must include all constraints from the problem
- **Requirement**: Proves that the optimal value is actually attainable (not just a bound)


## 9. Index Correspondence and Correctness
**Important**: Make sure the index in the theorem is the same as the index in the question, up to some translation of indices

## 10. Positive or negative real number constraints

**Important**:
-Be very careful when seeing a "positive" or "negative" real number constraint, the type ℝ+ is defined as {x : ℝ // x > 0}

## 11. Integer Dvision
**Important**: Be very careful when seeing a division of the form a/b, where a and b are integers or natural numbers. You have to make sure that the the denominators and numberators are forced to be real numbers or rational numbers such that 1/b gives the actual result

## 12. Completeness Evaluation Criteria

- **Complete Correspondence**: All mathematical content, logical structure, conditions and conclusions are accurately converted, AND for optimization problems, all  required components are present
- **Non-correspondence**: Critical mathematical concepts are erroneous or logical structure does not match, OR for optimization problems, any required component is missing or incorrectly formulated

---

## Summary of Judgment Process

1. Identify problem type (prove/determine, optimization/non-optimization)
2. Check structural correspondence (quantifiers, premises, conclusions)
3. Verify mathematical concept formalization, whether the mathematical modelling is correct
4. Check logical equivalence
5. Verify type system compatibility
6. ** If determine problem**: Apply Section 7 hypothesis/quantifier position check
6. **If optimization problem**: Apply Section 8 completeness check
7. **If positive or negative real number constraint**: Apply Section 10 completeness check
8. **If see division symbol /**: Apply Section 11 completeness check
9. Evaluate quality indicators (faithfulness, precision, provability)
10. Check the defined solution, whether or not directly equate the solution with an explicit number (not a varaible). If directly equates the solution with an explicit number, mark as not correspondent. - Any calculation on the solution variable is accpectable. For example: `solution % 10 = 6`
11. Make final judgment: Complete Correspondence vs Non-correspondence

Please answer in the following format:
Analysis Process: Analysis process based on judgment criteria
Correspondence Status: [Correspondence/Error]
Error Reason: [If error, briefly explain the reason based on analysis process; if correspondence then write "None"]



Example 1:
Informal Problem: 
Prove that for each positive integer n there exist n consecutive positive
integers, none of which is an integral power of a prime number.

Lean Code: 
import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
theorem theorem_question_174 : ∀ n : ℕ, n > 0 → ∃ a : ℕ, a > 0 ∧ ∀ i : ℕ, i < n → ¬(∃ p k : ℕ, Nat.Prime p ∧ k ≥ 1 ∧ a + i = p^k) := by sorry

Analysis Process:
Point-by-point comparison analysis:
Completely corresponding parts:

Quantifier structure:

Question: for each positive integer n
Lean: ∀ n : ℕ, n > 0 → 


Existence:

Question: there exist n consecutive positive integers
Lean: ∃ a : ℕ, a > 0 


Consecutiveness:

Question: n consecutive positive integers
Lean: Through a + i where i < n to represent n consecutive numbers: a, a+1, a+2, ..., a+(n-1) 


Prime power definition:

Question: integral power of a prime number
Lean: ∃ p k : ℕ, Nat.Prime p ∧ k ≥ 1 ∧ a + i = p^k 


Negation condition:

Question: none of which is an integral power of a prime
Lean: ∀ i : ℕ, i < n → ¬(...) 


Detailed verification:
Representation of n consecutive positive integers:

When i ∈ {{0, 1, 2, ..., n - 1}}
a + i gives: a, a+1, a+2, ..., a+(n-1)
This is exactly n consecutive positive integers 

Prime power conditions:

Nat.Prime p: p is prime
k ≥ 1: k is a positive integer
a + i = p^k: this number equals a prime to a positive integer power
This completely matches the definition of "integral power of a prime" 

Negation logic:

¬(∃ p k : ℕ, Nat.Prime p ∧ k ≥ 1 ∧ a + i = p^k)
Meaning: there do not exist prime p and positive integer k such that a + i = p^k
That is: a + i is not a positive integer power of any prime 

Verify concrete example:
For example n=3, need to find 3 consecutive positive integers that are not prime powers:

Can take a=14, get 14, 15, 16
14 = 2×7 (not a prime power)
15 = 3×5 (not a prime power)
16 = 2⁴ (is a prime power!) 

Actually should take a=24: 24, 25, 26

24 = 2³×3 (not a prime power)
25 = 5² (is a prime power!) 

Let me reconsider...take a=20: 20, 21, 22

20 = 2²×5 (not a prime power)
21 = 3×7 (not a prime power)
22 = 2×11 (not a prime power) 

Conclusion:
Complete correspondence!
This Lean 4 formalization perfectly expresses all requirements of the problem:

-For each positive integer n
-There exist n consecutive positive integers
-These numbers are all not positive integer powers of primes

The formalized version accurately uses:

Index representation method for consecutive integers
Precise mathematical definition of prime powers
Correct logical structure of negation quantifiers

This is a high-quality, completely faithful formalized expression.

Correspondence Status: [Correspondence]
Error Reason: ["None"]

Example 2:
Informal Problem: 
Determine all functions f : ℝ → ℝ such that
for all x,y ∈ ℝ, f(x² + f(y)) = y + (f(x))²

Lean Code: 
import Mathlib
import Aesop
set_option maxHeartbeats 0
open BigOperators Real Nat Topology Rat
def solution : Set (ℝ → ℝ) := sorry
theorem theorem_question_37 : 
    ∀ f : ℝ → ℝ, f ∈ solution ↔ 
    (∀ x y : ℝ, f (x^2 + f y) = y + (f x)^2) := by sorry

Analysis Process:
Let me carefully analyze the correspondence between this Lean 4 theorem and the mathematical problem.

**Point-by-point comparison analysis:**

## **Completely corresponding parts:**

1. **Problem type**:
    - Question: Determine all functions f : ℝ → ℝ such that...
    - Lean: `∀ f : ℝ → ℝ, f ∈ solution ↔ (...)` 
    - This is the standard formalization method for "determine all functions satisfying conditions"

2. **Function type**:
    - Question: f : ℝ → ℝ
    - Lean: `f : ℝ → ℝ` 

3. **Quantifier structure**:
    - Question: for all x,y ∈ ℝ
    - Lean: `∀ x y : ℝ` 

4. **Left side of functional equation**:
    - Question: f(x² + f(y))
    - Lean: `f (x^2 + f y)` 

5. **Right side of functional equation**:
    - Question: y + (f(x))²
    - Lean: `y + (f x)^2` 

## **Detailed verification:**

**Power operation representation**:
- Question: $x^2$, $(f(x))^2$
- Lean: `x^2`, `(f x)^2`
- Complete correspondence 

**Function composition representation**:
- Question: $f(x^2 + f(y))$
- Lean: `f (x^2 + f y)`
- In Lean, function application uses space, parentheses for grouping
- Semantics completely consistent 

**Addition operation**:
- Question: $x^2 + f(y)$ and $y + (f(x))^2$
- Lean: `x^2 + f y` and `y + (f x)^2`
- Operator precedence and associativity correct 

## **Type system check:**

**Real number type**:
- All variables and function values are in `ℝ`
- Addition, multiplication, power operations defined on real numbers
- Function composition type correct
- Types completely match 

## **Logical structure verification:**

**Equivalence relation**:

f ∈ solution ↔ (∀ x y : ℝ, f (x^2 + f y) = y + (f x)^2)

This correctly expresses:
f belongs to the solution set if and only if f satisfies the given functional equation. This is the standard formalization method for functional equation problems

Solution set definition:

def solution : Set (ℝ → ℝ) := sorry

1.Defines the solution set of functions (a set consisting of functions from ℝ to ℝ)
2.Uses sorry to indicate solution set content is pending
3.Characterizes properties of the solution set through the theorem

This is standard and correct practice

## Wrong Transalation:
Lean code:

import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

def solution : Set (ℝ → ℝ) := sorry

theorem theorem_question_37 (f : ℝ → ℝ) (x y : ℝ): 
    f ∈ solution ↔ (f (x^2 + f y) = y + (f x)^2) := by sorry

This type of translation is wrong, because the variable x and y are not quantified correctly. In the mathematical problem, we are asked to find "all functions" that satisfy the given functional equation "for all x,y ∈ ℝ". However, in the Lean code, the quantifiers are not correctly placed, and it actually means for some specific x and y.


Example 3:

Mathemnatical question:
Find all positive integers 0 < a, 0 < b  such that a+b divides ab - 1.

The correct lean code is:

import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

def solution : Set (ℕ × ℕ) := sorry

theorem  question119_1786_12567 (a b : ℕ):
    (a, b) ∈ solution ↔ (0 < a ∧ 0 < b ∧ (a + b) ∣ (a * b - 1)) := by sorry

## The wrong lean code is:
import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

def solution : Set (ℕ × ℕ) := sorry

theorem  question119_1786_12567 (a b : ℕ):
    (a, b) ∈ solution ↔ ((a + b) ∣ (a * b - 1)) := by sorry

## It forgets about the positive constraints on a and b, which is not acceptable.

## The wrong lean code is:

[import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

def solution : Set (ℕ × ℕ) := sorry

theorem  question119_1786_12567 (a b  : ℕ) (h : 0 < a ∧ 0 < b) :
    (a, b) ∈ solution ↔ (a + b) ∣ (a * b - 1) := by sorry]


-Be careful when seeing a "positive" or "negative" constraint on numbers, they correspond to different domains.
-Be very careful when you see an optimization problem. For problems involving **minimization** (keywords: "minimum", "minimize", "smallest", "least", "infimum") or **maximization** (keywords: "maximum", "maximize", "largest", "greatest"), Apply section 8 criterion check.
-Be very careful when seeing a "positive" or "negative" real number constraint, the type ℝ+ is defined as {x : ℝ // x > 0}
-ℕ strictly includes 0, ℕ+ strictly excludes 0
-Even is there is just a minor error, mark as not correspondent
-Focus on the position of the quantifiers, not the quantifiers themselves
-Do not use "sorry" to bypass any type checking, use the Lean 4 type system to verify the correctness of the code.

# Output

Return `YES` or `NO` indicating whether the question in natural language and the Lean statement have the same semantic meaning. Put the output in the `<correspondence>...</correspondence>` tag.
Then, return the reasonale for the judgement. Put the output in the `<reason> ... </reason>` tag.