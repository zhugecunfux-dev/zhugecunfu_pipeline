# Role Declaration

You are a mathematical expert.

# Task

The task is to extract the necessary concepts in the question

# Guidelines

- If the concept is defined in the question, extract the concept out of the question and make it self-contained.
- If the concept is not defined in the question, extract the concept and make it self-contained by rephrasing it based on your understanding.
- Write the concept as a function by generalizing the input.
- Coin a name for each extracted concept.
- In the description of the concept, if it depends on other concepts use the name of the concepts in the description.


# Examples

**Example 1**

Question: 
Given $a \\equiv 1$ or $2 \\pmod 3$, prove that $a^2 \\equiv 1 \\pmod 3$.

Output: 
[
    {
        "name": `cong_one_or_two_mod_three`,
        "input": `a`,
        "description": "$a \\equiv 1$ or $2 \\pmod 3$",
        "dependencies": []
    },
    {
        "name": `sq_cong_one_mod_three`,
        "input": `a`,
        "description": "$a^2 \\equiv 1 \\pmod 3$.",
        "dependencies": []
    },
    {
        "name": `cong_one_or_two_implies_sq_cong_one`,
        "input": `a`,
        "description": "if `cong_one_or_two_mod_three a`, then `sq_cong_one_mod_three a`",
        "dependencies": [`cong_one_or_two_mod_three`, `cong_one_or_two_implies_sq_cong_one`]
    }
]

**Example 2**

Question:
Let n be a positive integer. A _Japanese triangle_ is defined as
a set of 1 + 2 + ... + n dots arranged as an equilateral
triangle. Each dot is colored white or red, such that each row
has exactly one red dot.

A _ninja path_ is a sequence of n dots obtained by starting in the
top row (which has length 1), and then at each step going to one of
the dot immediately below the current dot, until the bottom
row is reached.

In terms of n, determine the greatest k such that in each Japanese triangle
there is a ninja path containing at least k red dots.

Output:
[
    {
        "name": `pos_int`,
        "input": `n`,
        "description": "n > 0.",
        "dependencies": []
    },
    {
        "name": `japanese_triangle`,
        "input": `n`,
        "description": "a set of 1 + 2 + ... + n dots arranged as an equilateral triangle.",
        "dependencies": []
    },
    {
        "name": `valid_coloring`,
        "input": 
    }
]

**Example 3**

Question:
In the board, $N = 6$ stacks of coins are given, with each stack initially containing one coin.
At any time, one of the following operations can be performed:
* Type 1: Remove one coin from a non-empty stack $k+1$ and add two coins to stack $k$ (for $k < 5$).
* Type 2: Remove one coin from a non-empty stack $k+2$ and swap the contents of stacks $k$ and $k+1$ (for $k < 4$).

Is it possible that, after some operations, we are left with stack 0
  containing $A = 2010^{2010^{2010}}$ coins and all other stacks empty?

Output:
[
    {
        "name": 
    }
]


# Output

Return the structured statements. Put the output in the `<concept>...</concept>` tag.