# Role Declaration

You are a mathematical expert.

# Task

The task is to the given math question as a math statement.

# Guidelines

- Rephrase the given math question to be a purely math statement where there is no keywords indictating it is a question.
- DO NOT skip any information from the original math question.

# Examples

**Example 1**

Question: 
Given $a \\equiv 1$ or $2 \\pmod 3$, prove that $a^2 \\equiv 1 \\pmod 3$.

Output:
If $a \\equiv 1$ or $2 \\pmod 3$, then $a^2 \\equiv 1 \\pmod 3$.

**Example 2**

Question:
Prove that for each positive integer n, there are pairwise relatively prime integers k₀,k₁,...,kₙ, all strictly greater than 1, such that k₀k₁...kₙ - 1 is a product of two consecutive integers.

Output:
For each positive integer n, there are pairwise relatively prime integers k₀,k₁,...,kₙ, all strictly greater than 1, such that k₀k₁...kₙ - 1 is a product of two consecutive integers.

**Example 3**

Question:
Prove that if n is a positive integer such that the equation\n\nx3 - 3xy^2 + y^3 = n has a solution in integers x, y, then it has at least three such solutions. Show that the equation has no solutions in integers for n = 2891.

Output:
If n is a positive integer such that the equation x3 - 3xy^2 + y^3 = n has a solution in integers x, y, then it has at least three such solutions.
The equation has no solutions in integers for n = 2891.

**Example 4**

Question:
Consider a collection $C$ of coins, where each coin has a value of $1/n$ for some positive integer $n$. A partition of $C$ into $N$ groups is called an *$N$-Cape Town* partition if the total value of coins in each group is at most $1$. Prove that if the total value of all coins in $C$ is at most $N + 1/2$, then $C$ has an $(N + 1)$-Cape Town partition.

Output:
Consider a collection $C$ of coins, where each coin has a value of $1/n$ for some positive integer $n$. A partition of $C$ into $N$ groups is called an *$N$-Cape Town* partition if the total value of coins in each group is at most $1$. If the total value of all coins in $C$ is at most $N + 1/2$, then $C$ has an $(N + 1)$-Cape Town partition.

# Output

Return the rephrased statements. Put the output in the `<statement>...</statement>` tag.