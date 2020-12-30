---
title: "Solving Regular Expression Constraints in Z3"
speaker: "Caleb Stanford"
semester: "FA20"
---
Abstract:
The manipulation of raw string data is ubiquitous in security-critical software, and prone to serious errors. While verification of such software typically reduces to solving string and regular expression constraints, the common case of Boolean combinations of regular expression constraints is not handled well by existing SMT string solvers. We present a new regular expression solver, called dZ3, which solves the problem by naturally supporting "extended" regular expression constraints (Boolean combinations) over an arbitrary character theory. At a technical level, the solver is based on "symbolic derivatives", a way of manipulating regular expressions algebraically. At a practical level, it is driven by applications in automated cloud security configuration.

dZ3 matches the state of the art on standard benchmarks, while outperforming the best solvers (CVC4, Z3, Z3str3, Z3trau, and Ostrich) on Boolean combinations of constraints. It is now the default solver shipped with Z3.

Homework:
Your homework is to play with Z3 and write a program which generates a valid password string -- a string which should contain at least one number and at least one letter. Here are some steps to guide you through:

1. Go to
https://rise4fun.com/z3
and try pasting in the following:
(declare-const x String)
(assert (str.in.re x (re.++ (str.to.re "hello") re.all (str.to.re "world"))))
(check-sat)
(get-model)
Here's an explanation of the syntax:
- "declare-const" means we declare a new string value.
- "(assert (str.in.re x R))" means we assert that that string value x matches the regular expression R.
- "(re.++ R1 R2 ...)" is regular expression concatenation of R1, R2, ...
- "(str.to.re s)" makes a regular expression from a string literal s.
- "re.all" is the regular expression which matches every string.

Click the big "run" button and take a look at the model. You should get a string starting with "hello" and ending with "world" (and possibly some weird characters in between).

2. Try modifying the program to have a second constraint which makes it unsatisfiable, using only the operations above.
(assert (str.in.re x <add your own regular expression here>))

Click run and see that Z3 gives "unsat".

3. Now try to modify the program so that it states that x has at least one letter (upper or lower case) and at least one number. The following may come in handy:
- (re.range "a" "z") is a regular expression matching a character with ascii code between "a" and "z".

Click run and see if you get a valid password string.

4. (OPTIONAL) Make it so that your password is also alphanumeric (all characters are either letters or numbers). Some additional syntax you can use:
- (re.union R1 R2 ...) is the union of regular expressions R1, R2, ...
- (re.* R1) is the Kleene star of regular expression R1.
