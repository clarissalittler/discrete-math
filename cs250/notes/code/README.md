# CS 250 — Companion code

Runnable Python companions to the CS 250 course notes. Every file in this
directory collects the Python snippets from one module (or intermezzo) of
the notes into a single self-contained script. Each script runs end to end
with no arguments and checks its own output via `assert` statements, so
you can verify the code works by running it:

```
python3 module01_sets.py
```

If all the assertions pass, the script prints `OK` at the end. If any
assertion fails, you get a traceback telling you exactly what went wrong.

## Inventory

| File                        | Module / intermezzo                            | Topics |
|-----------------------------|------------------------------------------------|--------|
| `module01_sets.py`          | Module 1 — Sets and Functions                  | Cartesian product, set operations |
| `module02_logic.py`         | Module 2 — Propositional Logic                 | Truth tables, tautology checker |
| `module03_proof_systems.py` | Module 3 — Proof Systems and Digital Logic     | DNF generator, NAND-only gates |
| `module04_quantifiers.py`   | Module 4 — Predicate Logic                     | Brute-force `∀∃` and `∃∀` checkers |
| `module05_groups.py`        | Module 5 — Direct Proof and Groups             | Group axiom checker |
| `module06_modular.py`       | Module 6 — Modular Arithmetic                  | Brute-force modular inverse, CRT |
| `module07_hoare.py`         | Module 7 — Indirect Proof and Hoare Logic      | Euclidean + extended Euclidean algorithm |
| `module08_sequences.py`     | Module 8 — Sequences and Induction             | Recursive sum-of-squares, Fibonacci variants |
| `module09_recurrences.py`   | Module 9 — Strong Induction and Recurrences    | Closed-form / iterative / matrix Fibonacci |
| `module10_structural.py`    | Module 10 — Structural Induction               | `List` and `BinTree` classes, property tests |
| `lambda_calculus.py`        | Intermezzo — The Lambda Calculus               | Church encodings of booleans and naturals |

## How to use this directory

The scripts are meant to be read alongside the notes, not instead of them.
When you're working through a module and want to see one of the snippets
actually execute, open the corresponding file here, run it, and poke at
the functions. The exercise solutions in the notes refer back to several
of these files by name, so you can also use them as reference
implementations when you're checking your own work.

Everything here requires only the Python 3 standard library (plus
`functools` and `itertools`, which are also in the stdlib). No pip install
needed. Tested on Python 3.11.
