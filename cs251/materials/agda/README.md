# Agda Labs (Optional)

This folder contains two kinds of files:
- WeekXX_*.agda: completed developments aligned with weekly notes.
- WeekXX_Lab.agda: optional lab sheets with holes.
- TUTORIAL.md: longer-form guide to the Agda materials.

Quick start (CLI)
- agda -i materials/agda materials/agda/Week01_Lab.agda
- agda -i materials/agda materials/agda/Week01_SetTheory.agda

Editor workflow
- Emacs: open a file, M-x agda2-mode, C-c C-l to load, C-c C-, to inspect a goal.
- VS Code: install the Agda plugin, run the "Agda: Load" command.

Week-by-week lab map
- Week 1: sets as predicates, subset reasoning, union/intersection.
- Week 2: functions, composition, inverses, preimage.
- Week 3: relations, closures, modular arithmetic.
- Week 4: counting rules, complements, small computations.
- Week 5: binomial coefficients and Pascal identity.
- Week 6: expectation basics and simple list computations.
- Week 7: walks and basic graph properties.
- Week 8: tree sizes, traversals, and recursion.
- Week 9: regex and DFA basics, nullable, run.
- Week 10: asymptotic notation and simple Big-O proofs.

Notes
- Lab files use --allow-unsolved-metas so they load with holes.
- Fill holes marked {!!}.
- The developments are self-contained; no standard library required.
