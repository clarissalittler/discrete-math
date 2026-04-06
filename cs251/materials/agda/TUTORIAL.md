# Agda Developments Tutorial

This tutorial explains how the Agda materials in this repo fit together, how to
read them, and how to use them alongside the weekly course notes. It is written
for students and instructors who want more context than the quick-start guide in
README.md.

## Who this is for

- Students who want to see discrete math in a proof assistant.
- Instructors who want to demo formal proofs or assign optional Agda work.
- Anyone curious about how proofs become programs.

You do not need prior Agda experience. The files are self-contained and avoid
Agda's standard library to keep the focus on the mathematics.

## How to run and interact

Command line (from repo root):
- agda -i materials/agda materials/agda/Week01_SetTheory.agda
- agda -i materials/agda materials/agda/Week01_Lab.agda

Editor workflow:
- Emacs: open a file, run agda2-mode, then C-c C-l to load. Use C-c C-, to
  inspect a goal and C-c C-. to see the expected type.
- VS Code: install the Agda plugin and run the "Agda: Load" command.

Lab files use the option --allow-unsolved-metas so they load even with holes.
A hole looks like {!!}. Use holes to explore and fill in a proof step by step.

## How the codebase is structured

- Common.agda: a tiny "standard library" with Bool, Nat, List, equality, and
  proof utilities. Most files depend on this.
- Week01_SetTheory.agda through Week10_Efficiency.agda: complete developments
  aligned to each week of the course.
- Week01_Lab.agda through Week10_Lab.agda: short lab exercises with holes that
  line up with weekly topics.

The full developments are meant to be read and demonstrated; the lab files are
short practice sheets for students.

## Proofs are programs (a quick primer)

Agda treats propositions as types and proofs as values. You will see several
"logical" types in Common.agda:

- Unit is the type with one value: a proof of a trivial statement.
- Empty is the type with no values: a contradiction.
- Pair A B corresponds to "A and B".
- Sum A B corresponds to "A or B".
- Sigma A B corresponds to "there exists x : A such that B x".
- Not A is A -> Empty (proof of A leads to contradiction).
- Eq x y is propositional equality, with constructor refl.

A typical proof is just a function. For example, a proof that P implies Q is
literally a function from P to Q. Pattern matching on refl is the standard way
of using equalities.

## A guided tour by week

Each week below mirrors the course notes and includes a short note on how the
Agda file models the mathematics.

Week 1: Sets as predicates
- File: Week01_SetTheory.agda
- Sets are modeled as Pred A = A -> Set (membership is a predicate).
- Subset, union, and intersection are functions between predicates.
- Many classic set laws are proved directly by constructing functions.
- Look at subsetTrans, unionAssoc, and deMorganUnion as templates.

Week 2: Functions and inverses
- File: Week02_Functions.agda
- Injective and surjective are defined as types of proofs.
- LeftInverse and RightInverse capture the usual reasoning about bijections.
- Composition laws show the category structure of sets and functions.
- Look at leftInverseInjective and composeSurjective as proof patterns.

Week 3: Relations and modular arithmetic
- File: Week03_RelationsMod.agda
- Reflexive, symmetric, and transitive are predicates on relations.
- Closure operators are defined as new relations with the desired property.
- Congruence modulo n is modeled with a divisibility witness.
- Some number theory results are postulated (see Postulates section below).

Week 4: Counting and probability (part 1)
- File: Week04_CountingProb1.agda
- Counting rules are defined as functions on Nat.
- Events are predicates; complement and union are logical operations.
- Pigeonhole principle is postulated as an abstract theorem.

Week 5: Counting (part 2) and recurrences
- File: Week05_CountingProb2.agda
- Binomial coefficients are defined by recursion (Pascal's identity).
- Many standard identities are postulated or kept as exercises.
- Derangements and inclusion-exclusion appear as functions on Nat.

Week 6: Expectation and graph fundamentals
- File: Week06_ExpectationGraphs.agda
- Expected value is represented as a numerator/denominator pair.
- Graphs are modeled as records with vertex and edge types.
- The handshake theorem is postulated; it connects to the lecture proof.

Week 7: Graph theory details
- File: Week07_GraphTheoryI.agda
- Walks, paths, and trails are encoded as inductive proofs.
- Euler trails and circuits are stated as postulates.
- Adjacency matrices are a concrete representation for finite graphs.

Week 8: Trees and algorithms
- File: Week08_TreesAlgorithms.agda
- Tree sizes, heights, and traversals are defined by recursion.
- Classical tree facts (like edges = vertices - 1) are postulated.
- Algorithmic ideas (Dijkstra, MST) are included at the specification level.

Week 9: Regular languages and automata
- File: Week09_RegexAutomata.agda
- Regex are data types; matching is an inductive relation.
- DFA are records; run and accepts are defined by recursion.
- Closure results and pumping lemma are stated as postulates.

Week 10: Efficiency and asymptotics
- File: Week10_Efficiency.agda
- Big-O is defined as an existential bound for large enough n.
- Common complexity classes are modeled as Nat -> Nat functions.
- Most properties are postulated; use this as a formal vocabulary.

## Postulates: what they mean here

You will see lines like:

  postulate
    theoremName : ...

A postulate tells Agda to assume a statement without a proof. We do this when
proving it would take the course far beyond a short discrete math sequence, or
when the details are not the focus of the class. Postulates are useful for
stating the exact theorem, even if we do not fully formalize it.

## How the lab files fit in

The lab files are short worksheets. They import the full development and ask
for a handful of proofs with holes. They are designed to be doable in a lab
session and to reinforce the main mathematical ideas from the week.

Examples:
- Week01_Lab focuses on subset and union proofs.
- Week05_Lab focuses on Pascal's identity and small binomial computations.
- Week09_Lab focuses on nullable and run definitions for regex and DFA.

## How to extend or add exercises

If you want to add your own exercises:
1. Open the weekly file and locate a lemma that is already proven.
2. Copy its statement into a lab file and replace the proof with {!!}.
3. Reload Agda and fill the hole interactively.

You can also create a new lab file (WeekXX_Lab.agda) that imports Common and
that week's development.

## A note on foundations

These developments use the option --type-in-type, which allows Set to be a
member of itself. This simplifies the code and keeps it approachable, but it is
not logically sound for foundational work. For this course, it is acceptable as
an educational convenience. If you want a fully sound development, the files
can be refactored to use universe levels.

## Suggested ways to use this in the course

- Show 5-10 minutes of Agda in lecture to reinforce a proof idea.
- Offer weekly optional labs using the WeekXX_Lab.agda files.
- Let students who enjoy formalization choose an Agda track for a project.

If you want help tailoring this to your class, we can add a short "Agda day"
plan or create additional lab sets focused on specific proof techniques.
