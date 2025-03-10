# Formalizing Verification in Lean – FU Berlin Block Course April 2025

## Announcements

* The course will take place in _room 1.3.48 of the physics building_ (Arnimallee 14) on **Friday the 14th of April**.
* The afternoon session will start half an hour later than usual at 14:30 on **Thursday the 13th of April**.
* Due to a planned power outage at ZIB, the course will take place in _room 1.3.48 of the physics building_ (Arnimallee 14) on **Tuesday the 10th of April**. If the power is back for the afternoon, we will move back to the ZIB for the second part that day.

## General notes

* This is the first time this course is being held. The structure is tentative and subject to change. Constructive feedback is welcomed throughout the course and afterwards.
* The course is split into two sessions (9:30 to 12:30 and 14:00 to 17:00) per day and takes place from Monday the 10th of April to Friday the 21st of April. The usual venue will be either the big lecture hall or small seminar room at the ZIB.
* The course is open to everyone, including guest auditors (Gasthörer), not just those who need it for their ABV modules. However, priority will be given to FU students who need the course as part of their degree program.
* Participants need to bring a laptop to do the exercises and follow along during the course and work on exercises and project work.
* Completion of Analysis I and Linear Algebra I should provide a sufficient mathematical background, but participants should have a strong understanding of these subjects, as formal proof verification is very "unforgiving". No prior programming experience is required, but a certain "technical affinity and interest" is needed.
* The course will be conducted in English, but students may express themselves in German if they prefer.

## Technical difficulties

### Wrangling `lean` and `lake`

* `lake init ProjectName math` sets up a project with mathlib as a dependency in the current folder.
* `lake build` builds the project.
* `pkill -f lean` kills the running Lean server.
* `lake exe cache get` pulls the pre-compiled mathlib binaries.
* In the worst casem deleting the `.lake` folder and running `lake clean` can fix many issues.

### Versioning with `git`

*To be added.*

## Resources

### Documentation and search
* The [mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/index.html) is the official documentation of the [mathlib library](https://github.com/leanprover-community/mathlib4)
* [LeanSearch](https://leansearch.net) is a helpful resource for finding results in mathlib

### Text books
* [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/) by Jeremy Avigad, Leonardo de Moura, Soonho Kong, Sebastian Ullrich
* [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) by Jeremy Avigad and Patrick Massot
* [The Hitchhiker’s Guide to Logical Verification](https://cs.brown.edu/courses/cs1951x/static_files/main.pdf) by Anne Baanen, Alexander Bentkamp, Jasmin Blanchette, Johannes Hölzl, Jannis Limperg
* [The Mechanics of Proof](https://hrmacbeth.github.io/math2001/) by Heather Macbeth
* [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/) by David Thrane Christiansen

### Talks

* Kevin Buzzard's talk on [The rise of formalism in mathematics](https://www.youtube.com/watch?v=SEID4XYFN7o) at ICM22

### A more playful approach
* The [Lean Game Server](https://adam.math.hhu.de) inspired many of the smaller exercises
 

## Course Outline

*To be added.*
