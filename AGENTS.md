# Overview

A design is at [DESIGN.md](docs/DESIGN.md)

# Building
- build: `lake build`
- run: `lake exe <target-name>`
- clean: `lake clean`

# Coding style
- Prefer dot-abbreviated names to fully qualified names.
- Prefer piping operations using `|>.` or `|>` to nesting parentheses.
- If using a chain of `|>.`s, try to make them all `|>.`s instead of a mix of `|>.`s and nested `.`s.
- If a piping chain is long, align the steps on multiple lines.
- Annotations should be on their own separate line before a definition, except for one-line definitions of non-theorems.

# Testing
- Prefer `#guard`/`#guard_expr` commands or `example` with proofs instead of run-time code.
- Simple tests serving as machine-checked examples should be right below definition(s) they refer to.
- Write plenty of examples on edge cases and common cases.
- Tests at each level of abstraction should not be specifying implementation details. For example, when testing maps and sets, focus on how operations should interact coherently (e.g. `∅ |>.insert 42 |>.size = 1`, `∅ |>.insert 42 |>.insert 42 = ∅ |>.insert 42`, `∅ |>.insert 42 |>.insert 34 |>.toList = [34, 42]`, etc.), instead of asserting representation details (e.g. we don't care about the shape or height of a set's internal tree).
- Internal data structures and utilities should also have their own tests, of course.
- Prefer "symbolic tests" using (implicitly quantified) variables to needlessly specific values (e.g. `example : ¬ x ∈ ∅ := by simp` instead of `example : ¬ 42 ∈ ∅ := by simp` if it works).

# Theorems and proving
- For general properties to be stated and proven as theorems, make sure some example tests pass first before bothering to prove them.
- Theorems of the form `lhs = rhs` should aim for `rhs` being simpler than `lhs` and be marked as `@[simp]` and `@[grind =]`.
- If using `grind`, always use `grind?`, then see precisely what are needed and revise with `grind only`.
- The newly stable tactics `cbv` and `decide_cbv` might be useful at places.
- Try to make proofs human readable: the strategy/structure should be apparent, with tedious details taken care of by tactics/helpers. This is analogous to how one would handwave proofs in a paper due to space constraint, deferring details to the appendix.
- Helper lemmas that are only used locally should be marked `private`, just like helper functions.
