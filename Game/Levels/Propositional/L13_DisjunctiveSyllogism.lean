import GameServer.Commands

namespace Propositional

World "Propositional"
Level 13
Title "Disjunctive Syllogism"

Introduction "
Suppose:

- `P ∨ Q` is true (at least one must hold), and
- `P` is false (i.e., `¬P` is true)

Then we can conclude that `Q` must be true.

This form of inference is called **Disjunctive Syllogism**.
"

/--
The `cases` tactic lets you do case analysis on a disjunction (`P ∨ Q`).

It splits the proof into two branches:
- one where `P` holds
- one where `Q` holds

If one branch leads to a contradiction, use `False.elim` to derive your goal.
-/
TacticDoc cases

/--
If you ever reach a contradiction (`False`), you can use the `False.elim` tactic to prove **any** goal.

This is based on the logical principle that "from falsehood, anything follows" (ex falso quodlibet).
-/
TacticDoc False.elim

/-- From `P ∨ Q` and `¬P`, conclude `Q`. -/
TheoremDoc Propositional.disjunctive_syllogism as "DisjunctiveSyllogism" in "Propositional"

Statement disjunctive_syllogism (P Q : Prop) (h : P ∨ Q) (hnp : ¬P) : Q := by
  Hint "Use `cases` to split `{h}` into two cases: either `P` holds, or `Q` does."
  cases h with
  | inl hp =>
    Hint "`P` leads to a contradiction with `{hnp}` — use `False.elim` to conclude."
    exact False.elim (hnp hp)
  | inr hq =>
    Hint "`Q` is true here. Use `exact`."
    exact hq

NewTactic False.elim
NewTheorem Propositional.disjunctive_syllogism

Conclusion "
Nicely done! You've applied **Disjunctive Syllogism** — eliminating one side of a disjunction using negation.
"

end Propositional
