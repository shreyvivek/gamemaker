import GameServer.Commands

namespace Propositional

World "Propositional"
Level 13
Title "Disjunctive Syllogism"

Introduction "
From `P ∨ Q` and `¬P`, we can conclude `Q`.

This rule is known as **Disjunctive Syllogism**.
"

/--
Use the `cases` tactic to break down a disjunction into two branches.

Then handle contradiction in the `P` case and proceed with `Q` in the other.
-/
TacticDoc cases

/-- From `P ∨ Q` and `¬P`, conclude `Q`. -/
TheoremDoc Propositional.disjunctive_syllogism as "DisjunctiveSyllogism" in "Propositional"

Statement disjunctive_syllogism (P Q : Prop) (h : P ∨ Q) (hnp : ¬P) : Q := by
  Hint "Use `cases` to split `{h}` into two cases: `P` or `Q`."
  cases h with
  | inl hp =>
    Hint "`P` is true, but this contradicts `{hnp}`."
    exact False.elim (hnp hp)
  | inr hq =>
    Hint "`Q` is true here. Use `exact`."
    exact hq

NewTheorem Propositional.disjunctive_syllogism

Conclusion "
That’s **Disjunctive Syllogism**: if one side is false, the other must be true.
"

end Propositional
