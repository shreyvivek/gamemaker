import GameServer.Commands

namespace Propositional

World "Propositional"
Level 15
Title "Dilemma"

Introduction "
This is the **Constructive Dilemma**:

From `P ∨ Q`, `P → R`, and `Q → R`, you can conclude `R`.

It's case-based reasoning again.
"

/--
Use `cases` on the disjunction `P ∨ Q`, then use `apply` or `exact` in each branch with the given implications.
-/
TacticDoc apply

/-- From `P ∨ Q`, `P → R`, and `Q → R`, derive `R`. -/
TheoremDoc Propositional.dilemma as "Dilemma" in "Propositional"

Statement dilemma (P Q R : Prop) (hpq : P ∨ Q) (hpr : P → R) (hqr : Q → R) : R := by
  Hint "Use `cases` on `{hpq}` to consider each possibility."
  cases hpq with
  | inl hp =>
    Hint "`P` holds. Use `{hpr}` to conclude `R`."
    exact hpr hp
  | inr hq =>
    Hint "`Q` holds. Use `{hqr}` to conclude `R`."
    exact hqr hq

NewTheorem Propositional.dilemma

Conclusion "
Excellent! You've completed the Constructive Dilemma — a powerful inference rule using `∨`.
"

end Propositional
