import GameServer.Commands
import Game.Levels.Propositional.L13_DisjunctiveSyllogism
namespace Propositional

World "Propositional"
Level 14
Title "Dilemma"

Introduction "
This is the **Constructive Dilemma**:

From `P ∨ Q`, `P → R`, and `Q → R`, you can conclude `R`.

It's case-based reasoning again.
"

/-- From `P ∨ Q`, `P → R`, and `Q → R`, derive `R`. -/
TheoremDoc Propositional.dilemma as "Dilemma" in "Propositional"

Statement dilemma (P Q R : Prop) (hpq : P ∨ Q) (hpr : P → R) (hqr : Q → R) : R := by
  Hint "Use `cases` on `{hpq}` to consider each possibility."
  cases hpq with
  | inl hp =>
    Hint "Now, `P` holds. Use `{hpr}` to conclude `R`."
    Hint "After that, `Goal 2` contains the scenario where `Q` holds. Use `{hqr}` to conclude `R`."
    Hint "Also, Lean is really smart. The `exact` tactic is so versatile that both `exact modus_ponens a b` and `exact a b` mean the same."
    exact hpr hp
  | inr hq =>
    exact hqr hq

Conclusion "
Excellent! You've completed the Constructive Dilemma — a powerful inference rule using `∨`.
"

end Propositional
