import GameServer.Commands
import Game.Levels.Propositional.L14_DoubleNegation
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
Purpose: Use exact when you already have a proof of exactly what the goal is asking for.

It closes the goal immediately if the term matches the goal’s type.

📌 Think of it as:

“Here's exactly what you're asking for — done!”

If your goal is `P` and you have a proof of `P` (say `h : P`), then `exact h` completes the proof.

To summarize:

You have : `h : P`
Your goal : `P`
`exact h` will complete the proof!
-/
TacticDoc exact


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

NewTheorem Propositional.dilemma Propositional.swap_implication
Conclusion "
Excellent! You've completed the Constructive Dilemma — a powerful inference rule using `∨`.
"

end Propositional
