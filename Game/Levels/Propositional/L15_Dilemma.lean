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
Purpose: Use intro to assume something — usually when proving an implication.

If your goal is `P → Q`, `intro h` changes the goal to `Q` and gives you `h : P` as a local assumption.

📌 Think of it as:

“Let me assume `P` is true for now, and see if I can prove `Q`.”
Opens up an implication goal by introducing its assumption.

To summarize:

Your goal : `h : P → P`
After `intro h`,
you get an assumption `h : P` and your goal will just be `P`.
-/
TacticDoc intro


/--
Purpose: Use constructor when your goal is a conjunction (`P ∧ Q`).

It splits the goal into two subgoals: one for `P`, and one for `Q`.

📌 Think of it as:

“To prove both `P` and `Q`, let’s do them one at a time.”

To summarize:
`constructor` on `P ∧ Q` gives you two sub goals — one for `P` and one for `Q`.
-/
TacticDoc constructor


/--
Purpose: Use `left` when your goal is a disjunction (`P ∨ Q`) and you want to prove the **left** part.

If your goal is `P ∨ Q`, then `left` changes the goal to proving `P`.

📌 Think of it as:

“I’ll prove the first part of the `or`, and that’s good enough.”

To summarize:

Your goal : `P ∨ Q`
After `left`, your new goal is just `P`
-/
TacticDoc left




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
