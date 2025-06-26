import GameServer.Commands
import Game.Levels.Propositional.L07_OrElimination
namespace Propositional

World "Propositional"
Level 8
Title "Implication Chain"

Introduction "
Suppose you know two implications:

- If `P`, then `Q`. (i.e., `P → Q`)
- If `Q`, then `R`. (i.e., `Q → R`)

Then it logically follows that `P → R`.

Let’s practice chaining these implications directly.

**Note:** This level can be solved like the previous one, but it can also be done using a new tactic. Follow the hints accordingly.
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
The `intro` tactic assumes the premise of an implication.

Then you can either:
- Use `apply` with a function, or
- Call implication functions directly (e.g., `exact h₂ (h₁ hp)`).
-/
TacticDoc intro

/--
Solves the current goal by using a function or theorem.

If your goal is `Q` and you have `P → Q`, then `apply` turns the goal into proving `P`.
It's like saying: “To prove `Q`, it's enough to prove `P`.”
-/

TacticDoc apply

/-- From `P → Q` and `Q → R`, derive `P → R`. -/
TheoremDoc Propositional.implication_chain as "ImplicationChain" in "Propositional"

Statement implication_chain (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) : P → R := by
  Hint "Start with `intro` to assume that `P` is true."
  intro hp
  Hint "Now finish the level off using `{h₁}` and `{h₂}`. Make use of apply and exact."
  apply h₂
  apply h₁
  exact hp

NewTactic apply

NewTheorem Propositional.or_elim
Conclusion "
Perfect! You directly chained together `P → Q → R` into `P → R`.
"

end Propositional
