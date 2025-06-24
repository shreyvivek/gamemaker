import GameServer.Commands

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
"

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
NewTheorem Propositional.implication_chain

Conclusion "
Perfect! You directly chained together `P → Q → R` into `P → R`.
"

end Propositional
