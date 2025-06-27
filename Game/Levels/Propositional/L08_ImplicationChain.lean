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
