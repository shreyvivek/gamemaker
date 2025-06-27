import GameServer.Commands
import Game.Levels.Propositional.L04_AndEliminationLeft
namespace Propositional

World "Propositional"
Level 5
Title "Or Introduction (Left)"

Introduction "
Let’s now turn to disjunctions — statements involving the word 'or'.

In Lean, `P ∨ Q` means “either `P` is true, or `Q` is true (or both).”
To prove something like `P ∨ Q`, it’s enough to prove just one side — because *at least one must be true*.

In this level, you already have a proof of `P`, and your goal is `P ∨ Q`.
So all you have to do is tell Lean: “I want to prove the left side of the disjunction”, as you can finish it off with your existing proof.
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

/-- From `P`, derive `P ∨ Q`. -/
TheoremDoc Propositional.or_intro_left as "OrIntroLeft" in "Propositional"

Statement or_intro_left (P Q : Prop) (h : P) : P ∨ Q := by
  Hint "Use the `left` tactic to say `P ∨ Q` is true because `P` is true."
  left
  Hint "Now you can finish the level yourself."
  exact h

NewTactic left

NewTheorem Propositional.and_elim_left
Conclusion "
Great! You’ve learned how to state that “at least one is true.”
"

end Propositional
