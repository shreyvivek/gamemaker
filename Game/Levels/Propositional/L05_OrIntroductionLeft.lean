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
  Hint "Use the `left` tactic to say `P ∨ Q` is true because `P` is true.

  **Note:** Here you are directly operating on the goal itself. So you just need to type `left` and Lean will understand."
  left
  Hint "Now you can finish the level yourself."
  exact h

NewTactic left

Conclusion "
Great! You’ve learned how to state that “at least one is true.”
"

end Propositional
