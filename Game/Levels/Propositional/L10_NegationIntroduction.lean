import GameServer.Commands
import Game.Levels.Propositional.L09_ModusPonens
namespace Propositional

World "Propositional"
Level 10
Title "Negation Introduction"

Introduction "
To prove `¬P`, assume `P` and derive a contradiction.

This is called *proof by contradiction*.
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
To prove `¬P`, use `intro h` to assume `P`.

Then derive a contradiction (such as `False`), and use `exact` or `contradiction` to finish.
-/
TacticDoc contradiction

/-- If `P` leads to a contradiction, then `¬P`. -/
TheoremDoc Propositional.negation_intro as "NegationIntro" in "Propositional"

Statement negation_intro (P : Prop) (h : P → False) : ¬P := by
  Hint "To prove `¬P`, use `intro` to assume `P` is true."
  intro hp
  Hint "Now you have `{hp} : P`, and `{h} : P → False`. Apply `{h}` to get a contradiction."
  exact h hp

NewTactic contradiction

NewTheorem Propositional.modus_ponens_statement
Conclusion "
You’ve introduced negation: `¬P` is proven by making use of `P` itself. A bit absurd, but that's what make Math so special!
"

end Propositional
