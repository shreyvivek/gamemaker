import GameServer.Commands
import Game.Levels.Propositional.L03_AndIntroduction
namespace Propositional

World "Propositional"
Level 4
Title "And Elimination (Left)"

Introduction "
If you know `P ∧ Q`, then you can extract `P` from it.

Let’s see how to do that with `.left`.
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
If you have `h : P ∧ Q`, then:

- `h.left` gives you a proof of `P`.
- `h.right` gives you a proof of `Q`.

They’re used to “unpack” conjunctions.
-/
TacticDoc and.left

/-- From `P ∧ Q`, derive `P`. -/
TheoremDoc Propositional.and_elim_left as "AndElimLeft" in "Propositional"

Statement and_elim_left (P Q : Prop) (h : P ∧ Q) : P := by
  Hint "Use `h.left` to extract the left part `P` from `P ∧ Q`."
  exact h.left

NewTactic and.left

NewTheorem Propositional.and_intro

Conclusion "
Nicely done! You extracted the left side of a conjunction. A similar procedure can be followed to extract the right half of a conjunction.
"

end Propositional
