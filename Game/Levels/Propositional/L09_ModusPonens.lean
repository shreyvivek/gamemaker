import GameServer.Commands
import Game.Levels.Propositional.L08_ImplicationChain
namespace Propositional

World "Propositional"
Level 9
Title "Modus Ponens"

Introduction "
From `P → Q` and `P`, we can conclude `Q`.

This rule of inference is known as **Modus Ponens**. Let’s practice using `apply`.

After completing Level 7 and 8, this should be cake walk!
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
Solves the current goal by using a function or implication.

If your goal is `Q` and you have `h : P → Q`, then `apply h` turns the goal into proving `P`.

It’s like saying: “To prove `Q`, it’s enough to prove `P`.”
-/
TacticDoc apply

/-- Modus Ponens: from `P → Q` and `P`, conclude `Q`. -/
TheoremDoc Propositional.modus_ponens_statement as "ModusPonens" in "Propositional"

Statement modus_ponens_statement (P Q : Prop) (h₁ : P → Q) (h₂ : P) : Q := by
  Hint "Use the `apply` tactic with the implication `{h₁}` to reduce the goal `Q` to `P`."
  apply h₁
  Hint "Now you have a new goal `P`, and `{h₂} : P` is already available."
  exact h₂


NewTheorem Propositional.implication_chain
Conclusion "
Classic and powerful — you’ve just used **Modus Ponens** correctly.
"

end Propositional
