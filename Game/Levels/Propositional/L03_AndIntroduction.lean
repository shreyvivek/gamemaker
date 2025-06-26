import GameServer.Commands
import Game.Levels.Propositional.L02_IntroduceAssumption
namespace Propositional

World "Propositional"
Level 3
Title "And Introduction"

Introduction "
From `P` and `Q`, we can conclude `P ∧ Q`. That’s how conjunction works!

You’ll learn the `constructor` tactic in this level.
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
Used when the goal is a compound proposition like `P ∧ Q`.

It splits the goal into proving both components separately.

For example: `constructor` on `P ∧ Q` gives you two goals — one for `P` and one for `Q`.
-/
TacticDoc constructor

/-- From `P` and `Q`, derive `P ∧ Q`. -/
TheoremDoc Propositional.and_intro as "AndIntro" in "Propositional"

Statement and_intro (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  Hint "Use the `constructor` tactic to split the goal `P ∧ Q` into two parts."
  constructor
  Hint "Now prove `P` using `{hp}`."
  exact hp
  Hint "Now prove `Q` using `{hq}`."
  exact hq

NewTactic constructor
NewTheorem Propositional.intro_self


Conclusion "
Nice work! You combined two truths into one solid conjunction.
"

end Propositional
