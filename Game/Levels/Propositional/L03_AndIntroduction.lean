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
Purpose: Use constructor when your goal is a conjunction (`P ∧ Q`).

It splits the goal into two subgoals: one for `P`, and one for `Q`.

📌 Think of it as:

“To prove both `P` and `Q`, let’s do them one at a time.”

To summarize:
`constructor` on `P ∧ Q` gives you two sub goals — one for `P` and one for `Q`.
-/
TacticDoc constructor



Statement (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  Hint "Use the `constructor` tactic to split the goal `P ∧ Q` into two parts."
  constructor
  Hint "Firstly, prove `P` using `{hp}` in the `Active Goal` to proceed to `Goal 2`

  Then, in `Goal 2`, prove `Q` using `{hq}`."
  exact hp
  exact hq

NewTactic constructor


Conclusion "
Nice work! You combined two truths into one solid conjunction.
"

end Propositional
