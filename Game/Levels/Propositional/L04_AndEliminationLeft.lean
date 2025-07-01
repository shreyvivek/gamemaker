import GameServer.Commands
import Game.Levels.Propositional.L03_AndIntroduction
namespace Propositional

World "Propositional"
Level 4
Title "And Elimination (Left)"

Introduction "
If you know `P ∧ Q`, then you can extract `P` from it.

We’ll use the `exact` tactic, combined with `.left`, described further below.
"

Statement (P Q : Prop) (h : P ∧ Q) : P := by
  Hint "As you know, the `exact` tactic finishes the goal using a term that exactly matches the target.

  If you have `h : P ∧ Q`, then:
  - `h.left` gives you a term of type `P`
  - `h.right` gives you a term of type `Q`

  These are not tactics, but useful expressions to pass to `exact`.

  Now you know what to do to extract the left part `P` from `P ∧ Q` using `exact`."
  exact h.left


Conclusion "
Nicely done! You extracted the left side of a conjunction. A similar procedure can be followed to extract the right half of a conjunction.
"

end Propositional
