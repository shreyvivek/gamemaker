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
