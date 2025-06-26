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
