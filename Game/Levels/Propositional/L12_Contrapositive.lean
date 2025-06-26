import GameServer.Commands
import Game.Levels.Propositional.L11_ModusTollens
namespace Propositional

World "Propositional"
Level 12
Title "Contrapositive"

Introduction "
The **contrapositive** of an implication `P → Q` is `¬Q → ¬P`.

In fact, both are logically equivalent!
"

/--
You’ll use `intro`, apply implications, and reason using negation and contradiction.
-/
TacticDoc intro

/-- From `P → Q`, derive `¬Q → ¬P`. -/
TheoremDoc Propositional.contrapositive_equiv as "Contrapositive" in "Propositional"

Statement contrapositive_equiv (P Q : Prop) (h : P → Q) : ¬Q → ¬P := by
  Hint "To prove `¬Q → ¬P`, use `intro` twice."
  intro hnq
  intro hp
  Hint "Use `{h}` to derive `Q` from `P`, then contradict `{hnq}`."
  exact hnq (h hp)


NewTheorem Propositional.modus_tollens
Conclusion "
You’ve shown that an implication and its contrapositive are logically equivalent!
"

end Propositional
