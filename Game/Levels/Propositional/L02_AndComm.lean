import GameServer.Commands
import Game.Levels.Propositional.L01_ModusPonens
namespace Propositional

World "Propositional"
Level 2
Title "And Commutativity"

Introduction "In this level, you will prove the commutativity of the logical operator AND"

/--
jffdsj
-/
TacticDoc cases
/--
jffdsj
-/
TacticDoc split

/--
To prove `P ∧ Q`, it suffices to prove `P` and `Q` separately.

This constructor builds a conjunction from two proofs.
-/
TheoremDoc And.intro as "AndIntro" in "Propositional"

/-- And Commutativity: from P ∧ Q, we can conclude Q ∧ P. -/
TheoremDoc Propositional.and_comm_statement as "AndComm" in "Propositional"
Statement and_comm_statement (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  apply And.intro
  exact h.right
  exact h.left

NewTactic split cases
NewTheorem And.intro Propositional.modus_ponens_statement
Conclusion "
Conjunction is commutative. You can always flip the two parts of a logical AND.
"
end Propositional
