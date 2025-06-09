import GameServer.Commands

namespace Propositional

World "Propositional"
Level 2
Title "And Commutativity"

/-- And Commutativity: from P ∧ Q, we can conclude Q ∧ P. -/
TheoremDoc Propositional.and_comm_statement as "AndComm" in "Propositional"
Statement and_comm_statement (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  apply And.intro
  exact h.right
  exact h.left

Conclusion "
Conjunction is commutative. You can always flip the two parts of a logical AND.
"
