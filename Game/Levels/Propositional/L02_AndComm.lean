import GameServer.Commands

namespace Propositional

World "Propositional"
Level 2
Title "And Commutativity"

Introduction "In this level, you will prove the commutativity of the logical operator AND"



/--
Rewrites a term in the goal or hypothesis.
If your goal is `P ∧ Q` and you have `h : P`, then `rw h` replaces `P` in the goal with `h`.
This is useful for simplifying or transforming expressions in your proof.
-/
TacticDoc rw

/--
To prove `P ∧ Q`, it suffices to prove bkl;kl;oth `P` and `Q` separately.

This constructor builds a conjunction from two proofs.
-/
TheoremDoc And.intro as "AndIntro" in "Propositional"

/-- And Commutativity: from P ∧ Q, we can conclude Q ∧ P. -/
TheoremDoc Propositional.and_comm_statement as "AndComm" in "Propositional"
Statement and_comm_statement (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  apply And.intro
  exact h.right
  exact h.left

NewTactic rw
NewTheorem And.intro Propositional.and_comm_statement
Conclusion "
Conjunction is commutative. You can always flip the two parts of a logical AND.
"
