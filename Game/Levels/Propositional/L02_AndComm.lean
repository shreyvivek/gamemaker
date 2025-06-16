import GameServer.Commands

namespace Propositional

World "Propositional"
Level 2
Title "And Commutativity"

Introduction "In this level, you will prove the commutativity of the logical operator AND"


/--
Solves the current goal by using a function or theorem.

If your goal is `Q` and you have `P → Q`, then `apply` turns the goal into proving `P`.
It's like saying: “To prove `Q`, it's enough to prove `P`.”
-/
TacticDoc apply

/--
Closes the goal by providing a term that exactly matches the goal.

If your goal is `P` and you already have `h : P`, then `exact h` finishes the proof.
-/
TacticDoc exact

/--
<<<<<<< HEAD
Rewrites a term in the goal or hypothesis.
If your goal is `P ∧ Q` and you have `h : P`, then `rw h` replaces `P` in the goal with `h`.
This is useful for simplifying or transforming expressions in your proof.
=======
Closes the goal by providing a term that exactly matches the goal.
>>>>>>> 3a1f40e351a90b8c52318979222766ad45941d2e
-/
TacticDoc rw

/--
To prove `P ∧ Q`, it suffices to prove both `P` and `Q` separately.

This constructor builds a conjunction from two proofs.
-/
TheoremDoc And.intro as "AndIntro" in "Propositional"

/-- And Commutativity: from P ∧ Q, we can conclude Q ∧ P. -/
TheoremDoc Propositional.and_comm_statement as "AndComm" in "Propositional"
Statement and_comm_statement (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  apply And.intro
  exact h.right
  exact h.left

NewTactic apply exact rw
<<<<<<< HEAD
NewTheorem And.intro
=======
NewTheorem And.intro Propositional.and_comm_statement
>>>>>>> 3a1f40e351a90b8c52318979222766ad45941d2e
Conclusion "
Conjunction is commutative. You can always flip the two parts of a logical AND.
"
