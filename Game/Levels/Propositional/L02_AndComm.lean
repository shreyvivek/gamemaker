import GameServer.Commands
import Game.Levels.Propositional.L01_ModusPonens

namespace Propositional

World "Propositional"
Level 2
Title "And Commutativity"

Introduction "
In this level, you will prove the **commutativity** of the logical AND operator:
If you know `P ∧ Q`, then you can conclude `Q ∧ P`.
"

/--
To prove `P ∧ Q`, it suffices to prove both `P` and `Q` separately.

This constructor builds a conjunction from two proofs.
-/
TheoremDoc And.intro as "AndIntro" in "Propositional"

/-- And Commutativity: from `P ∧ Q`, we can conclude `Q ∧ P`. -/
TheoremDoc Propositional.and_comm_statement as "AndComm" in "Propositional"

Statement and_comm_statement (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  Hint "You want to prove a conjunction — use `apply And.intro`."
  apply And.intro
  Hint "Now prove the right side of the original conjunction, which is `Q`. Use `exact h.right`."
  exact h.right
  Hint "Now finish by proving `P` using `h.left`."
  exact h.left

NewTactic apply exact
NewTheorem And.intro Propositional.and_comm_statement

Conclusion "
You've proven that logical AND is **commutative** — from `P ∧ Q`, you can always derive `Q ∧ P`.
"

end Propositional
