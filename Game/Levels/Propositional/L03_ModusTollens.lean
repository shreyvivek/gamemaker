import GameServer.Commands

namespace Propositional

World "Propositional"
Level 3
Title "Modus Tollens"

Introduction "From P → Q and ¬Q, we can conclude ¬P. This is known as Modus Tollens."

/-- Modus Tollens: from P → Q and ¬Q, we can conclude ¬P. -/
TheoremDoc Propositional.modus_tollens_statement as "ModusTollens" in "Propositional"

Statement modus_tollens_statement (P Q : Prop) (h₁ : P → Q) (h₂ : ¬Q) : ¬P := by
  intro hP
  apply h₂
  exact h₁ hP

Conclusion "
You've proven Modus Tollens: from P → Q and ¬Q, you can conclude ¬P.
"

end Propositional
