import GameServer.Commands

namespace Propositional

World "Propositional"
Level 1
Title "Modus Ponens"

Introduction "From P → Q and P, we can conclude Q. This is known as Modus Ponens."

/-- Modus Ponens: from P → Q and P, we can conclude Q. -/
TheoremDoc Propositional.modus_ponens_statement as "ModusPonens" in "Propositional"
Statement modus_ponens_statement (P Q : Prop) (h₁ : P → Q) (h₂ : P) : Q := by
  apply h₁
  exact h₂

Conclusion "
You've proven Modus Ponens: from P → Q and P, you can conclude Q.
"

end Propositional
