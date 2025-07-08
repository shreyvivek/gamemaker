import GameServer.Commands

namespace Exercises_Propositional

/-- Modus Tollens: from `Q → P` and `¬P`, conclude `¬Q`. -/
TheoremDoc Exercises_Propositional.modus_tollens as "modus_tollens" in "Exercises_Propositional"
theorem modus_tollens {P Q : Prop} (h₁ : Q → P) (h₂ : ¬P) : ¬Q := by
  intro hq
  apply h₂
  exact h₁ hq

/-- Modus Ponens: from `P → Q` and `P`, conclude `Q`. -/
TheoremDoc Exercises_Propositional.modus_ponens as "modus_ponens" in "Exercises_Propositional"
theorem modus_ponens {P Q : Prop} (h₁ : P → Q) (h₂ : P) : Q := by
  apply h₁
  exact h₂

end Exercises_Propositional
