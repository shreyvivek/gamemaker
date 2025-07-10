import GameServer.Commands
import Game.Levels.Exercises_Propositional.L02_PracticeProp
import Game.Levels.Exercises_Propositional.ProofHelpers

namespace Exercises_Propositional

World "Exercises_Propositional"

Level 3
Title "Modus Chain Attack"

Introduction "
Apply both **Modus Tollens** and **Modus Ponens** in a clean logical chain.

Hint: Make use of the `have` tactic wherever necessary, or a nested `exact` chain!
"

Statement (P Q R S T : Prop)
  (h₁ : ¬P ∧ Q)
  (h₂ : R → P)
  (h₃ : ¬R → S)
  (h₄ : S → T) : T := by
  have hnp : ¬P := h₁.left
  have hnr : ¬R := modus_tollens h₂ hnp
  have hs : S := modus_ponens h₃ hnr
  exact modus_ponens h₄ hs

Conclusion "
Excellent. You combined two powerful rules — **Modus Tollens** and **Modus Ponens** — using structured steps.
"

end Exercises_Propositional
