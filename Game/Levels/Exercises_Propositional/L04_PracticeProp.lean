import GameServer.Commands
import Game.Levels.Exercises_Propositional.L03_PracticeProp
import Game.Levels.Exercises_Propositional.ProofHelpers

namespace Exercises_Propositional

World "Exercises_Propositional"

Level 4
Title "Another Modus Chain"

Introduction "
Apply both **Modus Tollens** and **Modus Ponens** in a clean logical chain.

Hint: Make use of the `have` tactic wherever necessary, or a nested `exact` chain!
"

Statement (T U V W X : Prop)
  (h₁ : T ∧ U)
  (h₂ : U → ¬V ∧ W)
  (h₃ : X → V) : ¬X := by
  have hu : U := h₁.right
  have hnv_w : ¬V ∧ W := modus_ponens _ _ h₂ hu
  have hnv : ¬V := hnv_w.left
  have hnx : ¬X := modus_tollens _ _ h₃ hnv
  exact hnx

Conclusion "
Excellent. You combined two powerful rules — **Modus Tollens** and **Modus Ponens** — using structured steps.
"

end Exercises_Propositional
