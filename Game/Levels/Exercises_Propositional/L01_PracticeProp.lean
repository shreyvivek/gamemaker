import GameServer.Commands
import Game.Levels.Propositional.L07_ModusPonens
import Game.Levels.Propositional.L11_ModusTollens
namespace Exercises_Propositional

World "Exercises_Propositional"

Level 1
Title "From And to Implication"

Introduction "
You’re given a conjunction and an implication.

Your task: extract the right part and trigger the implication.
"


Statement (P Q R : Prop)
  (h₁ : P ∧ Q)
  (h₂ : P → R) : R := by
  apply h₂
  exact h₁.left


Conclusion "
You extracted `P` from the conjunction and applied the implication to reach `R`. Nicely done!
"

end Exercises_Propositional
