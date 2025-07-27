import GameServer.Commands
import Game.Levels.Exercises_Propositional.L01_PracticeProp
import Game.Levels.Propositional.L07_ModusPonens
import Game.Levels.Propositional.L11_ModusTollens


namespace Exercises_Propositional

World "Exercises_Propositional"
Level 2
Title "Hands On"

Introduction "
You've learned some of the core tactics:
- `intro` to assume
- `apply` to break down implications
- `exact` to close goals

In this level, you’ll combine multiple implications to reach a goal.
All the theorems you’ve proved so far are available — so use them!

Try to:
- Think in chains
- Finish clearly

(Pun intended) _Lean_ on what you know. You’ve got this!
"
open Propositional
Statement (A B C D : Prop) (h₁ : A → B) (h₂ : B → C) (h₃ : C → D) : A → D := by
  Hint "First you need to assume `A`."
  intro a
  Hint "Now proceed using tactics you already know!"
  apply h₃
  apply h₂
  exact h₁ a

Conclusion "
You’ve just walked through a chain of reasoning — turning `A → B → C → D` into `A → D`.

This level shows how powerful basic implication chaining is — and how all the tactics you’ve learned work together.
"

end Exercises_Propositional
