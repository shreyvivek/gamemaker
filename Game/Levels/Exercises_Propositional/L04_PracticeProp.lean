import GameServer.Commands
import Game.Levels.Exercises_Propositional.L03_PracticeProp
import Game.Levels.Exercises_Propositional.ProofHelpers

namespace Exercises_Propositional

World "Exercises_Propositional"

Level 4
Title "Disjunctive Detour"

Introduction "
Time to bring in disjunctions (`P ∨ Q`)!

You’re given:

- `h₁ : P ∨ Q`
- `h₂ : Q → ¬R`
- `h₃ : ¬P`

Your goal is to prove `¬R`.

You’ll need to use:
- The `cases` tactic to split the disjunction
- `have` to name intermediate steps
- Possibly use contradiction to eliminate impossible paths

"

Statement (P Q R : Prop)
  (h₁ : P ∨ Q)
  (h₂ : Q → ¬R)
  (h₃ : ¬P) : ¬R := by
  intro hr
  cases h₁ with
  | inl hp =>
    have f : False := h₃ hp
    exact False.elim f
  | inr hq =>
    have hnr : ¬R := h₂ hq
    exact hnr hr

Conclusion "
Excellent! You split the disjunction and handled both cases carefully:
- The first led to contradiction with `¬P`
- The second allowed you to conclude `¬R`

This is classic **disjunction reasoning** paired with a chain of implications.
"

end Exercises_Propositional
