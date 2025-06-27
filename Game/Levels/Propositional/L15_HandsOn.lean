import GameServer.Commands
import Game.Levels.Propositional.L14_Dilemma
namespace Propositional

World "Propositional"
Level 15
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


/-- From a chain of implications, conclude the final result. -/
TheoremDoc Propositional.implication_maze as "ImplicationMaze" in "Propositional"
Statement implication_maze (A B C D : Prop) (h₁ : A → B) (h₂ : B → C) (h₃ : C → D) : A → D := by
  Hint "First you need to assume `A`."
  intro a
  Hint "Your goal is now `D`. Reduce it to `C`."
  apply h₃
  Hint "Now your goal is `C`. Reduce it to `B`."
  apply h₂
  Hint "Finish the level now!."
  exact h₁ a

NewTheorem Propositional.implication_maze

Conclusion "
You’ve just walked through a chain of reasoning — turning `A → B → C → D` into `A → D`.

This level shows how powerful basic implication chaining is — and how all the tactics you’ve learned work together.

With that, we have come to the end of this World. Click on the Home button at the top to explore other worlds.
"

end Propositional
