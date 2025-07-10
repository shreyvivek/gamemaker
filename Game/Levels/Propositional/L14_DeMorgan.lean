import GameServer.Commands
import Game.Levels.Propositional.L13_DisjunctiveSyllogism

namespace Propositional

World "Propositional"
Level 14
Title "Negation of a Disjunction"

Introduction "
Let’s practice reasoning with **negated disjunctions**.

You're told that `¬(P ∨ Q)` is true. That means **neither `P` nor `Q` can be true**.

So your goal is to prove both `¬P` and `¬Q` — together, this becomes `¬P ∧ ¬Q`.

You’ll use:
- The `intro` tactic to assume one of the disjuncts
- The `apply` tactic to derive a contradiction using `¬(P ∨ Q)`
- The `constructor` tactic to prove a conjunction
"

Statement (P Q : Prop) (h : ¬(P ∨ Q)) : ¬P ∧ ¬Q := by
  Hint "Begin with `constructor`. Then you will separately prove `¬P` and `¬Q`."
  constructor

  -- Part 1: Prove ¬P
  Hint "Start with intro, then you can proceed by yourself."
  intro hp
  apply h
  left
  exact hp

  -- Part 2: Prove ¬Q
  intro hq
  apply h
  right
  exact hq

Conclusion "
Well done!

You proved that if `P ∨ Q` is false, then both `P` and `Q` must individually be false.

This is an application of **De Morgan’s Law** in reverse — and a great example of using elimination to handle disjunctions.
"

end Propositional
