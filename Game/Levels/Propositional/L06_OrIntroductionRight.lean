import GameServer.Commands
import Game.Levels.Propositional.L05_OrIntroductionLeft
namespace Propositional

World "Propositional"
Level 6
Title "Or Introduction (Right)"

Introduction "
If `Q` is true, then `P ∨ Q` is also true — because *at least one* must hold.

Now let’s learn how to use the `right` tactic.
"

/--
---

Purpose: Use `right` when your goal is a disjunction (`P ∨ Q`) and you want to prove the **right** part.

If your goal is `P ∨ Q`, then `right` changes the goal to proving `Q`.

📌 Think of it as:

“I’ll prove the second part of the `or`, and that’s good enough.”

---

### In Propositional Logic:

Your goal : `P ∨ Q`

After `right`, your new goal is just `Q`.

---

### In Sets:

Your goal : `x ∈ A ∪ B`

After `right`, your new goal is just `x ∈ B`.

---

-/
TacticDoc right

Statement (P Q : Prop) (h : Q) : P ∨ Q := by
  Hint "Use the `right` tactic this time, to commit to proving `Q` instead of `P`."
  right
  Hint "Now you can finish the level yourself."
  exact h

NewTactic right

Conclusion "
Great! You've now mastered both `left` and `right` tactics, and how they can be useful in a disjunction.
"

end Propositional
