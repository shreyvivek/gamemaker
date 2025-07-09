import GameServer.Commands
import Game.Levels.Propositional.L01_AssumeAndFinish
namespace Propositional

World "Propositional"
Level 2
Title "Introduce Assumption"

Introduction "
Let’s prove an implication: `P → P`. That is, if `P` holds, then `P` holds (trivially).

This level introduces the `intro` tactic.
"

/--
---

Purpose: Use intro to assume something — usually when proving an implication.

If your goal is `P → Q`, `intro h` changes the goal to `Q` and gives you `h : P` as a local assumption.

📌 Think of it as:

“Let me assume `P` is true for now, and see if I can prove `Q`.”
Opens up an implication goal by introducing its assumption.

---

### In Propositional Logic:

Your goal : `h : P → P`
After `intro h`,
you get an assumption `h : P` and your goal will just be `P`.

---

### In Sets:

You’re given:
- A set `A : Set ℕ`

To prove `A ⊆ A`, you must show: `∀ x, x ∈ A → x ∈ A`

Strategy:
1. Use `intro x` to assume an arbitrary element.
2. Use `intro h` to assume `x ∈ A`.
3. Use `exact h` to conclude `x ∈ A`.

This pattern is the **structure of proving subset relations**.

---

-/
TacticDoc intro

Statement (P : Prop) : P → P := by
  Hint "Use the `intro` tactic to assume `P` is true. Try `intro h`."
  intro h
  Hint "Now you have `{h} : P`, and your goal is `P`. Use `exact` to finish."
  exact h

NewTactic intro


Conclusion "
That was a basic implication! The `intro` tactic is your go-to tool for these.
"

end Propositional
