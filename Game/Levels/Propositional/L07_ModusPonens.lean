import GameServer.Commands
import Game.Levels.Propositional.L06_OrIntroductionRight
namespace Propositional

World "Propositional"
Level 7
Title "Modus Ponens"

Introduction "
Time to visit one of the most fundamental rules of inference: **Modus Ponens**.

It says:
> If `P → Q` and `P` are both true, then `Q` must also be true.

In Lean, this means:
- If you have `implication : P → Q`, and
- `fact : P`,

then you can apply the implication to the fact to get `Q`.

This is what we’ll do in this level:
You’re given `P → Q` and `P`, and your goal is to prove `Q`.

You're going to make use of `apply` tactic.
Let’s break it down step by step.
"

/--

---

Purpose: Use `apply` to reduce your current goal to an earlier implication.

If your goal is `Q`, and you have `implication : P → Q`,
then `apply implication` changes the goal to `P`.

📌 Think of it as:

“To prove `Q`, it’s enough to prove `P` — because I already have `P → Q`.”

---

-/
TacticDoc apply


/-- Modus Ponens: from `P → Q` and `P`, conclude `Q`. -/
TheoremDoc Propositional.modus_ponens as "modus_ponens" in "Propositional"

Statement modus_ponens {P Q : Prop} (h₁ : P → Q) (h₂ : P) : Q := by
  Hint "Your goal is `Q`, and you have an implication `h₁ : P → Q`.

  By writing `apply h₁`, you are telling Lean:
  “To prove `Q`, it suffices to prove `P`.”

  That’s because `P → Q` works like a function:
  If you give it `P`, it will return `Q`.

  So `apply h₁` transforms your goal from `Q` to `P`,
  and Lean now expects you to prove `P`.

  Now go ahead — apply the implication!

  _for writing subscript 1, type `h`, enter a backslash and then enter `1`._"
  apply h₁
  Hint "Now the goal has changed to `P`. You're being asked to prove the condition of the implication.

  Luckily, you already have `h₂ : P`. Use `exact` to finish!"
  exact h₂

NewTactic apply
Conclusion "
Nicely done! You’ve applied **Modus Ponens** by thinking backwards from your goal.

You told Lean: “To prove `Q`, I’ll use `P → Q`, so just give me `P`.”

That’s the core idea behind the `apply` tactic — a major tool in your proof toolkit.
"

end Propositional
