import GameServer.Commands
import Game.Levels.Propositional.L10_NegationIntroduction
namespace Propositional

World "Propositional"
Level 11
Title "Modus Tollens"

Introduction "
This level introduces another classic rule of inference: **Modus Tollens**.

You may recall from Level 7 (**Modus Ponens**) that:
> If `P → Q` and `P` are true, then `Q` is true.
Now imagine the opposite:
> If `P → Q` and `Q` is **false**, then `P` must also be false.

That’s **Modus Tollens**.
Let’s break it down logically:

You’re given:
- `implication : P → Q`
- `not_q : ¬Q` (i.e., `Q → False`)
Your goal is:
- `¬P` (i.e., `P → False`)

This means:
“Assume `P`. Then use `P → Q` to get `Q`, and then use `¬Q` to show that `Q` leads to `False` — which proves `¬P`.”
Notice how this structure is **very similar to Level 10 (Negation Introduction)**:
- You assume something (`P`)
- Derive a contradiction
- Conclude its negation
But here, you must **chain implications across two steps**:
`P → Q`, then `Q → False`, to eventually get `P → False`.

Let’s walk through this chain and build the logic slowly.
"
/-- Modus Tollens: from `Q → P` and `¬P`, conclude `¬Q`. -/
TheoremDoc Propositional.modus_tollens as "modus_tollens" in "Propositional"
Statement modus_tollens {P Q : Prop} (h₁ : P → Q) (h₂ : ¬Q) : ¬P := by
  Hint "Start by using `intro` to assume that `P` holds. This is needed to prove `¬P`, or `P → False`."
  intro hp
  Hint "Your goal is now `False`. Since you have `h₂ : Q → False`, you can use `apply h₂` to reduce the goal to `Q`."
  apply h₂
  Hint "Now your goal is `Q`, and you have `h₁ : P → Q` and `hp : P`."
  Hint "Use `apply h₁` to reduce the goal to proving `P`, which you already assumed initially."
  apply h₁
  Hint "Now your goal is `P`, and you already have `hp`."
  exact hp


Conclusion "
Well done! You’ve just used **Modus Tollens** with a clean chain of `apply` steps.

This level showed how `apply` works **in reverse**:
- From `False`, you worked backwards through `Q → False` and `P → Q` to reduce everything to `P`, which you already had.

This step-by-step approach gives you precise control over each part of the logic.
"

end Propositional
