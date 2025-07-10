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
/-- Modus Tollens: from `P → Q` and `¬Q`, conclude `¬P`. -/
TheoremDoc Propositional.modus_tollens as "modus_tollens" in "Propositional"
Statement modus_tollens {P Q : Prop} (h₁ : P → Q) (h₂ : ¬Q) : ¬P := by
  Hint "
We are proving `¬P`, which means the goal is `P → False`.

This type is a function — it says: “If you give me a proof of `P`, I will return a contradiction.”

To do that, **assume `P` holds**, and then try to derive a contradiction from it.

Use the `intro` tactic to assume `P`.
"
  intro hp
  Hint "
Now your goal has become `False`.

Let’s see what you have:

- `h₂ : ¬Q` (this means `Q → False`)
- `h₁ : P → Q`
- `hp : P`

We want to reach a contradiction — `False`.

Let’s look at `h₂`. It says:
> “If you give me `Q`, I’ll give you `False`.”

So the idea is: **try to produce `Q`, then feed it into `h₂`.**

Use `apply h₂` to say:
> “To prove `False`, it’s enough to prove `Q`.”
"
  apply h₂
  Hint "
Now your goal is to prove `Q`.

How can we get `Q`?

You have:
- `h₁ : P → Q`
- `hp : P`

So this is a perfect match for applying an implication.

Use `apply h₁` to transform your goal from `Q` to `P`.
"
  apply h₁
  Hint "
Now your goal is `P`.

But you already assumed `P` at the very beginning, as `hp`.

So simply use:
`exact hp`

to conclude the proof.
"
  exact hp
Conclusion "
Well done! You’ve just used **Modus Tollens** with a clean chain of `apply` steps.

This level showed how `apply` works **in reverse**:
- From `False`, you worked backwards through `Q → False` and `P → Q` to reduce everything to `P`, which you already had.

This step-by-step approach gives you precise control over each part of the logic.
"

end Propositional
