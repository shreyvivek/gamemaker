import GameServer.Commands
import Game.Levels.Propositional.L08_OrElimination
namespace Propositional

World "Propositional"
Level 9
Title "Implication Chain"

Introduction "
You’re given two facts:

1. If `P` is true, then `Q` is true. (`P → Q`)
2. If `Q` is true, then `R` is true. (`Q → R`)

Your task: prove that `P` implies `R` — in other words, show that `P → R`.

This is called **chaining implications**. It’s a very common pattern in logic and proofs.

The idea is:
“If `P` gives me `Q`, and `Q` gives me `R`, then `P` gives me `R`.”

In this level, you’ll:
- assume `P` is true,
- use it to get `Q` via the first implication,
- and then use that `Q` to get `R` via the second implication.

Let’s walk through this chain step by step.

_**Note:** There can be many alternative ways to prove the same level, with tactics you may already know. If you are keen, try them out!
PS: You will not be prompted with hints in that case :)_
"

/-- From `P → Q` and `Q → R`, derive `P → R`. -/
TheoremDoc Propositional.implication_chain as "ImplicationChain" in "Propositional"

Statement implication_chain (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) : P → R := by
  Hint "Start with `intro` to assume that `P` is true."
  intro hp
  Hint "Now finish the level off using `{h₁}` and `{h₂}`. Make use of the exact tactic in a similar manner like you did in the last level.

  `exact (modus_ponens h₁ a)` probably gives you `Q`, but the goal is `R`. But you also have `{h₂}`. So try giving an appropriate prefix/suffix to `(h₁ a)` with `h₂`, chaining the modus_ponens operation correctly.

  Note that binding with brackets here is very important for Lean to understand what you're proving. Else, it throws you a *type mismatch*."
  exact h₂ (h₁ hp)


Conclusion "
Perfect! You directly chained together `P → Q → R` into `P → R` with `exact` and `Modus Ponens`.

By the way, you have crossed the half way mark! Congratulations, keep the momentum going!"

end Propositional
