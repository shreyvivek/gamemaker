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

You’ll learn how to use the `have` tactic to break up and name intermediate steps — a powerful tool for writing clean, readable proofs.

_**Note:** There can be many alternative ways to prove the same level, with tactics you may already know. If you are keen, try them out! PS: You will not be prompted with hints in that case :)_
"

/--
Purpose: Use `have` to create and name an intermediate result in your proof.

It lets you:
- Break up long reasoning chains
- Improve clarity and structure
- Reuse partial results later

### Example:

If you have `h₁ : P → Q` and `hp : P`, and you want to reach `Q`, you can write:

`have hq : Q := modus_ponens h₁ hp`.

Similar to what

`exact modus_ponens h₂ hq` would do.

This is useful when proofs grow longer or when you want to give names to intermediate steps to reason about them clearly.
-/
TacticDoc «have»

Statement (P Q R : Prop) (h₁ : P → Q) (h₂ : Q → R) : P → R := by
Hint "Quite obvious, you can start with `intro`."
intro hp
Hint "One way to go ahead is to use the exact statement by writing something like `exact modus_ponens h₂ (modus_ponens h₁ a)`

Looks complicated, and I hope you aren't too confused, because there's an amazing tactic to use here. Read about the `have` tactic on the right.

**Note** that the `have` tactic is strict on syntax, but it simplifies your task in seconds! Also if you just write `modus_ponens h₁ hp` in the `have` tactic, it does the same thing as `exact modus_ponens h₁ hp`"
have hq : Q := h₁ hp
exact h₂ hq

NewTactic «have»

Conclusion "
Perfect! You used the have tactic to extract Q from P → Q, and then concluded R cleanly.

This kind of structured chaining is essential in longer proofs — well done!
"
end Propositional
