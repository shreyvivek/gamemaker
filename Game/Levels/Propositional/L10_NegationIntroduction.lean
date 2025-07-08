import GameServer.Commands
import Game.Levels.Propositional.L09_ImplicationChain
namespace Propositional

World "Propositional"
Level 10
Title "Negation Introduction"

Introduction "
You’re now going to prove something of the form `¬P`.

What does that mean?

> `¬P` is just shorthand for `P → False`. Why? See below:

### Truth Table for ¬P and P → False

| P   | ¬P  | P → False |
|-----|-----|-----------|
| T   | F   | F         |
| F   | T   | T         |

So, to prove `¬P`, you must:
1. Assume `P`
2. Derive a contradiction (i.e., prove `False`)
3. That shows `P` can’t be true — which proves `¬P`

This is called **negation introduction** — a foundational pattern in proof by contradiction.

In this level, you're given:
- `h : P → False`
And your goal is to prove `¬P`.

Let’s walk through how to unpack and apply this.
"

Statement (P : Prop) (h : P → False) : ¬P := by
  Hint "Your goal is `¬P`, which is just `P → False`. Use `intro` to assume that `P` holds."
  intro assumed_p
  Hint "Now your goal is to prove `False`. You have `assumed_p : P`, and a function `h : P → False`."
  Hint "`_____ _________ __ __`. By now, you should know what to fill in the blanks! Eventually, it will give you `False`."
  Hint "This shows that assuming `P` leads to `False`, which proves `¬P`."
  exact h assumed_p


Conclusion "
You’ve introduced negation: `¬P` is proven by assuming `P` is true itself. Something like the proof by contradiction, whose applications you would have seen earlier in your math classes.

There is no right or wrong method, use whatever you find more comfortable. After all, the objective of this game is to build that intuition in proving everyday statements/theorems you encounter in math."

end Propositional
