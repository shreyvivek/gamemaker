import GameServer.Commands

namespace Induction

World "Induction"
Level 1
Title "Base Case"

Introduction "
Welcome to the world of **Mathematical Induction**! 🌱

We'll begin by proving the **base case** of a simple statement:

> For all natural numbers `n`, `n + 0 = n`

This level focuses only on the **base case**, where `n = 0`.
"

/--
`rfl` stands for “reflexivity of equality”.

It can be used when both sides of your goal are definitionally equal — meaning Lean can reduce/simplify both sides to the same expression.

You’ll use `rfl` all the time to finish goals like `0 + 0 = 0`, `n = n`, etc.
-/
TacticDoc rfl

Statement : 0 + 0 = 0 := by
Hint "You're trying to show `0 + 0 = 0`.

Lean knows how to compute `0 + 0`, and simplifies it automatically using its built-in definition of addition.

So simply type `rfl`."
rfl

NewTactic rfl
Conclusion "
Nice! You’ve proven the base case. 🎉

The next step is the **inductive step** — where we assume the statement for `n` and prove it for `n + 1`.
"

end Induction
