import GameServer.Commands
import Game.Levels.Induction.natdef

namespace Induction

World "Induction"
Level 2
Title "Prove ∀ n, n + 0 = n"

Introduction "
You’ve seen the base case. Now let’s prove a **universal identity** using **mathematical induction**! 🧠

We aim to prove:

```lean
∀ n : ℕ, n + 0 = n
```
This means: for every natural number n, adding 0 on the right does not change the number.

We’ll proceed by induction on n.

In this game, we are using our own custom natural numbers (ℕ) defined using MyNat.
Lean won't assume any built-in knowledge about +, so we prove everything from scratch!
"

/--
Use `induction n with` to perform induction on `n`.

It splits your goal into:

--The base case (n = 0).

--The inductive step, where you assume the statement for n (the induction hypothesis),
and prove it for succ n, i.e., the successor of n.

Lean will automatically give names like `zero`, `succ`, and `ih`.

Within the succ branch, use `rewrite (rw)` to apply previously proven theorems like add_succ

Combine with the induction hypothesis to finish the proof

Finally, `rfl` often concludes the goal once both sides match.
-/
TacticDoc induction


/--
The `rw` tactic stands for **rewrite**.

It allows you to replace part of your goal using a known equation.

For example, if you have:
```lean
ih : k + 0 = k
and your goal is:

succ (k + 0) = succ k
then:

rw [ih]
will turn the goal into:

succ k = succ k
```
which can then be solved using `rfl`.

You can also use rewrite lemmas like `add_succ` or `add_zero`:

```lean
rw [add_succ]
```
Lean replaces the left side using the definition:
```lean
succ n + m = succ (n + m)
```
You can rewrite multiple things:
```lean
rw [add_succ, ih]
```
-/
TacticDoc rw


Statement : ∀ n : ℕ, n + MyNat.zero = n := by
Hint "We want to prove this for all n. Use `intro n` first, then perform `induction n with`."
intro n
induction n with
| zero =>
Hint "This is the base case: `0 + 0 = 0`, which follows directly by definition.

So you can do `rfl`, because that is exactly what you need to conclude the base case."
rfl
| succ k ih =>
Hint "
You're now in the inductive step.

Your goal is:
```lean
succ k + 0 = succ k
```
Use the definition of addition:
```lean
succ k + 0 = succ (k + 0)
```
Then use the induction hypothesis:
```lean
ih : k + 0 = k
```
Applying only `rw` will solve it."
rw [MyNat.add_succ, ih]

NewTactic induction rw
Conclusion "
Fantastic! 🎉

You’ve completed a full induction proof.

You showed:

`0 + 0 = 0 (base case)`

`succ k + 0 = succ k` assuming it was true for k (inductive step)

This is how we prove facts for all natural numbers — one step at a time!

Ready for more? Let’s go!
"

end Induction
