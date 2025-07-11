import GameServer.Commands
import Game.Levels.Induction.natdef

namespace Induction

open Induction

World "Induction"
Level 1
Title "n + 0 = n"

Introduction "
Let’s prove the most basic identity: adding `0` to any number `n` gives back `n`.

This is the **base case** of many induction chains.
"
/--
Use `induction` to perform mathematical induction on a natural number.

It splits your goal into:
- a base case (`zero`)
- an inductive step (`succ n`), assuming the result holds for `n`.

This is the backbone of most proofs involving ℕ!
-/
TacticDoc induction

/--
Use `simp` to simplify expressions using known definitions and lemmas.

Great for unfolding things like `add`, `zero`, etc.
-/
TacticDoc simp

/--
Use `rw` (rewrite) to replace one side of an equation with another using a known equality.
-/
TacticDoc rw

/--
Use `rfl` when both sides of the equation are already the same — “reflexivity”.
-/
TacticDoc rfl

Statement (n : ℕ) : n + zero = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [add]
    rw [ih]
    rfl



NewTactic induction simp rw rfl

Conclusion "
You just performed your first induction proof!

This is a cornerstone of formal mathematics — congrats!
"

end Induction
