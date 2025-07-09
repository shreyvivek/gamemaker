import GameServer.Commands
import Game.Levels.Sets.L06
import Game.Levels.Sets.setdef

open Sets

namespace Sets

World "Sets"
Level 7
Title "Union Superset"

Introduction "
Let’s now bring in a new set operation — **union**.

We write `A ∪ B` for the union of two sets, which means:
> all elements that are in `A`, or in `B`, or in both.

In this level, you're asked to prove:
> `A ⊆ A ∪ B`

In words:
Every element of `A` is definitely in the union `A ∪ B`.

Lean will require you to **choose the correct branch** of the union — use what you’ve learned about proving disjunctions.
"

Statement (A B : Set ℕ) : A ⊆ A ∪ B := by
  Hint "Start with `intro x` and `intro h` — you're assuming `x ∈ A` and must prove `x ∈ A ∪ B`, i.e., `x ∈ A ∨ x ∈ B`."
  intro x
  intro h
  Hint "Since `x ∈ A`, you can conclude `x ∈ A ∨ x ∈ B` by using the `left` tactic. It tells Lean: 'I’ll prove the left side of the disjunction.'"
  left
  exact h

Conclusion "
Perfect!

This is a very important property: every set is a subset of its own union.

You’ll now explore more properties of unions in the next levels.
"

end Sets
