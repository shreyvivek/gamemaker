import GameServer.Commands
import Game.Levels.Sets.L01
import Game.Levels.Sets.setdef
open Sets

namespace Sets

World "Sets"
Level 2
Title "Subset Intro"

Introduction "
Let’s now talk about **subsets**.

We write `A ⊆ B` to mean *every element of A is also an element of B*. That is: `∀ x, x ∈ A → x ∈ B`

This level helps you prove that every set is a subset of itself, using basic logic and the `intro` and `exact` tactics.
"

Statement (A : Set ℕ) : A ⊆ A := by
  Hint "
In order to do this proof in Lean, we use `intro x` to introduce an element `x` which belongs to both sets. Then, `intro h` assumes `x ∈ A` is true, then we write `exact h`.

You are proving `A ⊆ A`, which means: for all `x`, if `x ∈ A` then `x ∈ A`."
  intro x
  intro h
  exact h

Conclusion "
Well done!

You've just proved that a set is a subset of itself — this is called **reflexivity** of subsets.

You'll use this idea as a stepping stone for more complex subset proofs.
"

end Sets
