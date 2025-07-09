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

We write `A ⊆ B` to mean *every element of A is also in B*. That is: `∀ x, x ∈ A → x ∈ B`

This level helps you prove that one set is a subset of another, using basic logic and the `intro` and `exact` tactics.
"
/--
placeholder intro
-/
TacticDoc intro
Statement (A : Set ℕ) : A ⊆ A := by
  Hint "
To prove a subset, use `intro x` and `intro h`, then apply `exact h`.

You are proving `A ⊆ A`, which means: for all `x`, if `x ∈ A` then `x ∈ A`."
  intro x
  intro h
  exact h

NewTactic intro
Conclusion "
Well done!

You've just proved that a set is a subset of itself — this is called **reflexivity** of subsets.

You'll use this idea as a stepping stone for more complex subset proofs.
"

end Sets
