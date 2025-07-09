import GameServer.Commands
import Game.Levels.Sets.L07
import Game.Levels.Sets.setdef

open Sets

namespace Sets

World "Sets"
Level 8
Title "Breaking a Union"

Introduction "
Previously, you proved that every element of `A` is also in `A ∪ B`.

Now you’ll do the **reverse**:
You’re given `x ∈ A ∪ B`, and must show that `x ∈ B ∪ A`.

Even though the goal is another union, this time your **assumption** is a union. That means you’ll need to break it apart using `cases`.

This level helps you understand how **disjunction elimination** works in the context of sets.
"

Statement (A B : Set ℕ) : A ∪ B ⊆ B ∪ A := by
  Hint "Start with `intro x` and `intro h` to assume `x ∈ A ∪ B`."
  intro x
  intro h
  Hint "`h` is a disjunction — `x ∈ A ∨ x ∈ B`. Use `cases h with` to split into two possibilities."
  cases h with
  | inl ha =>
    Hint "`x ∈ A` is true in this branch. So, to prove `x ∈ B ∪ A`, use `right` — you want to show the second part of the union."
    right
    exact ha
  | inr hb =>
    Hint "`x ∈ B` is true here. So, use `left` to show the first part holds."
    left
    exact hb

Conclusion "
Well done!

You just deconstructed a union and rearranged it — this is part of proving the **commutativity** of union.

Later, you'll use this pattern in longer, chained proofs.
"

end Sets
