import GameServer.Commands
import Game.Levels.Sets.L03
import Game.Levels.Sets.setdef

open Sets

namespace Sets

World "Sets"
Level 4
Title "Subset of Intersection"

Introduction "
Let’s prove something involving **intersection of sets**.

You are given:
- `A ⊆ B`
- `A ⊆ C`

You are asked to prove:
- `A ⊆ B ∩ C`

Remember, intersection (`B ∩ C`) means the set of all elements that are in **both** `B` and `C`.

So this level asks: if everything in `A` is in both `B` and `C`, can we say `A` is a subset of `B ∩ C`?

Let’s find out!
"

Statement (A B C : Set ℕ) (hAB : A ⊆ B) (hAC : A ⊆ C) : A ⊆ B ∩ C := by
  Hint "You're proving a subset relation. Start with `intro x` and then `intro h` to assume `x ∈ A`."
  intro x
  intro h
  Hint "You want to prove `x ∈ B ∩ C`, which means both `x ∈ B` and `x ∈ C`.

  Use `have` twice — once to get `x ∈ B` from `hAB`, and once to get `x ∈ C` from `hAC`."
  have xb : x ∈ B := hAB x h
  have xc : x ∈ C := hAC x h
  Hint "Now construct the pair `(xb, xc)` using the `constructor` tactic. That will prove `x ∈ B ∩ C`."
  constructor
  exact xb
  exact xc

Conclusion "
Excellent work!

You've shown that if everything in `A` is in both `B` and `C`, then everything in `A` is also in their intersection.

This is one of the most common patterns in set theory — you'll use it a lot going forward.
"

end Sets
