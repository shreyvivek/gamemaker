import GameServer.Commands
import Game.Levels.Sets.L04
import Game.Levels.Sets.setdef

open Sets

namespace Sets

World "Sets"
Level 5
Title "Unpack Both Sides"

Introduction "
Let’s make things a little more interesting.

You’re given: `x ∈ A ∩ B`

Your goal is to show: `x ∈ B ∩ A`

This may seem trivial, but it helps build the skill of **manipulating set expressions** using logical tools.

The key is to:
- Extract both parts of the intersection from `h : x ∈ A ∩ B`
- Recombine them in reverse order using `constructor`.
"

/--
We use this to show `A ∩ B ⊆ B ∩ A`-/
TheoremDoc Sets.A_and_B_subset_B_and_A as "A_and_B_subset_B_and_A" in "Sets"
Statement A_and_B_subset_B_and_A (A B : Set ℕ) : A ∩ B ⊆ B ∩ A := by
  Hint "Start with `intro x`, then `intro h` to assume `x ∈ A ∩ B`."
  intro x
  intro h
  Hint "`h` is a pair: `x ∈ A ∧ x ∈ B`.

Use `h.left` to get `x ∈ A`, and `h.right` to get `x ∈ B` using `have` tactic."
  have xa := h.left
  have xb := h.right
  Hint "Now use `constructor` to prove `x ∈ B ∩ A`, which means `x ∈ B ∧ x ∈ A`."
  constructor
  exact xb
  exact xa

Conclusion "
Awesome!

You just took apart an intersection and built a new one in reverse.

This simple trick underpins many proofs involving **set equalities** — where you must show two sets contain the same elements.
"

end Sets
