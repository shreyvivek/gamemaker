import GameServer.Commands
import Game.Levels.Sets.L08
import Game.Levels.Sets.setdef

open Sets

namespace Sets

World "Sets"
Level 9
Title "Commutativity of Union"

Introduction "
You’re now ready to prove that `A ∪ B = B ∪ A` — that is, **union is commutative**.

From earlier levels:
- You proved `A ⊆ A ∪ B` and `A ∪ B ⊆ B ∪ A`.
- You’ve learned how to split and construct disjunctions using `cases`, `left`, and `right`.

Now, use these together to prove **both directions** of the subset relation.
"

Statement (A B : Set ℕ) : Equal (A ∪ B) (B ∪ A) := by
  Hint "To prove set equality, start with `constructor` to break the goal into two subset proofs: `⊆` in both directions."
  constructor

  -- Direction 1: A ∪ B ⊆ B ∪ A
  Hint "Assume an arbitrary element `x : ℕ`, and a hypothesis `h : x ∈ A ∪ B`."
  intro x
  intro h
  Hint "`h` is a disjunction — `x ∈ A ∨ x ∈ B`. Use `cases h` to split into the two cases."
  cases h with
  | inl ha =>
    Hint "`x ∈ A` holds here. Since your goal is `x ∈ B ∪ A`, use `right` to focus on the second part of the union."
    right
    exact ha
  | inr hb =>
    Hint "`x ∈ B` holds here. So use `left` to show `x ∈ B ∪ A` by focusing on the first part."
    left
    exact hb

  -- Direction 2: B ∪ A ⊆ A ∪ B
  Hint "Then repeat the same reasoning, but with `B ∪ A` on the left side."
  intro x
  intro h
  cases h with
  | inl hb =>
    Hint "You can take it from here."
    right
    exact hb
  | inr ha =>
    left
    exact ha


Conclusion "
Great work!

You’ve now proved that **union is commutative** — just like intersection.

This reinforces how logic and set theory walk hand-in-hand!
"

end Sets
