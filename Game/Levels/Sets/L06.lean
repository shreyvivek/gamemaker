import GameServer.Commands
import Game.Levels.Sets.L05
import Game.Levels.Sets.setdef

open Sets

namespace Sets

World "Sets"
Level 6
Title "Commutativity of Intersection"

Introduction "
Time for your first **set equality** proof!

You’re proving that: `A ∩ B = B ∩ A`

That means:
- every element of `A ∩ B` is in `B ∩ A` (*left-to-right*),
- and every element of `B ∩ A` is in `A ∩ B` (*right-to-left*).

This is called the **commutativity of intersection**.

You already proved both directions separately before — now combine them together!
"

Statement (A B : Set ℕ) : Equal (A ∩ B) (B ∩ A) := by
  Hint "To prove set equality, use `constructor` to break the goal into two subset goals: `⊆` in both directions."
  constructor

  -- Direction 1: A ∩ B ⊆ B ∩ A
  Hint "Begin by assuming `x : ℕ` is an arbitrary element of `A ∩ B`."
  intro x
  Hint "Now assume the hypothesis `h : x ∈ A ∩ B`. That means you have both `x ∈ A` and `x ∈ B`."
  intro h
  have xa := h.left
  have xb := h.right
  Hint "You now want to prove that `x ∈ B ∩ A`. Use `constructor` to build that conjunction."
  constructor
  Hint "First, prove `x ∈ B` using `exact xb`."
  exact xb
  Hint "Then, prove `x ∈ A` using `exact xa`."
  exact xa

  -- Direction 2: B ∩ A ⊆ A ∩ B
  Hint "Now prove the reverse direction using the same pattern."
  intro x
  intro h
  have xb := h.left
  have xa := h.right
  constructor
  exact xa
  exact xb

Conclusion "
Excellent!

You’ve now formally proved that intersection is **commutative** — the order of sets doesn't matter.

This idea appears often when simplifying or rearranging set expressions.
"

end Sets
