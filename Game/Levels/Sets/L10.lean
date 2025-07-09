import GameServer.Commands
import Game.Levels.Sets.L09
import Game.Levels.Sets.setdef

open Sets

namespace Sets

World "Sets"
Level 10
Title "Distributivity of ∩ over ∪"

Introduction "
Let’s take things up a notch!

In this level, you’ll prove:

`A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`.

This is called the **distributivity of intersection over union** — it lets you simplify nested set expressions logically.

You’ll combine everything you’ve seen so far:
- `constructor` for set equality
- `cases` to break disjunctions
- `.left` / `.right` for conjunctions
- `left` / `right` to construct disjunctions
"

Statement (A B C : Set ℕ) : Equal (A ∩ (B ∪ C)) ((A ∩ B) ∪ (A ∩ C)) := by
  Hint "To prove set equality, use `constructor` to split the goal into two subset directions."
  constructor

  -- Direction 1: A ∩ (B ∪ C) ⊆ (A ∩ B) ∪ (A ∩ C)
  Hint "Assume an arbitrary `x` and the hypothesis `h : x ∈ A ∩ (B ∪ C)`."
  intro x
  intro h
  Hint "Break the conjunction using `.left` and `.right`."
  have ha := h.left
  have hub := h.right
  Hint "`x ∈ B ∪ C` is a disjunction. Use `cases` to split it."
  cases hub with
  | inl hb =>
    Hint "`x ∈ B` holds. Combine with `x ∈ A` using `constructor`, then use `left` to insert into `(A ∩ B) ∪ (A ∩ C)`."
    left
    constructor
    exact ha
    exact hb
  | inr hc =>
    Hint "`x ∈ C` holds. Combine with `x ∈ A`, then use `right` to finish."
    right
    constructor
    exact ha
    exact hc

  -- Direction 2: (A ∩ B) ∪ (A ∩ C) ⊆ A ∩ (B ∪ C)
  Hint "Now assume `x ∈ (A ∩ B) ∪ (A ∩ C)`. Use `cases` to split the disjunction."
  intro x
  intro h
  cases h with
  | inl hab =>
    have ha := hab.left
    have hb := hab.right
    Hint "Construct `x ∈ A ∩ (B ∪ C)` by first proving `x ∈ A`, then `x ∈ B ∨ C` using `left`."
    constructor
    exact ha
    left
    exact hb
  | inr hac =>
    have ha := hac.left
    have hc := hac.right
    constructor
    exact ha
    right
    exact hc


Conclusion "
Superb!

You just proved one of the most important set identities: **distributivity of ∩ over ∪**.

This type of proof trains you to handle complex logical structure using simple steps — a critical skill in discrete math.
"

end Sets
