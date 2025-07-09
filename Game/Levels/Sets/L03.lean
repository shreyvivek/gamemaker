import GameServer.Commands
import Game.Levels.Sets.L02
import Game.Levels.Sets.setdef

open Sets

namespace Sets

World "Sets"
Level 3
Title "Subset via Chain"

Introduction "
Let’s now apply the idea of subset proofs with some logical chaining.

You're given:
- `A ⊆ B`
- `B ⊆ C`

Your task: Prove that `A ⊆ C`.

This is called the **transitivity of subsets** — if everything in `A` is in `B`, and everything in `B` is in `C`, then everything in `A` must be in `C` as well.

Use `intro` to assume an arbitrary element and its membership, and then chain your reasoning using `exact`.
"
/--
placeholder have
-/
TacticDoc «have»
Statement (A B C : Set ℕ) (h₁ : A ⊆ B) (h₂ : B ⊆ C) : A ⊆ C := by
  Hint "Start by assuming an arbitrary element from `A` using `intro x`."
  intro x
  Hint "Assume that `x ∈ A` using `intro h`."
  intro h
  Hint "Since `h₁ : A ⊆ B`, and `h : x ∈ A`, you can use `have` to create `x ∈ B`."
  Hint "This is analogous to `h₁ : P → Q` and `h : P`. To prove `Q`, we would write `have hq: Q := modus_ponens h₁ h`. In fact, even `have hq: Q := h₁ h` would work!"
  Hint "In our case now, we would write something very similar : `have xb : x ∈ B := h₁ h`. But this is not fully correct. We need to keep in mind that we're dealing with Sets, not Propositions. Hence, we must specify which member of the set we are actually talking about; in this case - `x`."
  Hint "So the correct command would be : `have xb : x ∈ B := h₁ x h`."

  have xb : x ∈ B := h₁ x h
  Hint "Now use `h₂ : B ⊆ C` to conclude that `x ∈ C`, similar to the previous command."
  exact h₂ x xb

NewTactic «have»
Conclusion "
Nice work!

This was an example of **chaining subset relations**, and formally proves that subsets are transitive:

If `A ⊆ B` and `B ⊆ C`, then `A ⊆ C`.

You’ll use this kind of reasoning a lot in set theory.
"

end Sets
