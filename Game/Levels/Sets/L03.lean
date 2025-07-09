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
Purpose: Create and name an intermediate result in your proof.

The `have` tactic is used when you want to:
- Break up a long proof into smaller steps
- Store a useful intermediate result
- Avoid repeating expressions

`have h : P := proof_of_P`
This introduces a new local hypothesis `h` with value `P`.

**Example:**

If you have:

h₁ : A ⊆ B (which is a function: x ∈ A → x ∈ B)

h : x ∈ A

Then you can write:

`have xb : x ∈ B := h₁ x h`
Now `xb` stores `x ∈ B` for later use.
-/
TacticDoc «have»

Statement (A B C : Set ℕ) (h₁ : A ⊆ B) (h₂ : B ⊆ C) : A ⊆ C := by
  Hint "Start by assuming an arbitrary element from `A` using `intro x`."
  intro x
  Hint "Assume that `x ∈ A` using `intro h`."
  intro h
  Hint "Since `h₁ : A ⊆ B`, and `x ∈ A`, you can use `have` to create `x ∈ B`."
  have xb : x ∈ B := h₁ x h
  Hint "Now use `h₂ : B ⊆ C` to conclude that `x ∈ C`."
  exact h₂ x xb

NewTactic «have»

Conclusion "
Nice work!

This was an example of **chaining subset relations**, and formally proves that subsets are transitive:

If `A ⊆ B` and `B ⊆ C`, then `A ⊆ C`.

You’ll use this kind of reasoning a lot in set theory.
"

end Sets
