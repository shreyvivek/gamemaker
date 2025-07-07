import GameServer.Commands

-- Minimal definition of Set and membership
def Set (α : Type) := α → Prop
notation:50 x " ∈ " A => A x

namespace Sets

World "Sets"
Level 1
Title "Set Membership"

Introduction "
Welcome to the world of **Set Theory**! 🧺

Sets are collections of objects. We write `x ∈ A` to say that *element x is in set A*.

This level introduces one of the most fundamental ideas: **membership**.

In Lean, we work with `x ∈ A` as a proposition, which we can use in proofs.

Let’s prove something simple!
"

/--
Purpose: Use the `exact` tactic when your goal matches something you already know.

You’re given:
- A set `A : Set ℕ`
- An element `x : ℕ`
- A hypothesis `h : x ∈ A`

And your goal is to prove exactly that: `x ∈ A`.

Since your goal *already matches* your assumption, just use:
`exact h`

This is the most basic kind of step in a proof: confirming something you’ve already assumed.
-/
TacticDoc exact



Statement (A : Set ℕ) (x : ℕ) (h : x ∈ A) : x ∈ A := by
  Hint "You are trying to prove `x ∈ A`. And you already have `h : x ∈ A`.

Just use `exact h` to complete the proof."
  exact h



Conclusion "
Great start! ✅

You’ve just used a given assumption to complete a proof.

Set membership (`x ∈ A`) is one of the most basic ideas in math — and you’ll use it a lot in upcoming levels.
"

end Sets
