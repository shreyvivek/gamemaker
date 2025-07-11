import GameServer.Commands
import Game.Levels.Sets.setdef


namespace Sets

World "Sets"
Level 1
Title "Set Membership"

Introduction "
Welcome to the world of **Set Theory**!

Sets are collections of objects. We write `x ∈ A` to say that *element x is in set A*.

This level introduces one of the most fundamental ideas: **membership**.

In Lean, we work with `x ∈ A` as a proposition, which we can use in proofs.

Let’s prove something simple!
"


Statement (A : Set ℕ) (x : ℕ) (h : x ∈ A) : x ∈ A := by
  Hint "You are trying to prove `x ∈ A`. And you already have `h : x ∈ A`.

Just use `exact h` to complete the proof."
  exact h


Conclusion "
Great start!

You’ve just used a given assumption to complete a proof.

Set membership (`x ∈ A`) is one of the most basic ideas in math — and you’ll use it a lot in upcoming levels.
"

end Sets
