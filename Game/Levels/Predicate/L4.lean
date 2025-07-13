import GameServer.Commands

namespace Predicate

World "Predicate"
Level 4
Title "Existential Elimination"

Introduction "
You've seen how to *prove* that something exists. Now let’s see how to *use* such a fact.

Suppose you're told:

> \"There exists an `x` such that `P(x)` is true\" — written as `∃ x, P(x)`

This means:
> \"Some value satisfies the property `P` — but we don’t know which one yet.\"

To work with this, we can use the `cases` tactic to:
1. Pull out a specific witness - `x`.
2. Pull out the proof that this witness satisfies `P` - `hx`.

This is called **existential elimination**.

*Note: `P x` and `P (x)` mean the same thing — Lean just omits the parentheses by default.*
"


Statement {α : Type} (P : α → Prop) (Q : Prop) (h : ∃ w, P w) (hQ : ∀ w, P w → Q) : Q := by
Hint "Use `cases h` to extract the witness `w` and the proof `h_1 : P w`."
cases h with
|intro w h_1 =>
Hint "Now you have `w : α` and `h_1 : P w`. Use the universal statement `hQ : ∀ w, P w → Q`.

It wouldn't be just `apply hQ`. We also need to specify which element we are working on, which is `w` in this case. So do `apply hQ w`."
apply hQ w
Hint "Lean wants you to prove `P w`, which you have as `h_1`."
exact h_1

Conclusion "
Nice! 🎉

You just performed existential elimination:

You started with `∃ w, P (w).`

Then used `cases` to extract a witness and its property and applied a general rule to that specific value.

This is actually one of the most important tools for reasoning about existential statements.
"

end Predicate
