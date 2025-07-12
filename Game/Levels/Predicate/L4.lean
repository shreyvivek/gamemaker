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


Statement {α : Type} (P : α → Prop) (Q : Prop) (h : ∃ x, P x) (hQ : ∀ x, P x → Q) : Q := by
Hint "Use `cases h with | intro x hx =>` to extract the witness `x` and the proof `hx : P x`. It is a unique combination of `cases` and `intro` tactics, but is the most elegant way to prove it here."
cases h with
|intro x hx =>
Hint "Now you have `x : α` and `hx : P x`. Use the universal statement `hQ : ∀ x, P x → Q`.

If it wasn't obvious, yes, we will make use of the `apply` tactic, but it looks slightly different in predicate logic.

It wouldn't be just `apply hQ`. We also need to specify which element we are working on, which is `x` in this case. So do `apply hQ x`."
apply hQ x
Hint "Lean wants you to prove P x, which you have as hx."
exact hx

Conclusion "
Nice! 🎉

You just performed existential elimination:

You started with `∃ x, P (x).`

Then used `cases` to extract a witness and its property and applied a general rule to that specific value.

Hence, this is one of the most important tools for reasoning about existential statements.
"

end Predicate
