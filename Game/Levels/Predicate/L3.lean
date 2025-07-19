import GameServer.Commands

namespace Predicate

World "Predicate"
Level 3
Title "Existential Introduction"

Introduction "
Time to look at **existential statements** — ones that say *something exists*.

For example:
> \"There exists a student\" means `∃ x, P(x)`, which means, for some `x`, `P(x)` is true, which simply means, for some `x`, “x is a student”. There could be more than one such `x` value. But there **definitely is one `x`** for which it is true.

To prove this, it’s enough to show one example:
If you can prove `P(a)` for some `a`, then `∃ x, P(x)` is true.

This is called **existential introduction**.

*Note: `P x` and `P (x)` mean the same. Lean just omits the parentheses by default.*
"

/--
  The constructor `Exists.intro` is used to prove an existential statement.
  Given a value `a : α` and a proof `h : P a`, `Exists.intro a h` proves `∃ x, P x`.
-/
TheoremDoc Exists.intro as "Exists.intro" in "Predicate"


Statement {α : Type} (P : α → Prop) (a : α) (h : P (a)) : ∃ x, P (x) := by
Hint "You are trying to prove `∃ x, P x`. That means you need to provide a witness — a specific value — and show that it satisfies `P`.

Once you have `P a`, it is straightforward.'

But you already have `P a`. So we do need to make use of the `exact` tactic.

The syntax is a bit different though. You need to type in `exact ⟨a, h⟩`.

But this can look a bit complicated. So we make use of `Exists.intro`. Read more about it by clicking its documentation on the right."

Hint "With `Exists.intro`, we are building a value of type `∃ x, P x` by giving:
- `a`: the specific value (the witness)
- `h`: a proof that `P a` is true

Use the constructor `Exists.intro a h`, written after `exact`, to build the required object."
exact Exists.intro a h


NewTheorem Exists.intro
Conclusion "
Great job! 🎉

You’ve just used existential introduction by giving an example where the predicate holds.

From P(a), you concluded `∃ x, P(x)` — saying that at least one such `x` exists.
"

end Predicate
