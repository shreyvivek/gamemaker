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

Statement {α : Type} (P : α → Prop) (a : α) (h : P (a)) : ∃ x, P (x) := by
Hint "You are trying to prove `∃ x, P x`. That means you need to provide a witness — a specific value — and show that it satisfies `P`.

Once you have `P a`, it is straightforward.'

But you already have `P a`. So we do need to make use of the `exact` tactic.

The syntax is a bit different though. You need to type in `exact ⟨a, h⟩`."

Hint "This is Lean's syntax for a **pair** (a tuple).
It builds a value of type `∃ x, P x` by giving:
- `a`: the specific value (the witness)
- `h`: a proof that `P a` is true

So when you write:

`exact ⟨a, h⟩`
You're saying:

“The thing that satisfies `∃ x, P x` is `a`, and here’s a proof `h` that `P a` holds.”"
exact ⟨a, h⟩

Conclusion "
Great job! 🎉

You’ve just used existential introduction by giving an example where the predicate holds.

From P(a), you concluded ∃ x, P(x) — saying that at least one such `x` exists.
"

end Predicate
