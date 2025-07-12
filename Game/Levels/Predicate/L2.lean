import GameServer.Commands

namespace Predicate

World "Predicate"
Level 2
Title "Universal Elimination"

Introduction "
Let’s dive deeper into **universal statements** — ones that say something is true for *every* value.

For example:
> \"Everyone is a student\" would mean `∀ x, P(x)`, which means, for all `x`, `P(x)` is true, which simply means, for all `x`, “x is a student”.

Once we know something is true for **all** values, we can plug in any specific one.

So from `∀ x, P(x)`, we can conclude `P(a)`, for some value `a` — this is called **universal elimination**.

*Note: `P x` and `P (x)` mean the same. Lean removes the parentheses by default.*
"

Statement {α : Type} (P : α → Prop) (a : α) (h : ∀ x, P (x)) : P (a) := by
Hint "You are given `h : ∀ x, P x`, and want to prove `P a`.

Just `apply` the universal statement to the specific value `a`."
apply h

Conclusion "
Nice work! 🎉

You’ve just used **universal elimination** — plugging a value into a statement that's true for all.

From `∀ x, P(x)` you derived `P(a)`. This is one of the most common and powerful rules in predicate logic!
"

end Predicate
