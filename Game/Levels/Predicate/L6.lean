import GameServer.Commands

namespace Predicate

World "Predicate"
Level 6
Title "Existential Before Universal"

Introduction "
Let’s look at **another nesting** of quantifiers — this time:

> \"There exists an `x` such that for every `y`, `P(x, y)` holds.\"

This is written:
```lean
∃ x, ∀ y, P(x, y)
```
This means there is one special `x` that works for all `y`.

So to prove a particular P(a, b), it’s enough to:
- Pull out that special `x`
- Apply the universal rule for `y = b`

We’ll use a combination of `intro` and `exact`.
"

Statement {α : Type} (P : α → α → Prop) (a : α) (h : ∃ x, ∀ y, P x y) : ∀ y, P a y → ∃ x, P x y := by
Hint "You want to prove a universal statement: `∀ y, P a y → ∃ x, P x y.`

This means we should assume an arbitrary value of `y`, and a hypothesis that `P a y` holds.

Use the intro tactic twice to bring them into the context : `intro y hy`"
intro y hy
Hint "Now your goal is: `∃ x, P x y`.

You already have a proof of `P a y` (it's called `hy`).

To prove that there exists such an `x`, it’s enough to give a specific example — and you know that `a` works!

Use the existential introduction syntax to finish off (with `exact`)."
exact ⟨a, hy⟩

Conclusion "
Awesome! 🎉

You just worked through a nested quantifier goal — in the reverse direction from before.

From:
```lean
P a y
```
you concluded:
```lean
∃ x, P x y
```
This is called **existential introduction** — and you used the value `a` as your witness.

Pay attention to the order of quantifiers:

`∀ x, ∃ y` means each `x` may have its own `y`

`∃ x, ∀ y` means one single `x` works for every `y`

These are not logically equivalent — and you now understand how to prove statements from both.
"

end Predicate
