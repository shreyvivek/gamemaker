import GameServer.Commands

namespace Predicate

World "Predicate"
Level 5
Title "Nested Quantifiers"

Introduction "
You’ve worked with `∀` and `∃` individually. Now let’s **combine** them.

Suppose we’re told:
> \"For every `x`, there exists a `y` such that `P(x, y)` holds.\"

That’s written as:
```lean
∀ x, ∃ y, P(x, y)
```
In Lean, you can treat universal quantifiers (`∀`) like functions.

So:

```lean
h : ∀ x, ∃ y, P(x, y)
a : α
```

Then we get to
```lean
h a : ∃ y, P(a, y)
```

Let's try to break this down!
"

Statement {α : Type} (P : α → α → Prop) (a : α) (h : ∀ x, ∃ y, P x y) : ∃ y, P a y := by
Hint "You want to prove `∃ y, P a y`, and you have a general rule: `∀ x, ∃ y, P x y`.

`apply h` to `a` to get: `∃ y, P a y`."
apply h a

Conclusion "
Awesome! 🎉

You just worked with a nested quantifier:

`h : ∀ x, ∃ y, P(x, y)` means every `x` has its own matching `y`

By applying it to a specific `a`, you got `∃ y, P(a, y)`.

This pattern — universal followed by existential — is very common in mathematical reasoning.
"

end Predicate
