import GameServer.Commands

namespace Predicate

World "Predicate"
Level 7
Title "Negating ∃"

Introduction "
Let’s learn how to reason with a **negated existential** statement.

Suppose you’re told:
> “There is **no** value of `x` for which `P(x)` is true.”

That’s written as:
```lean
¬ (∃ x, P x)
```
This means:

“For every `x`, `P(x)` must be false” — or in logic terms:
```lean
∀ x, ¬ P x
```
We’ll now prove this!
"

Statement {α : Type} (P : α → Prop) (h : ¬ (∃ x, P x)) : ∀ x, ¬ P x := by
Hint "Your goal is to prove `∀ x, ¬ P x`.

So first, assume an arbitrary `x` using `intro x`."
intro x
Hint "Now you want to prove `¬ P x`. This means: assume `P x` and derive a contradiction.

Use `intro hPx` to assume `P x`."
intro hPx
Hint "Now think: If you know that `P x` is true, then you can say:

'There exists some x such that P x is true.'

Lean lets you write that as:
```lean
exact Exists.intro x hPx
```
But it can be packed better with the angular brackets as you read in Level 3.

```lean
⟨x, hPx⟩
```
This is a value of type `∃ x, P x` — a witness `x` and proof `hPx`.

So use:
```lean
exact h ⟨x, hPx⟩
```

This says: “Here’s an example of something that shouldn’t exist,” and Lean will conclude a contradiction."

Hint "If you notice, this looks a bit similar to stuff that we have encountered in Propositional Logic.

`exact ¬P P` and `exact ¬(∃ x, P x) (∃ x, P x)`, both result in `False`.

The structure in the exact statement you're about to use, resembles `exact ¬(∃ x, P x) (∃ x, P x)`. It is now time for you to observe the pattern!"
exact h ⟨x, hPx⟩

Conclusion "
Awesome! 🎉

You just proved that:
```lean
¬ (∃ x, P x) → ∀ x, ¬ P x
```
This is a powerful logical transformation.

*Key idea:* To prove something doesn’t exist, show that any attempt to build it leads to contradiction.
"

end Predicate
