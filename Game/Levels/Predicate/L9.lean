import GameServer.Commands

namespace Predicate

World "Predicate"
Level 9
Title "Combining ∃ and ∀"

Introduction "
Let’s now combine everything:

You’re given:
- `∃ x, P x` — so there’s some x where `P x` holds
- `∀ x, P x → Q x` — so whenever `P x` is true, `Q x` is also true

From this, you want to prove:
```lean
∃ x, P x ∧ Q x
```
This means:
There’s some value of `x` where both `P x` and `Q x` are true.

Let’s do it!
"

Statement {α : Type} (P Q : α → Prop)
(h₁ : ∃ x, P x)
(h₂ : ∀ x, P x → Q x) :
∃ x, P x ∧ Q x := by
Hint "You are given `h₁ : ∃ x, P x`.

Use `cases h₁` to pull out the witness `x` and the proof `hx : P x`."
cases h₁ with
| intro x hx =>
Hint "Now you have:
```lean
x : α

hx : P x
and you know:

h₂ : ∀ x, P x → Q x
```
Apply `h₂ x` to get `Q x` using `have`."
have hq := h₂ x hx
Hint "Now you have both:
```lean
hx : P x

hq : Q x
```
You can combine them like this:

`⟨hx, hq⟩`

Then wrap that with the witness `x` as:

`⟨x, ⟨hx, hq⟩⟩`
```"
exact ⟨x, ⟨hx, hq⟩⟩

Conclusion "
Amazing! 🎉

You just combined:
- An existential (`∃ x, P x`)
- A universal implication (`∀ x, P x → Q x`)
- Into a new existential with a conjunction: `∃ x, P x ∧ Q x`

This is the kind of reasoning that shows up in real math proofs, and you handled it perfectly.
"

end Predicate
