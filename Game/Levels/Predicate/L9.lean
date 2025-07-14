import GameServer.Commands

namespace Predicate

World "Predicate"
Level 9
Title "Combining ∃ and ∀"

Introduction "
Let’s now combine everything:

You’re given:
- `∃ w, P w` — so there’s some `w` where `P w` holds
- `∀ w, P w → Q w` — so whenever `P w` is true, `Q w` is also true

From this, you want to prove:
```lean
∃ w, P w ∧ Q w
```
This means:
There’s some value of `w` where both `P w` and `Q w` are true.

Let’s do it!
"

Statement {α : Type} (P Q : α → Prop)
(h₁ : ∃ w, P w)
(h₂ : ∀ w, P w → Q w) :
∃ w, P w ∧ Q w := by
Hint "You are given `h₁ : ∃ w, P w`.

Use `cases h₁` to pull out the witness `w` and the proof `h : P w`."
cases h₁ with
| intro x hx =>
Hint "Now you have:
```lean
w : α

h : P x
and you know:

h₂ : ∀ w, P w → Q w
```
Apply `h₂ w` to get `Q w` using `have`."
have hq := h₂ x hx
Hint "Now you have both:
```lean
h : P w

hq : Q w
```
You can combine them like this:

`⟨h, hq⟩`

Then wrap that with the witness `w` as:

`⟨w, ⟨h, hq⟩⟩`
```"
exact ⟨x, ⟨hx, hq⟩⟩

Conclusion "
Amazing! 🎉

You just combined:
- An existential (`∃ w, P w`)
- A universal implication (`∀ w, P w → Q w`)
- Into a new existential with a conjunction: `∃ w, P w ∧ Q w`

This is the kind of reasoning that shows up in real math proofs, and you handled it perfectly.
"

end Predicate
