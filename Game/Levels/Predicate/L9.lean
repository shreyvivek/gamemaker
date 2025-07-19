import GameServer.Commands

namespace Predicate

World "Predicate"
Level 9
Title "Existential + Universal"

Introduction "
Let’s combine **existential** and **universal** logic with a conjunction.

You are given:

- `∃ w, P w` — There exists some `w` such that `P w` holds
- `∀ w, P w → Q w` — For all `w`, if `P w` holds, then `Q w` also holds

Your goal is to prove:

`∃ w, P w ∧ Q w` — There exists some `w` such that both `P w` and `Q w` are true.

We’ll do this using the constructors `And.intro` and `Exists.intro`.
"

/--
Constructs a proof of `P ∧ Q` given proofs of `P` and `Q`.
-/
TheoremDoc And.intro as "And.intro" in "Predicate"

Statement {α : Type} (P Q : α → Prop)
(h₁ : ∃ w, P w)
(h₂ : ∀ w, P w → Q w) :
∃ w, P w ∧ Q w := by
Hint "
Start by breaking down the existential `h₁`.

Use the `cases` tactic to extract a witness `w` and the fact `h : P w`:
```lean
cases h₁
```
"

cases h₁ with
| intro w h =>
Hint "
Now you have:

```lean
h : P w
h₂ : ∀ w, P w → Q w
```

So you can derive `Q w` by applying h₂ to w and h:

`have hq : Q w := h₂ w h`
"
have hq : Q w := h₂ w h
Hint "
Now construct the conjunction `P w ∧ Q w` using:
```lean
And.intro h hq
```
Then wrap it with the witness using:
```lean
Exists.intro w (And.intro h hq)
```
"
exact Exists.intro w (And.intro h hq)

NewTheorem And.intro
Conclusion "
Awesome! 🎉

You used:

cases to extract a witness from an existential

A universal implication to derive new information

`And.intro` to build a conjunction

`Exists.intro` to reintroduce the existential

These steps form a solid foundation for more advanced logic proofs ahead.
"

end Predicate
