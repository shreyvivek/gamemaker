import GameServer.Commands

namespace Predicate

World "Predicate"
Level 8
Title "A Counterexample Exists"

Introduction "
Let’s try something easier — and more concrete!

Suppose we know that `P(a)` is **not true**.

Then we can conclude:
> “There exists some x for which `P(x)` is not true.”

In logic:
```lean
h : ¬ P a
⊢ ∃ x, ¬ P x
```

We’re simply providing a specific example (a counterexample!) to prove an existential statement.

Let’s try it!
"

Statement {α : Type} (P : α → Prop) (a : α) (h : ¬ P a) : ∃ x, ¬ P x := by
Hint "Your goal is to prove `∃ x, ¬ P x`.

You already know a specific `a` where `P a` is not true — it’s given by `h`.

So you can just provide `a` as the witness, and `h` as the proof.
```lean
exact ⟨a, h⟩
```"
exact ⟨a, h⟩

Conclusion "
Perfect! 🎉

You just gave a **counterexample** to the statement `∀ x, P x`.

You showed that:
```lean
P a is false ⇒ ∃ x, P x is false
```
This is one of the cleanest uses of existential introduction — and a very common pattern in proofs!

It might just be a one line proof, but again, we're going step by step to make sure that your understanding is complete.
"
end Predicate
