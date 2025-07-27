import GameServer.Commands
import Game.Levels.Propositional.L07_ModusPonens

open Propositional

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

Hint "We want to extract a specific witness from the existential statement `h₁`.

Use `cases h₁` to pull out:

a value `w : α`

and a proof `h : P w`"
cases h₁

Hint "From `h₂ : ∀ w, P w → Q w`, you can specialize it to the specific `w` using:

`have hPwtQw : P w → Q w := h₂ w`
This gives you a conditional statement just for this particular `w`."

have hPwtQw : P w → Q w := h₂ w

Hint "Now apply Modus Ponens.

You have:

`P w → Q w` as `hPwtQw`

`P w` as `h`

So you can deduce `Q w` as `hQw` with the `have` tactic."

have hQw : Q w := modus_ponens hPwtQw h

Hint "Now you have both `P w` and `Q w`.

You can combine them using `And.intro h hQw` to get `P w ∧ Q w`.

Then use `Exists.intro w (...)` to finish the proof:
```lean
exact Exists.intro w (And.intro h hQw)
```"

exact Exists.intro w (And.intro h hQw)

NewTheorem And.intro
Conclusion "
Awesome! 🎉

You used:

`cases` to extract a witness from an existential

A universal implication to derive new information

`And.intro` to build a conjunction

`Exists.intro` to reintroduce the existential

These steps form a solid foundation for more advanced logic proofs ahead.
"

end Predicate
