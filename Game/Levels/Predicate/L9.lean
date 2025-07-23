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

cases h₁
have hPwtQw : P w → Q w := h₂ w
have hQw : Q w := modus_ponens hPwtQw h
exact Exists.intro w (And.intro h hQw)
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
