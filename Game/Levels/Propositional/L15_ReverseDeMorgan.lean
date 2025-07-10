import GameServer.Commands
import Game.Levels.Propositional.L14_DeMorgan

namespace Propositional

World "Propositional"
Level 15
Title "Negation of a Disjunction (←)"

Introduction "
Time to prove the **converse** of the previous level!

You're given `¬P ∧ ¬Q`, and need to prove `¬(P ∨ Q)`.

That is: if both `P` and `Q` are false, then the disjunction `P ∨ Q` is also false.

Strategy:
- Use `intro` to assume `P ∨ Q` is true (for contradiction)
- Use `cases` to consider each case: `P` or `Q`
- In each case, derive a contradiction using `¬P` or `¬Q`
"

Statement (P Q : Prop) (h : ¬P ∧ ¬Q) : ¬(P ∨ Q) := by
  Hint "Use `intro` first and then `cases`. It should be doable."
  intro hpq
  cases hpq with
  | inl hp =>
    exact h.left hp
  | inr hq =>
    exact h.right hq

Conclusion "
Great work!

You’ve now proven **both directions** of this classic equivalence:

- `¬(P ∨ Q) → ¬P ∧ ¬Q` (Level 14)
- `¬P ∧ ¬Q → ¬(P ∨ Q)` (Level 15)

Together, they form **De Morgan’s Law**:
`¬(P ∨ Q) ↔ ¬P ∧ ¬Q`

This logical identity is used constantly in proofs, programming, and logic design!
"

end Propositional
