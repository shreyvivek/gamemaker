import GameServer.Commands
import Game.Levels.Propositional.L15_ReverseDeMorgan

namespace Propositional

World "Propositional"
Level 16
Title "Distributivity of ∧ over ∨"

Introduction "
In this level, we prove a fundamental logical identity:

> `(P ∧ (Q ∨ R)) ↔ (P ∧ Q) ∨ (P ∧ R)`

This is called **distributivity** — it shows how conjunction distributes over disjunction.

You’ll prove this *bidirectional* statement by:
- Using `constructor` to prove both directions of the equivalence
- Breaking down disjunctions using `cases`
- Building conjunctions and disjunctions using `constructor`, `left`, and `right`

This is the final level in this World. And we use several tactics to arrive at the result. You will be prompted with obvious hints as well - to ensure that you take away a good understanding of the several tactics and their uses.
"

Statement (P Q R : Prop) : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by
  Hint "Use `constructor` first — you're proving a ↔, so you need to prove two implications."
  constructor

  -- Forward direction: (P ∧ (Q ∨ R)) → (P ∧ Q) ∨ (P ∧ R)
  intro h
  Hint "You now have `h : P ∧ (Q ∨ R)`. Use `have hp := h.left` to extract the first part."
  have hp := h.left
  Hint "Then do `cases h.right with` to split the `(Q ∨ R)` into two cases."
  cases h.right with
  | inl hq =>
    Hint "Now you have `P` and `Q`. Use `left` to choose the left side of the ∨ goal, then use `constructor` to form `P ∧ Q`."
    left
    constructor
    exact hp
    exact hq
  | inr hr =>
    Hint "This case is similar — now `P` and `R` are both true. Use `right` and `constructor` to build `P ∧ R`."
    right
    constructor
    exact hp
    exact hr

  -- Reverse direction: (P ∧ Q) ∨ (P ∧ R) → (P ∧ (Q ∨ R))
  intro h
  Hint "To handle the ∨ on the left, use `cases h with` to handle each case separately."
  cases h with
  | inl hpq =>
    Hint "You now have `hpq : P ∧ Q`. Break it using `.left` and `.right`."
    constructor
    exact hpq.left
    left
    exact hpq.right
  | inr hpr =>
    Hint "Similarly, you now have `hpr : P ∧ R`. Use `constructor`, then `right` for the `Q ∨ R`."
    constructor
    exact hpr.left
    right
    exact hpr.right

Conclusion "
Beautiful!

You’ve now proven the **distributive law**:
`P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R)`

By carefully analyzing the structure of each side, and using basic building blocks like `cases`, `constructor`, `left`, and `right`, you've completed a foundational logical identity.

You'll use this reasoning in simplifying logical formulas, circuits, and more.

With that, we have come to the end of this World. Click on the Home button at the top to explore other worlds.
"

end Propositional
