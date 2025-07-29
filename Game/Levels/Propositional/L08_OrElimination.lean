import GameServer.Commands
import Game.Levels.Propositional.L07_ModusPonens
namespace Propositional

World "Propositional"
Level 8
Title "Or Elimination"

Introduction "
You might remember one such proof from lectures — **Dilemma**.

"
/--

---

Purpose: Use `cases` on a disjunction (e.g. `P ∨ Q`) to split it into two separate cases.

Each case creates a new assumption:
- `inl hp` means `P` is assumed true
- `inr hq` means `Q` is assumed true

📌 Think of it as:

“Let’s examine both possible scenarios and show that the goal works either way.”

---

### In Propositional Logic:

Given: `h : P ∨ Q`

After `cases h`:
- Case 1: `hp : P`
- Case 2: `hq : Q`

---

### In Predicate Logic:

You’re given:
- `P : ℕ → Prop`
- `h : ∃ x, P x`

And your goal is to use that `∃ x, P x` to reason further.

`cases h` will break apart the existential statement.
After this, you’ll have:

- `x : ℕ` — a specific witness
- `hx : P x` — proof that `P x` holds for this `x`.

You can now work with `x` and `hx` to prove your goal.

You can also use cases on a conjunction:

You’re given:

`h : P x ∧ Q x`

`cases h` will split the conjunction into two separate facts:

- `hP : P x`
- `hQ : Q x`

Now you can use either or both in your proof.

---

### In Sets:

Suppose:

`h : x ∈ A ∪ B` (i.e., `x ∈ A ∨ x ∈ B`)

Then:

After `cases h`:
- Case 1: `ha : x ∈ A`
- Case 2: `hb : x ∈ B`

---

-/
TacticDoc cases

Statement (P Q R : Prop) (hpq : P ∨ Q) (hpr : P → R) (hqr : Q → R) : R := by
  Hint "
  ---

**Given:**
- (1) `P ∨ Q`
- (2) `P → R`
- (3) `Q → R`

**To Prove:** `R`

---

**Proof (in natural language):**

We use disjunction elimination on `P ∨ Q`, i.e., we consider both cases separately:

---

- *Case 1:* Assume `P` is true.

  From (2), `P → R`, so `R` is true (Modus Ponens).

- *Case 2:* Assume `Q` is true.

  From (3), `Q → R`, so again `R` is true (Modus Ponens).

---

In both cases, `R` is true.

So regardless of whether `P` or `Q` is true, we conclude:

**`R` is true.**


Let us now try it in Lean. Also, `modus_ponens` as a `Theorem` is now unlocked under `Theorems` and can be found under the `Propositional` section.
  "
  Hint "Use the `cases` tactic to break the disjunction `hpq` into two cases: one - the `Active Goal` where `P` is true, and `Goal 2` - where `Q` is true."
  cases hpq with
  | inl h =>
    Hint "
In this case, `P` holds (`h : P`) and you also have `hpr : P → R`.

This matches the **Modus Ponens** pattern: if `P` is true and `P → R`, then `R` must be true.

Use the `exact` tactic to apply the implication, with `modus_ponens` like this : `exact modus_ponens hpr h`.

This tells Lean to use modus_ponens on `hpr` and `h₁`, resulting in `R`.

Do similarly for when `Q` is assumed to be true in `Goal 2`.
    "
    exact hpr h
  | inr h =>
    exact hqr h


NewTactic cases

NewTheorem Propositional.modus_ponens
Conclusion "
You’ve completed a textbook disjunction elimination! You can also see how versatile the `exact` tactic is.

By showing the goal holds in **both** branches of the `or`, you’ve logically proven it no matter what.
"

end Propositional
