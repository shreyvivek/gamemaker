namespace Induction

inductive ℕ : Type
| zero : ℕ
| succ : ℕ → ℕ
deriving Repr

open ℕ

-- Define zero and succ notation
notation "zero" => ℕ.zero
notation "succ " n => ℕ.succ n

-- Define addition
def add : ℕ → ℕ → ℕ
| zero, m => m
| succ n, m => succ (add n m)

-- Allow use of `+`
instance : HAdd ℕ ℕ ℕ where
  hAdd := add

-- Define custom equality
def Equal (a b : ℕ) : Prop := ∀ P : ℕ → Prop, P a → P b
infix:50 " ≡ " => Equal

end Induction
