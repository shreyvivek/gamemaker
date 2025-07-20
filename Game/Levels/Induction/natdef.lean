inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

-- Alias ℕ to MyNat
notation "ℕ" => MyNat

-- Define addition manually
def add : ℕ → ℕ → ℕ
  | zero, n => n
  | succ m, n => succ (add m n)

-- Provide HAdd instance so we can write n + m
instance : HAdd ℕ ℕ ℕ where
  hAdd := add

-- Rewrite lemmas for addition
@[simp] theorem add_zero (n : ℕ) : zero + n = n := by rfl
@[simp] theorem add_succ (m n : ℕ) : succ m + n = succ (m + n) := by rfl

-- Theorem: n + 0 = n
theorem add_right_zero (n : ℕ) : n + zero = n := by
  induction n with
  | zero =>
    -- Goal: zero + zero = zero
    rfl
  | succ k ih =>
    -- Goal: succ k + zero = succ k
    -- By definition: succ k + zero = succ (k + zero)
    -- Apply induction hypothesis: k + zero = k
    -- So: succ (k + zero) = succ k
    rw [add_succ, ih]

end MyNat
