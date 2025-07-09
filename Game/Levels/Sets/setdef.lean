namespace Sets

def Set (α : Type) := α → Prop

def Mem {α : Type} (x : α) (A : Set α) : Prop := A x
infix:50 " ∈ " => Mem

def Subset {α : Type} (A B : Set α) : Prop := ∀ x, x ∈ A → x ∈ B
infix:50 " ⊆ " => Subset

def Inter (A B : Set ℕ) : Set ℕ := fun x => x ∈ A ∧ x ∈ B
infix:70 " ∩ " => Inter

def Union (A B : Set ℕ) : Set ℕ := fun x => x ∈ A ∨ x ∈ B
infix:65 " ∪ " => Union

def Equal (A B : Set ℕ) : Prop := A ⊆ B ∧ B ⊆ A

end Sets
