

def Set (α : Type) := α → Prop

def Mem {α : Type} (x : α) (A : Set α) : Prop := A x
infix:50 " ∈ " => Mem

def Subset {α : Type} (A B : Set α) : Prop := ∀ x, x ∈ A → x ∈ B
infix:50 " ⊆ " => Subset
