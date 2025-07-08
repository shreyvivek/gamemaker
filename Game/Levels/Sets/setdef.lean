def Set (α : Type) := α → Prop

def Mem {α : Type} (x : α) (A : Set α) : Prop := A x
infix:50 " ∈ " => Mem
