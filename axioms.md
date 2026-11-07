```#print Matrix.conjTranspose_apply

@[defeq] theorem Matrix.conjTranspose_apply.{v, u_2, u_3} : ∀ {m : Type u_2} {n : Type u_3} {α : Type v} [inst : Star α]
  (M : Matrix m n α) (i : m) (j : n), Mᴴ j i = star (M i j) :=
fun {m} {n} {α} [Star α] M i j => rfl
```

```
#print Matrix.transpose_apply

@[defeq] theorem Matrix.transpose_apply.{v, u_2, u_3} : ∀ {m : Type u_2} {n : Type u_3} {α : Type v} (M : Matrix m n α)
  (i : n) (j : m), Mᵀ i j = M j i :=
fun {m} {n} {α} M i j => rfl
```

```
#print Matrix.IsSymm

def Matrix.IsSymm.{u_1, u_3} : {α : Type u_1} → {n : Type u_3} → Matrix n n α → Prop :=
fun {α} {n} A => Aᵀ = A
```

```
#print Matrix.IsHermitian

def Matrix.IsHermitian.{u_1, u_4} : {α : Type u_1} → {n : Type u_4} → [Star α] → Matrix n n α → Prop :=
fun {α} {n} [Star α] A => Aᴴ = A
```