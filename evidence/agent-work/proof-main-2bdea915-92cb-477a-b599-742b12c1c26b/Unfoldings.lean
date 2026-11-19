import ArithmeticalHierarchyLevels

#check @PrimrecRel
#check @Primrec.fin_app
#check @Primrec.fin_curry

example (A : Set (Fin 1 → Nat)) :
    A ∈ (ArithmeticalHierarchyLevels 1 1 (Nat.le_refl 1)).1 ↔
      ∃ R : (Fin 1 → Nat) → (Fin 1 → Nat) → Prop,
        PrimrecRel R ∧ ∀ xs : Fin 1 → Nat, xs ∈ A ↔
          ∃ a : Nat, R xs (Fin.cons a Fin.elim0) := Iff.rfl

example (A : Set (Fin 1 → Nat)) :
    A ∈ (ArithmeticalHierarchyLevels 2 1 (Nat.le_succ 1)).1 ↔
      ∃ R : (Fin 1 → Nat) → (Fin 2 → Nat) → Prop,
        PrimrecRel R ∧ ∀ xs : Fin 1 → Nat, xs ∈ A ↔
          ∃ a : Nat, ∀ b : Nat, R xs (Fin.cons a (Fin.cons b Fin.elim0)) := Iff.rfl

example (A : Set (Fin 1 → Nat)) :
    A ∈ (ArithmeticalHierarchyLevels 2 1 (Nat.le_succ 1)).2.1 ↔
      Aᶜ ∈ (ArithmeticalHierarchyLevels 2 1 (Nat.le_succ 1)).1 := Iff.rfl
