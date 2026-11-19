∀ (X N : Set Nat), REPred (fun q : Nat => q ∈ X) →
  (RelativeComputabilityAndEnumerability X).2.1 N →
  {xs : Fin 1 → Nat | xs 0 ∈ N} ∈
    (ArithmeticalHierarchyLevels 2 1 (Nat.le_succ 1)).1
