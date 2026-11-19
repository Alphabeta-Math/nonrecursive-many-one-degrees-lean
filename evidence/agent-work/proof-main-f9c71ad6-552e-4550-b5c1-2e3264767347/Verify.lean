import HaltingSigmaOneCompleteness

open HaltingSigmaOneCompleteness

#check HaltingSigmaOneCompleteness canonicalNumbering canonicalNumbering_acceptable

example : ∃ (φ : ℕ → ℕ → Part ℕ) (stage : ℕ → ℕ → ℕ → Finset ℕ),
    AcceptableNumbering φ ∧
    Computable (fun p : ℕ × ℕ × ℕ => Finset.equivBitIndices.symm (stage p.1 p.2.1 p.2.2)) ∧
    (∀ e x, Monotone (stage e x)) ∧
    (∀ i, ∃ e, ∀ x y, (∃ s, y ∈ stage e x s) ↔ (φ i (Nat.pair x y)).Dom) :=
  ⟨canonicalNumbering, rowAt, canonicalNumbering_acceptable, computable_rowAt_code,
    monotone_rowAt, rowAt_exhausts_numbering⟩

#print axioms HaltingSigmaOneCompleteness
#print axioms canonicalNumbering_acceptable
#print axioms computable_rowAt_code
#print axioms monotone_rowAt
#print axioms mem_row_iff_exists_stage
#print axioms rowAt_exhausts_numbering
#print axioms exists_index_stages
