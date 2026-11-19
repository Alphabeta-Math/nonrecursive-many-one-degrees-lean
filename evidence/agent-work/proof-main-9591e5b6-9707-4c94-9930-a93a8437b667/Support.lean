/-- Race two partial computable maps. The domain is their union, and every
    returned value is an output of one of the two maps at the same input. -/
theorem CofiniteDomainLemma.partrec_union
    {φ ψ : ℕ → Part ℕ} (hφ : Partrec φ) (hψ : Partrec ψ) :
    ∃ χ : ℕ → Part ℕ, Partrec χ ∧
      (∀ x, (χ x).Dom ↔ (φ x).Dom ∨ (ψ x).Dom) ∧
      (∀ x y, y ∈ χ x → y ∈ φ x ∨ y ∈ ψ x) := by
  -- For the c.e. branch, the coordinator asks for the bounded-code race.
  -- Nat.Partrec.merge' already implements it: at each fuel, try both codes
  -- with left priority at equal fuel, then use rfindOpt for the first success.
  -- Its soundness and completeness give both clauses even when the maps
  -- return different values on their common domain.
  obtain ⟨χ, hχ, hspec⟩ :=
    Nat.Partrec.merge' (Partrec.nat_iff.mp hφ) (Partrec.nat_iff.mp hψ)
  exact ⟨χ, Partrec.nat_iff.mpr hχ, fun x => (hspec x).2,
    fun x => (hspec x).1⟩
