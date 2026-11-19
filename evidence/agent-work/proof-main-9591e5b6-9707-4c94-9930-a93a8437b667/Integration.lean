import Proofs.CofiniteDomainLemma

#print axioms CofiniteDomainLemma
#print axioms CofiniteDomainLemma.partrec_union

example (A : Set ℕ) {φ ψ : ℕ → Part ℕ} (hφ : Partrec φ) (hψ : Partrec ψ)
    (hφasc : ∀ x y, y ∈ φ x → x < y ∧ (y ∈ A ↔ x ∈ A))
    (hψasc : ∀ x y, y ∈ ψ x → x < y ∧ (y ∈ A ↔ x ∈ A)) :
    ∃ χ : ℕ → Part ℕ, Partrec χ ∧
      (∀ x, (χ x).Dom ↔ (φ x).Dom ∨ (ψ x).Dom) ∧
      (∀ x y, y ∈ χ x → x < y ∧ (y ∈ A ↔ x ∈ A)) := by
  obtain ⟨χ, hχ, hdom, hout⟩ := CofiniteDomainLemma.partrec_union hφ hψ
  exact ⟨χ, hχ, hdom, fun x y hy => (hout x y hy).elim (hφasc x y) (hψasc x y)⟩
