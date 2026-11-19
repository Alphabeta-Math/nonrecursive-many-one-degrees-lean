import Mathlib

import Proofs.ProfileRealization
import Proofs.ReducibilityImplications
import Proofs.ManyOneReducibilityOnNat

set_option maxHeartbeats 2000000

theorem PullbackReductions : (∀ (A P : _root_.Set _root_.Nat) (p s : _root_.Nat → _root_.Nat),
  _root_.Computable p →
  _root_.Function.Surjective p →
  {y : _root_.Nat | _root_.Set.Infinite (_root_.Set.preimage p ({y} : _root_.Set _root_.Nat))} = P →
  _root_.Computable s →
  _root_.Function.RightInverse s p →
  let C : _root_.Set _root_.Nat := _root_.Set.preimage p A
  let finiteOneReducible : Prop :=
    ∃ f : _root_.Nat → _root_.Nat, _root_.Computable f ∧
      (∀ y : _root_.Nat, _root_.Set.Finite (_root_.Set.preimage f ({y} : _root_.Set _root_.Nat))) ∧
      (∀ x : _root_.Nat, x ∈ A ↔ f x ∈ C)
  _root_.OneOneReducible (fun x : _root_.Nat => x ∈ A) (fun x : _root_.Nat => x ∈ C) ∧
    finiteOneReducible ∧ _root_.ManyOneReducibilityOnNat C A ∧
    _root_.ManyOneDegree.of C = _root_.ManyOneDegree.of A) :=
(by
  -- Cintioli, arXiv:2609.00419v1, §4, proof of Theorem 5, p. 11.
  -- The article obtains p and s from Lemma 1 (ProfileRealization). This
  -- endpoint supplies them as hypotheses. The profile and surjectivity are
  -- used in the surrounding construction. The right-inverse equation
  -- suffices for membership preservation and injectivity of the section.
  -- The article-specific Alphabeta Math portal and its defect report both
  -- returned HTTP 404. The shared-library item below supplies verification
  -- step 1.1 for the computable-map membership calculation on Nat.
  intro A _P p s hp _hpSurj _hProfile hs hSection
  let C : Set Nat := Set.preimage p A
  -- Alphabeta Math, def-computable-many-one-reducibility-interface, step 1.1
  -- checks the membership equivalence for computable witnesses. Here the
  -- equation p (s y) = y gives that equivalence and the extra injectivity
  -- needed for one-one reducibility. Step 2.1 concerns string encodings.
  have hOne : OneOneReducible (fun x : Nat => x ∈ A) (fun x : Nat => x ∈ C) := by
    refine ⟨s, hs, hSection.injective, ?_⟩
    intro y
    change y ∈ A ↔ p (s y) ∈ A
    rw [hSection y]
  have hFinite := (ReducibilityImplications A C).1 hOne
  have hAC := (ReducibilityImplications A C).2 hFinite
  -- Pullback membership is definitionally membership of the image under p.
  have hCA : ManyOneReducibilityOnNat C A := by
    unfold ManyOneReducibilityOnNat
    exact ⟨p, hp, fun _ => Iff.rfl⟩
  exact ⟨hOne, hFinite, hCA, (ManyOneDegree.of_eq_of (p := C) (q := A)).2 ⟨hCA, hAC⟩⟩)
