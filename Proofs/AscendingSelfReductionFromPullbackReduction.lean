import Mathlib

import Proofs.ProfileRealization

set_option maxHeartbeats 2000000

theorem AscendingSelfReductionFromPullbackReduction : (∀ (A P : _root_.Set _root_.Nat) (p h : _root_.Nat → _root_.Nat),
  _root_.Computable p →
  _root_.Function.Surjective p →
  (∃ s : _root_.Nat → _root_.Nat,
    _root_.Computable s ∧ _root_.Function.RightInverse s p) →
  {y : _root_.Nat | _root_.Set.Infinite (_root_.Set.preimage p ({y} : _root_.Set _root_.Nat))} = P →
  let C : _root_.Set _root_.Nat := _root_.Set.preimage p A
  _root_.Computable h →
  (∀ z : _root_.Nat, _root_.Set.Finite (_root_.Set.preimage h ({z} : _root_.Set _root_.Nat))) →
  (∀ u : _root_.Nat, u ∈ C ↔ h u ∈ A) →
  let f_h : _root_.Nat → _root_.Part _root_.Nat := fun y =>
    _root_.Part.map h
      (_root_.Nat.rfind (fun u => _root_.Part.some (_root_.Decidable.decide (p u = y ∧ y < h u))))
  _root_.Partrec f_h ∧
  (∀ y z : _root_.Nat, z ∈ f_h y → y < z ∧ (z ∈ A ↔ y ∈ A)) ∧
  P ⊆ {y : _root_.Nat | _root_.Part.Dom (f_h y)}) :=
(by
  intro A P p h hp _hpSurj _hSection hProfile C hh hFibres hReduction f_h
  -- Cintioli, arXiv:2609.00419v1, §4, proof of Theorem 5, pp. 11–12.
  -- Lemma 1 (ProfileRealization) gives a computable surjection, a section
  -- and the prescribed profile when the caller supplies a Pi-2 set P.
  -- Here those data are inputs. The search uses computability and the
  -- profile equation. Surjectivity and the section serve the caller.
  -- https://arxiv.org/pdf/2609.00419v1#page=12
  -- This passage has no numbered steps. The article-specific Alphabeta Math
  -- Research Portal and its defect report both returned HTTP 404.
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects
  --
  -- Alphabeta Math's recognizability equivalence, step 1.1, tests the
  -- values of a total enumerator in index order. Here the tests are on
  -- naturals and include the inequality y < h u. On success the search
  -- returns the least admissible index, which we send through h.
  -- https://alphabetamath.cc/item/thm-recognizable-iff-enumerable
  let test (y u : Nat) : Part Bool :=
    Part.some (decide (p u = y ∧ y < h u))
  have hEq : Computable (fun q : Nat × Nat => decide (p q.2 = q.1)) :=
    Primrec.eq.decide.to_comp.comp (hp.comp Computable.snd) Computable.fst
  have hLt : Computable (fun q : Nat × Nat => decide (q.1 < h q.2)) :=
    Primrec.nat_lt.decide.to_comp.comp Computable.fst (hh.comp Computable.snd)
  have hTest : Computable (fun q : Nat × Nat => decide (p q.2 = q.1 ∧ q.1 < h q.2)) := by
    simpa only [Bool.decide_and] using Primrec.and.to_comp.comp hEq hLt
  have hSearch : Partrec (fun y => Nat.rfind (test y)) :=
    Partrec.rfind hTest.partrec
  refine ⟨Partrec.map (g := fun _ u => h u) hSearch (hh.comp Computable.snd), ?_, ?_⟩
  · intro y z hz
    change z ∈ Part.map h (Nat.rfind (test y)) at hz
    obtain ⟨u, hu, rfl⟩ := (Part.mem_map_iff h).mp hz
    have hPass := (Nat.mem_rfind.mp hu).1
    change true ∈ Part.some (decide (p u = y ∧ y < h u)) at hPass
    obtain ⟨hpu, hyu⟩ := of_decide_eq_true (Part.mem_some_iff.mp hPass).symm
    -- Step 1.1 of Alphabeta Math's many-one interface chains pointwise
    -- membership equivalences. Here the reduction gives the equivalence
    -- in reverse, and p u = y identifies the pullback membership.
    -- https://alphabetamath.cc/item/def-computable-many-one-reducibility-interface
    refine ⟨hyu, ?_⟩
    have hMem := (hReduction u).symm
    change h u ∈ A ↔ p u ∈ A at hMem
    simpa only [hpu] using hMem
  · intro y hy
    have hInfinite : (p ⁻¹' ({y} : Set Nat)).Infinite := by
      rw [← hProfile] at hy
      exact hy
    -- The finite initial interval has a finite pullback along h. The
    -- infinite fibre of p therefore meets the complement of this pullback.
    have hFinite : (h ⁻¹' Set.Iic y).Finite :=
      (Set.finite_Iic y).preimage' (fun z _ => hFibres z)
    have hNotSubset : ¬ (p ⁻¹' ({y} : Set Nat)) ⊆ h ⁻¹' Set.Iic y :=
      fun hSub => hInfinite (hFinite.subset hSub)
    obtain ⟨u, hu, hOut⟩ := Set.not_subset.mp hNotSubset
    have hpu : p u = y := Set.mem_singleton_iff.mp hu
    have hyu : y < h u := lt_of_not_ge hOut
    change (Nat.rfind (test y)).Dom
    refine Nat.rfind_dom.mpr ⟨u, ?_, ?_⟩
    · simp [test, hpu, hyu]
    · intro m _
      exact trivial)
