import Mathlib

import Proofs.ReducibilityImplications

set_option maxHeartbeats 2000000

theorem CylinderGreatestFiniteOneDegree : (∀ A : _root_.Set _root_.Nat,
  let cyl : _root_.Set _root_.Nat :=
    {z | ∃ x n : _root_.Nat, x ∈ A ∧ z = _root_.Nat.pair x n}
  let finiteOneReducible (X Y : _root_.Set _root_.Nat) : Prop :=
    ∃ f : _root_.Nat → _root_.Nat, _root_.Computable f ∧
      (∀ y : _root_.Nat, _root_.Set.Finite (_root_.Set.preimage f ({y} : _root_.Set _root_.Nat))) ∧
      (∀ x : _root_.Nat, x ∈ X ↔ f x ∈ Y)
  _root_.ManyOneDegree.of cyl = _root_.ManyOneDegree.of A ∧
    (∀ B : _root_.Set _root_.Nat,
      _root_.ManyOneDegree.of B = _root_.ManyOneDegree.of A → finiteOneReducible B cyl)) :=
(by
  -- Cintioli, arXiv:2609.00419v1, §1, p. 1 and §2, pp. 2–3.
  -- The article-specific Alphabeta Math Research Portal and defect report
  -- both returned HTTP 404 on recheck.
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects
  -- Use verification step 1.1 of the shared-library item
  -- def-computable-many-one-reducibility-interface for composition of total
  -- Nat witnesses and their membership equivalences. Step 2.1 concerns
  -- canonical binary strings; the endpoint uses only Nat representatives.
  intro A cyl finiteOneReducible
  -- The pairing identities characterize membership via the first projection.
  have mem_cyl (z : Nat) : z ∈ cyl ↔ (Nat.unpair z).1 ∈ A := by
    change (∃ x n : Nat, x ∈ A ∧ z = Nat.pair x n) ↔ _
    constructor
    · rintro ⟨x, n, hx, rfl⟩
      simpa only [Nat.unpair_pair] using hx
    · intro hz
      exact ⟨(Nat.unpair z).1, (Nat.unpair z).2, hz, (Nat.pair_unpair z).symm⟩
  have mem_pair (x n : Nat) : Nat.pair x n ∈ cyl ↔ x ∈ A := by
    simpa only [Nat.unpair_pair] using mem_cyl (Nat.pair x n)
  -- The article's projection and zero-column maps give mutual many-one
  -- reducibility. Mathlib expresses their equivalence as equality of degrees.
  refine ⟨ManyOneDegree.of_eq_of.mpr ⟨?_, ?_⟩, ?_⟩
  · exact ⟨fun z => (Nat.unpair z).1,
      Computable.fst.comp Primrec.unpair.to_comp, mem_cyl⟩
  · exact ⟨fun x => Nat.pair x 0,
      Primrec₂.natPair.to_comp.comp Computable.id (Computable.const 0),
      fun x => (mem_pair x 0).symm⟩
  · intro B hDegree
    obtain ⟨f, hf, hfMem⟩ := (ManyOneDegree.of_eq_of.mp hDegree).1
    -- The second coordinate preserves the input, even when f has infinite fibres.
    have hOne : OneOneReducible (fun x : Nat => x ∈ B) (fun z : Nat => z ∈ cyl) := by
      refine ⟨fun x => Nat.pair (f x) x,
        Primrec₂.natPair.to_comp.comp hf Computable.id, ?_,
        fun x => (hfMem x).trans (mem_pair (f x) x).symm⟩
      intro x y h
      have hPair : Nat.pairEquiv (f x, x) = Nat.pairEquiv (f y, y) := h
      exact congrArg Prod.snd (Nat.pairEquiv.injective hPair)
    -- The reviewed endpoint compares representatives as in §2, p. 3.
    -- ReducibilityImplications supplies the finite fibres from injectivity.
    exact (ReducibilityImplications B cyl).1 hOne)
