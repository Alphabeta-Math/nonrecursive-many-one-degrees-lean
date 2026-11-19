import Mathlib
import Proofs.ProfileRealization
import Proofs.ComputablyEnumerableSet

set_option maxHeartbeats 2000000

theorem HomogeneousRowsFromCylinderReduction : (∀ (A P : _root_.Set _root_.Nat) (p : _root_.Nat → _root_.Nat),
  _root_.Computable p →
  _root_.Function.Surjective p →
  (∃ s : _root_.Nat → _root_.Nat,
    _root_.Computable s ∧ _root_.Function.RightInverse s p) →
  {y : _root_.Nat | _root_.Set.Infinite (_root_.Set.preimage p ({y} : _root_.Set _root_.Nat))} = P →
  let C := _root_.Set.preimage p A
  let cyl : _root_.Set _root_.Nat :=
    {z | ∃ x n : _root_.Nat, x ∈ A ∧ z = _root_.Nat.pair x n}
  ∀ h : _root_.Nat → _root_.Nat,
    _root_.Computable h →
    (∀ y : _root_.Nat, _root_.Set.Finite (_root_.Set.preimage h ({y} : _root_.Set _root_.Nat))) →
    (∀ z : _root_.Nat, z ∈ cyl ↔ h z ∈ C) →
    let encode : _root_.Nat → _root_.List _root_.Bool :=
      fun n => _root_.List.replicate n _root_.Bool.true
    let decode : _root_.List _root_.Bool → _root_.Option _root_.Nat :=
      fun w => if encode (_root_.List.length w) = w then
        _root_.Option.some (_root_.List.length w) else _root_.Option.none
    let uniformlyCE (W : _root_.Nat → _root_.Set _root_.Nat) : Prop :=
      _root_.ComputablyEnumerableSet encode decode
        (_root_.Function.LeftInverse.injective
          (show _root_.Function.LeftInverse _root_.List.length encode from
            fun _ => _root_.List.length_replicate))
        (fun n => by simp [decode, encode])
        (fun w hw => _root_.ite_eq_right (fun hEq => hw ⟨_root_.List.length w, hEq⟩))
        {z : _root_.Nat | ∃ x y : _root_.Nat, y ∈ W x ∧ z = _root_.Nat.pair x y}
    ∀ stage : _root_.Nat → _root_.Nat → _root_.Nat → _root_.Finset _root_.Nat,
      _root_.Computable (fun t : _root_.Nat × _root_.Nat × _root_.Nat =>
        (_root_.Equiv.symm _root_.Finset.equivBitIndices) (stage t.1 t.2.1 t.2.2)) →
      (∀ e x : _root_.Nat, _root_.Monotone (stage e x)) →
      let indexedRows (e x : _root_.Nat) : _root_.Set _root_.Nat :=
        {y | ∃ s : _root_.Nat, y ∈ stage e x s}
      (∀ W : _root_.Nat → _root_.Set _root_.Nat,
        uniformlyCE W → ∃ e : _root_.Nat, ∀ x : _root_.Nat, W x = indexedRows e x) →
      let V (x : _root_.Nat) : _root_.Set _root_.Nat :=
        _root_.Set.range (fun n : _root_.Nat => p (h (_root_.Nat.pair x n)))
      uniformlyCE V ∧
        (∃ e : _root_.Nat, ∀ x : _root_.Nat, V x = indexedRows e x) ∧
        (∀ x y : _root_.Nat, y ∈ V x → (y ∈ A ↔ x ∈ A))) :=
(by
  intro A P p hp _ _ _ C cyl h hh _ hReduction encode decode uniformlyCE stage _ _ indexedRows hIndex V
  -- Cintioli's proof of Theorem 5, §4, p. 11, fixes p and h before
  -- forming the rows. Lemma 1 (ProfileRealization) supplies p in the caller.
  -- Here p and its profile are hypotheses. The row argument uses the
  -- computability of p and h and the reduction's membership equivalence.
  -- https://arxiv.org/pdf/2609.00419v1#page=11
  -- The article passage is unnumbered. The corresponding Research Portal
  -- collection and defect report returned HTTP 404.
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects
  let pack (q : Nat × Nat) : Nat := Nat.pair q.1 (p (h (Nat.pair q.1 q.2)))
  let enumerate (k : Nat) : Nat := pack k.unpair
  let G : Set Nat := {z | ∃ x y, y ∈ V x ∧ z = Nat.pair x y}
  have hPair : Computable (fun q : Nat × Nat => Nat.pair q.1 q.2) :=
    Primrec₂.natPair.to_comp
  have hPack : Computable pack :=
    Primrec₂.natPair.to_comp.comp Computable.fst (hp.comp (hh.comp hPair))
  have hEnumerate : Computable enumerate :=
    hPack.comp Primrec.unpair.to_comp
  have hRange : Set.range enumerate = G := by
    ext z
    change (∃ k, enumerate k = z) ↔ ∃ x y, y ∈ V x ∧ z = Nat.pair x y
    constructor
    · rintro ⟨k, rfl⟩
      let q := k.unpair
      exact ⟨q.1, p (h (Nat.pair q.1 q.2)), ⟨q.2, rfl⟩, rfl⟩
    · rintro ⟨x, y, ⟨n, rfl⟩, rfl⟩
      have hUnpair : (Nat.pair x n).unpair = (x, n) :=
        Nat.pairEquiv.symm_apply_apply (x, n)
      exact ⟨Nat.pair x n, by simp only [enumerate, pack, hUnpair]⟩

  -- Alphabeta Math's recognizability equivalence, step 1.1, searches
  -- a total enumeration for equality with the input. The reviewed supplier
  -- implements this search on Nat. Step 2.1 uses shortlex words and a
  -- time bound. The supplier's Nat bridge searches coded inputs and fuel
  -- and expresses the result with the reviewed true-bit unary encoding.
  -- https://alphabetamath.cc/item/thm-recognizable-iff-enumerable
  have hRecognizer : REPred (fun z => z ∈ G) := by
    rw [← hRange]
    exact ComputablyEnumerableSet.nat_rePred_range hEnumerate
  have hCE : uniformlyCE V :=
    (ComputablyEnumerableSet.nat_rePred_iff true G).mp hRecognizer

  -- The assumed exhaustion of the stage enumeration applies to the whole
  -- coded graph, so the same index represents every row.
  refine ⟨hCE, hIndex V hCE, ?_⟩
  have hCylinder (x n : Nat) : Nat.pair x n ∈ cyl ↔ x ∈ A := by
    change (∃ u v : Nat, u ∈ A ∧ Nat.pair x n = Nat.pair u v) ↔ x ∈ A
    constructor
    · rintro ⟨u, v, hu, hEq⟩
      have huv : (x, n) = (u, v) := Nat.pairEquiv.injective hEq
      have hFirst : x = u := congrArg Prod.fst huv
      exact hFirst.symm ▸ hu
    · exact fun hx => ⟨x, n, hx, rfl⟩
  rintro x y ⟨n, rfl⟩
  exact (hReduction (Nat.pair x n)).symm.trans (hCylinder x n))

#print axioms HomogeneousRowsFromCylinderReduction
