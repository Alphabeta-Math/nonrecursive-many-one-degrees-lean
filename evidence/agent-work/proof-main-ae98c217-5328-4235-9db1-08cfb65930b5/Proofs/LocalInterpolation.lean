import Mathlib
import Proofs.PriorityRequirements
import Proofs.ProfileRealization
import Proofs.PullbackReductions
import Proofs.HomogeneousRowsFromCylinderReduction
import Proofs.AscendingSelfReductionFromPullbackReduction
import Proofs.CylinderGreatestFiniteOneDegree
import Proofs.ComputablyEnumerableSet
import Proofs.HaltingSigmaOneCompleteness

set_option maxHeartbeats 2000000

theorem LocalInterpolation : (∀ A : _root_.Set _root_.Nat,
  let cyl : _root_.Set _root_.Nat :=
    {z | ∃ x n : _root_.Nat, x ∈ A ∧ z = _root_.Nat.pair x n}
  let encode (n : _root_.Nat) := _root_.List.replicate n _root_.Bool.true
  let decode (w : _root_.List _root_.Bool) : _root_.Option _root_.Nat :=
    if encode (_root_.List.length w) = w then _root_.Option.some (_root_.List.length w)
    else _root_.Option.none
  let ce : _root_.Set _root_.Nat → Prop :=
    _root_.ComputablyEnumerableSet encode decode
      (_root_.List.replicate_left_injective _root_.Bool.true)
      (fun n => by simp [decode, encode])
      (fun w hw => _root_.ite_eq_right (fun h => hw ⟨_root_.List.length w, h⟩))
  let finiteOneReducible (X Y : _root_.Set _root_.Nat) : Prop :=
    ∃ f : _root_.Nat → _root_.Nat, _root_.Computable f ∧
      (∀ y : _root_.Nat, _root_.Set.Finite (_root_.Set.preimage f ({y} : _root_.Set _root_.Nat))) ∧
      (∀ x : _root_.Nat, x ∈ X ↔ f x ∈ Y)
  let finiteOneStrict (X Y : _root_.Set _root_.Nat) : Prop :=
    finiteOneReducible X Y ∧ ¬ finiteOneReducible Y X
  ¬ _root_.ComputablePred (fun x : _root_.Nat => x ∈ A) →
  ¬ (_root_.OneOneReducible (fun x : _root_.Nat => x ∈ A) (fun x : _root_.Nat => x ∈ cyl) ∧
     _root_.OneOneReducible (fun x : _root_.Nat => x ∈ cyl) (fun x : _root_.Nat => x ∈ A)) →
  ¬ ce A →
  ¬ ce (Aᶜ) →
  ∃ C : _root_.Set _root_.Nat,
    _root_.ManyOneDegree.of C = _root_.ManyOneDegree.of A ∧
    finiteOneStrict A C ∧ finiteOneStrict C cyl) :=
(by
  classical
  intro A cyl encode decode ce finiteOneReducible finiteOneStrict hNonrec hNoncyl hNotCE hNotCoCE
  -- Cintioli, arXiv:2609.00419v1, §4, Theorem 5, pp. 8–12.
  -- https://arxiv.org/pdf/2609.00419v1#page=8
  -- The article's proof is unnumbered. The article-specific Alphabeta Math
  -- portal and its defect report both returned HTTP 404 on recheck.
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects
  let φ := HaltingSigmaOneCompleteness.canonicalNumbering
  let V := HaltingSigmaOneCompleteness.row
  let stage := HaltingSigmaOneCompleteness.rowAt
  obtain ⟨_, hSurj, hUniversal, _⟩ := HaltingSigmaOneCompleteness.canonicalNumbering_acceptable
  -- Alphabeta Math, thm-halting-is-sigma-one-complete, Step 1.1 uses
  -- recognizable domains of the universal evaluator. Precomposing it with
  -- the computable packing (e,x,y) ↦ (e,pair x y) gives the row graph.
  -- https://alphabetamath.cc/item/thm-halting-is-sigma-one-complete
  have hPacked : Computable (fun q : Nat × Nat × Nat => Nat.pair q.2.1 q.2.2) :=
    Primrec₂.natPair.to_comp.comp (Computable.fst.comp Computable.snd)
      (Computable.snd.comp Computable.snd)
  have hGraph : REPred (fun q : Nat × Nat × Nat => q.2.2 ∈ V q.1 q.2.1) :=
    (hUniversal.comp Computable.fst hPacked).dom_re
  have hStages (e x y : Nat) : y ∈ V e x ↔ ∃ s, y ∈ stage e x s :=
    HaltingSigmaOneCompleteness.mem_row_iff_exists_stage e x y
  have hCoverage (i : Nat) : ∃ e : Nat, ∀ x y : Nat,
      y ∈ V e x ↔ (φ i (Nat.pair x y)).Dom := by
    obtain ⟨e, he⟩ := HaltingSigmaOneCompleteness.rowAt_exhausts_numbering i
    exact ⟨e, fun x y => (hStages e x y).trans (he x y)⟩
  have hStageCode := HaltingSigmaOneCompleteness.computable_rowAt_code
  have hMonotone := HaltingSigmaOneCompleteness.monotone_rowAt
  obtain ⟨N, _, _, hPi, hRequirements⟩ :=
    PriorityRequirements φ V stage hUniversal hSurj hGraph hCoverage hStageCode hMonotone hStages
  have hForA := hRequirements A hNonrec hNoncyl hNotCE hNotCoCE

  let P : Set Nat := Nᶜ
  obtain ⟨p, hp, hpSurj, hProfile, s, hs, hSection⟩ := ProfileRealization P hPi
  let C : Set Nat := p ⁻¹' A
  -- Alphabeta Math, def-computable-many-one-reducibility-interface, Step 1.1
  -- checks membership through computable maps. The pullback and section
  -- supply the two maps on Nat. The reviewed endpoint states strictness by
  -- forward reducibility and exclusion of the reverse at representative level.
  -- https://alphabetamath.cc/item/def-computable-many-one-reducibility-interface
  obtain ⟨_, hAC, _, hDegree⟩ := PullbackReductions A P p s hp hpSurj hProfile hs hSection
  have hCCyl : finiteOneReducible C cyl := (CylinderGreatestFiniteOneDegree A).2 C hDegree
  refine ⟨C, hDegree, ⟨hAC, ?_⟩, ⟨hCCyl, ?_⟩⟩
  · -- The ascending map supplied by the least search is partial recursive
    -- and defined on every infinite p-fibre index. Use its unary code at L_e.
    rintro ⟨h, hh, hFibres, hMem⟩
    let f (y : Nat) : Part Nat :=
      Part.map h (Nat.rfind (fun u => Part.some (decide (p u = y ∧ y < h u))))
    obtain ⟨hf, hAsc, hDom⟩ :=
      AscendingSelfReductionFromPullbackReduction A P p h hp hpSurj ⟨s, hs, hSection⟩
        hProfile hh hFibres hMem
    obtain ⟨e, he⟩ := hSurj f hf
    change φ e = f at he
    have hOdd : (2 * e + 1) % 2 ≠ 0 := by omega
    have hIndex : (2 * e + 1) / 2 = e := by omega
    have hLower : (∀ x y : Nat, y ∈ φ e x → x < y ∧ (y ∈ A ↔ x ∈ A)) →
        ∃ m : Nat, m ∉ N ∪ {x : Nat | (φ e x).Dom} := by
      simpa only [hOdd, ite_false, hIndex] using hForA (2 * e + 1)
    obtain ⟨m, hm⟩ := hLower (by rw [he]; exact hAsc)
    have hmP : m ∈ P := fun hmN => hm (Or.inl hmN)
    have hmDom : (f m).Dom := hDom hmP
    exact hm (Or.inr (show (φ e m).Dom by rw [he]; exact hmDom))
  · -- A hypothetical cylinder reduction yields a uniformly c.e. family.
    -- Alphabeta Math, thm-recognizable-iff-enumerable, Steps 1.1 and 3.1
    -- let us use a recognizer for its packed graph. Here the bridge is for
    -- unary Boolean encodings of naturals. Canonical finite stages bound
    -- both the simulation fuel and the row coordinate, with one common code.
    -- https://alphabetamath.cc/item/thm-recognizable-iff-enumerable
    rintro ⟨h, hh, hFibres, hMem⟩
    have hExhaustion (W : Nat → Set Nat)
        (hCE : ce {z : Nat | ∃ x y : Nat, y ∈ W x ∧ z = Nat.pair x y}) :
        ∃ e : Nat, ∀ x : Nat, W x = {y : Nat | ∃ t, y ∈ stage e x t} := by
      let G : Set Nat := {z | ∃ x y : Nat, y ∈ W x ∧ z = Nat.pair x y}
      have hRE : REPred (fun z => z ∈ G) :=
        (ComputablyEnumerableSet.nat_rePred_iff true G).mpr hCE
      obtain ⟨e, he⟩ := HaltingSigmaOneCompleteness.exists_index_stages hRE
      refine ⟨e, fun x => Set.ext (fun y => ?_)⟩
      refine Iff.trans ?_ (he x y)
      constructor
      · intro hy
        exact ⟨x, y, hy, rfl⟩
      · rintro ⟨a, b, hb, hEq⟩
        have hPair : (x, y) = (a, b) := Nat.pairEquiv.injective hEq
        cases hPair
        exact hb
    obtain ⟨_, ⟨e, he⟩, hHom⟩ :=
      HomogeneousRowsFromCylinderReduction A P p hp hpSurj ⟨s, hs, hSection⟩
        hProfile h hh hFibres hMem stage hStageCode hMonotone hExhaustion
    have hRow (x : Nat) : Set.range (fun n : Nat => p (h (Nat.pair x n))) = V e x :=
      (he x).trans (Set.ext (fun y => (hStages e x y).symm))
    have hEven : (2 * e) % 2 = 0 := by omega
    have hIndex : (2 * e) / 2 = e := by omega
    have hUpper : (∀ x y : Nat, y ∈ V e x → (y ∈ A ↔ x ∈ A)) →
        ∃ x : Nat, (V e x).Finite ∧ V e x ⊆ N := by
      simpa only [hEven, ite_true, hIndex] using hForA (2 * e)
    obtain ⟨x, hFinite, hInN⟩ := hUpper (fun x y hy => by
      apply hHom x y
      change y ∈ Set.range (fun n : Nat => p (h (Nat.pair x n)))
      rwa [hRow x])
    -- The article uses a finite union of fibres and the infinite column.
    -- Two finite preimages express that obstruction. The p-fibre hypothesis
    -- is needed only over this selected row, since the row lies in N.
    have hPreP : (p ⁻¹' (V e x)).Finite := hFinite.preimage' (fun y hy => by
      by_contra hInfinite
      have hyProfile : y ∈ {y : Nat | (p ⁻¹' ({y} : Set Nat)).Infinite} := hInfinite
      have hyP : y ∈ P := hProfile ▸ hyProfile
      exact hyP (hInN hy))
    have hPreH : (h ⁻¹' (p ⁻¹' (V e x))).Finite :=
      hPreP.preimage' (fun y _ => hFibres y)
    have hColumn : (Set.range (Nat.pair x)).Infinite :=
      Set.infinite_range_of_injective (fun a b hab => by
        have hPair : (x, a) = (x, b) := Nat.pairEquiv.injective hab
        exact congrArg Prod.snd hPair)
    apply hColumn (hPreH.subset ?_)
    rintro _ ⟨n, rfl⟩
    change p (h (Nat.pair x n)) ∈ V e x
    rw [← hRow x]
    exact ⟨n, rfl⟩)
