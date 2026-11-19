import Mathlib
import Proofs.PiTwoDescendingCePresentation
import Proofs.ComputableInjectiveSection
import Proofs.InfiniteCEInjectiveEnumeration
import Proofs.ArithmeticalHierarchyLevels
import Proofs.ComputablyEnumerableSet

set_option maxHeartbeats 2000000

theorem ProfileRealization : (∀ P : _root_.Set _root_.Nat,
  {xs : _root_.Fin 1 → _root_.Nat | xs 0 ∈ P} ∈
      (_root_.ArithmeticalHierarchyLevels 2 1 (_root_.Nat.le_succ 1)).2.1 →
    ∃ p : _root_.Nat → _root_.Nat,
      _root_.Computable p ∧ _root_.Function.Surjective p ∧
      {y : _root_.Nat | _root_.Set.Infinite (_root_.Set.preimage p ({y} : _root_.Set _root_.Nat))} = P ∧
      (∃ s : _root_.Nat → _root_.Nat,
        _root_.Computable s ∧ _root_.Function.RightInverse s p)) :=
(by
  classical
  intro P hP
  -- Cintioli, Lemma 1, §2, pp. 3–4, constructs a descending sequence and
  -- adds an unconditional level 0 to its packed graph.
  -- https://arxiv.org/pdf/2609.00419v1#page=3
  -- The article-specific Alphabeta Math portal and its defect report both
  -- returned HTTP 404.
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects
  -- The article proof is unnumbered. The verified library
  -- steps for the injective enumeration are cited at their application below.
  obtain ⟨Q, _, _, hG, hH0, hAnti, hPinter⟩ :=
    PiTwoDescendingCePresentation P hP
  let H (k : Nat) : Set Nat := {y | ∀ j < k, ∃ s, Q y j s}
  let G : Set Nat := {z | z.unpair.2 ∈ H z.unpair.1}
  let encode (n : Nat) : List Bool := List.replicate n false
  let decode (w : List Bool) : Option Nat :=
    if w = encode w.length then some w.length else none
  have hEncode : Function.Injective encode := List.replicate_left_injective false
  have hDecode (n : Nat) : decode (encode n) = some n := by
    simp [decode, encode]
  have hInvalid (w : List Bool) (hw : w ∉ Set.range encode) : decode w = none :=
    ite_eq_right (fun h => hw ⟨w.length, h.symm⟩)
  change ComputablyEnumerableSet encode decode hEncode hDecode hInvalid G at hG
  change H 0 = Set.univ at hH0
  change Antitone H at hAnti
  change P = ⋂ k, H k at hPinter
  have hGre : REPred (fun z => z ∈ G) :=
    (ComputablyEnumerableSet.nat_rePred_iff false G).mpr hG

  -- The article leaves the c.e. recombination implicit. A single
  -- computable preimage implements it. Both input levels 0 and 1
  -- map to level 0 of G, which contains every second coordinate.
  let shift (z : Nat) : Nat := Nat.pair z.unpair.1.pred z.unpair.2
  let R : Set Nat := {z | shift z ∈ G}
  have hFirst : Computable (fun z : Nat => z.unpair.1) :=
    Computable.fst.comp Primrec.unpair.to_comp
  have hSecond : Computable (fun z : Nat => z.unpair.2) :=
    Computable.snd.comp Primrec.unpair.to_comp
  have hShift : Computable shift :=
    Primrec₂.natPair.to_comp.comp (Primrec.pred.to_comp.comp hFirst) hSecond
  have hRre : REPred (fun z => z ∈ R) := by
    change Partrec (fun z : Nat => Part.assert (z ∈ G) (fun _ => Part.some ())) at hGre
    exact hGre.comp hShift
  have hRce : ComputablyEnumerableSet encode decode hEncode hDecode hInvalid R :=
    (ComputablyEnumerableSet.nat_rePred_iff false R).mp hRre
  have hRzero (y : Nat) : Nat.pair 0 y ∈ R := by
    simp [R, shift, G, Nat.unpair_pair, hH0]
  have hRsucc (k y : Nat) : Nat.pair (k + 1) y ∈ R ↔ y ∈ H k := by
    simp [R, shift, G, Nat.unpair_pair]
  have hPairRight (k : Nat) : Function.Injective (Nat.pair k) := by
    intro y z hyz
    exact congrArg Prod.snd (Nat.pairEquiv.injective (show
      Nat.pairEquiv (k, y) = Nat.pairEquiv (k, z) from hyz))
  have hPairLeft (y : Nat) : Function.Injective (fun k => Nat.pair k y) := by
    intro j k hjk
    exact congrArg Prod.fst (Nat.pairEquiv.injective (show
      Nat.pairEquiv (j, y) = Nat.pairEquiv (k, y) from hjk))
  have hRinf : R.Infinite :=
    (Set.infinite_range_of_injective (hPairRight 0)).mono (by
      rintro _ ⟨y, rfl⟩
      exact hRzero y)

  -- Alphabeta Math, thm-infinite-ce-sets-have-computable-injective-enumerations,
  -- steps 1.1, 2.1 and 3.1, scans distinct codewords, proves exact coverage,
  -- and uses infinitude for termination. The compiled supplier encapsulates
  -- these steps. Its computability conclusion is for the encoded outputs.
  -- Recover computability of r by taking the length of each false-bit codeword.
  -- https://alphabetamath.cc/item/thm-infinite-ce-sets-have-computable-injective-enumerations
  obtain ⟨r, hrCode, hrInj, hrRange⟩ :=
    InfiniteCEInjectiveEnumeration encode decode hEncode hDecode hInvalid R hRce hRinf
  have hr : Computable r :=
    (Computable.list_length.comp hrCode).of_eq (fun n => List.length_replicate)
  let p (n : Nat) : Nat := (r n).unpair.2
  have hp : Computable p := hSecond.comp hr
  have hpSurj : Function.Surjective p := by
    intro y
    have h := hRzero y
    rw [← hrRange] at h
    obtain ⟨n, hn⟩ := h
    exact ⟨n, by simp [p, hn, Nat.unpair_pair]⟩
  refine ⟨p, hp, hpSurj, ?_, ?_⟩
  · ext y
    -- The article counts fibres. Use the exact image under r to transport
    -- infinitude to the packed column and use a finite bound on its levels.
    let C : Set Nat := {z | z ∈ R ∧ z.unpair.2 = y}
    have hImage : r '' (p ⁻¹' ({y} : Set Nat)) = C := by
      ext z
      constructor
      · rintro ⟨n, hn, rfl⟩
        change r n ∈ R ∧ p n = y
        exact ⟨hrRange ▸ Set.mem_range_self n, Set.mem_singleton_iff.mp hn⟩
      · rintro ⟨hzR, hzy⟩
        rw [← hrRange] at hzR
        obtain ⟨n, rfl⟩ := hzR
        exact ⟨n, Set.mem_singleton_iff.mpr hzy, rfl⟩
    have hInf : C.Infinite ↔ (p ⁻¹' ({y} : Set Nat)).Infinite :=
      hImage ▸ Set.infinite_image_iff hrInj.injOn
    change (p ⁻¹' ({y} : Set Nat)).Infinite ↔ y ∈ P
    by_cases hy : y ∈ P
    · have hHy (k : Nat) : y ∈ H k :=
        Set.mem_iInter.mp (hPinter ▸ hy) k
      have hCinf : C.Infinite :=
        (Set.infinite_range_of_injective
          ((hPairLeft y).comp Nat.succ_injective)).mono (by
            rintro _ ⟨k, rfl⟩
            exact ⟨(hRsucc k y).mpr (hHy k), by simp [Nat.unpair_pair]⟩)
      exact iff_of_true (hInf.mp hCinf) hy
    · have hMiss : ∃ k, y ∉ H k := by
        apply not_forall.mp
        intro hAll
        exact hy (hPinter.symm ▸ Set.mem_iInter.mpr hAll)
      obtain ⟨k, hk⟩ := hMiss
      have hBound : C ⊆ (fun j => Nat.pair j y) '' Set.Iic k := by
        intro z hz
        obtain ⟨hzR, hzy⟩ := hz
        have hzPair : Nat.pair z.unpair.1 y = z := by
          rw [← hzy, Nat.pair_unpair]
        refine ⟨z.unpair.1, ?_, hzPair⟩
        change z.unpair.1 ≤ k
        cases hlevel : z.unpair.1 with
        | zero => exact Nat.zero_le k
        | succ j =>
          have hjy : y ∈ H j := (hRsucc j y).mp (by
            rw [hlevel] at hzPair
            simpa only [hzPair] using hzR)
          have hjk : j < k := lt_of_not_ge (fun hkj => hk (hAnti hkj hjy))
          exact Nat.succ_le_of_lt hjk
      have hCfin : C.Finite := ((Set.finite_Iic k).image _).subset hBound
      exact iff_of_false (fun hf => hInf.mpr hf hCfin) hy
  · -- Surjectivity discharges the reviewed least-preimage supplier's
    -- termination hypothesis. Its section equation is the right inverse.
    obtain ⟨s, hs, _, hRight, _⟩ := ComputableInjectiveSection p hp hpSurj
    exact ⟨s, hs, hRight⟩
)

#print axioms PiTwoDescendingCePresentation
#print axioms ComputableInjectiveSection
#print axioms InfiniteCEInjectiveEnumeration
#print axioms ArithmeticalHierarchyLevels
#print axioms ComputablyEnumerableSet
#print axioms ProfileRealization
