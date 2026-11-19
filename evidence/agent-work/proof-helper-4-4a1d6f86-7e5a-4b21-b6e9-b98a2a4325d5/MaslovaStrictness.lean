import Proofs.PriorityRequirements
import Proofs.ProfileRealization
import Proofs.PullbackReductions
import Proofs.HomogeneousRowsFromCylinderReduction
import Proofs.AscendingSelfReductionFromPullbackReduction
import Proofs.CylinderGreatestFiniteOneDegree
import Proofs.HaltingSigmaOneCompleteness

open ReducibilityImplications

set_option maxHeartbeats 2000000

namespace MaslovaStrictness

local notation "φ" => HaltingSigmaOneCompleteness.canonicalNumbering
local notation "V" => HaltingSigmaOneCompleteness.row
local notation "stage" => HaltingSigmaOneCompleteness.rowAt

def cylinder (A : Set Nat) : Set Nat :=
  {z | ∃ x n : Nat, x ∈ A ∧ z = Nat.pair x n}

theorem advancingOnCE (A : Set Nat) (hA : REPred (fun n => n ∈ A))
    (hNonrec : ¬ ComputablePred (fun n => n ∈ A)) :
    ∃ g : Nat → Part Nat, Partrec g ∧
      (∀ n, (g n).Dom ↔ n ∈ A) ∧
      (∀ x y, y ∈ g x → x < y ∧ (y ∈ A ↔ x ∈ A)) := by
  classical
  have hInf : A.Infinite := by
    intro hFin
    let L := hFin.toFinset.toList
    have hRel : PrimrecRel (fun (xs : List Nat) (x : Nat) => x ∈ xs) :=
      (PrimrecRel.exists_mem_list (R := @Eq Nat) Primrec.eq).of_eq (by
        intro xs x
        simp)
    exact hNonrec
      (((hRel.decide.to_comp.comp (Computable.const L) Computable.id).computablePred).of_eq
        (fun x => Finset.mem_toList.trans hFin.mem_toFinset))
  obtain ⟨enum, hEnum, hRange⟩ :=
    ComputablyEnumerableSet.nat_exists_computable_range hA hInf.nonempty
  let test (x i : Nat) : Option Nat := bif decide (x < enum i) then some (enum i) else none
  have hTest : Computable₂ test :=
    (Computable.cond
      (Primrec.nat_lt.decide.to_comp.comp Computable.fst (hEnum.comp Computable.snd))
      ((Computable.option_some.comp (hEnum.comp Computable.snd)))
      (Computable.const (none : Option Nat))).to₂
  have hAdvance := Partrec.rfindOpt hTest
  let g (x : Nat) : Part Nat :=
    (Part.assert (x ∈ A) (fun _ => Part.some ())).bind
      (fun _ => Nat.rfindOpt (test x))
  have hg : Partrec g :=
    Partrec.bind hA (hAdvance.comp Computable.fst).to₂
  have hGood (x y : Nat) (hy : y ∈ g x) : x ∈ A ∧ x < y ∧ y ∈ A := by
    dsimp only [g] at hy
    rw [Part.mem_bind_iff] at hy
    obtain ⟨u, hu, hy⟩ := hy
    have hx := (Part.mem_assert_iff.mp hu).1
    obtain ⟨i, hi⟩ := Nat.rfindOpt_spec hy
    by_cases hlt : x < enum i
    · have hyEq : enum i = y := by simpa [test, hlt, Option.mem_def] using hi
      exact ⟨hx, hyEq ▸ hlt, hyEq ▸ (hRange ▸ Set.mem_range_self i)⟩
    · simp [test, hlt, Option.mem_def] at hi
  refine ⟨g, hg, fun x => ⟨?_, ?_⟩, fun x y hy => ?_⟩
  · intro hd
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hd
    exact (hGood x y hy).1
  · intro hx
    obtain ⟨y, hy, hxy⟩ := hInf.exists_gt x
    rw [← hRange] at hy
    obtain ⟨i, rfl⟩ := hy
    have hd : (Nat.rfindOpt (test x)).Dom :=
      Nat.rfindOpt_dom.mpr ⟨i, enum i, by simp [test, hxy, Option.mem_def]⟩
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hd
    exact Part.dom_iff_mem.mpr
      ⟨y, Part.mem_bind_iff.mpr ⟨(), by simp [Part.assert_pos hx], hy⟩⟩
  · obtain ⟨hx, hlt, hyA⟩ := hGood x y hy
    exact ⟨hlt, iff_of_true hyA hx⟩

theorem strictPullback (A : Set Nat)
    (hA : REPred (fun n => n ∈ A))
    (hNonrec : ¬ ComputablePred (fun n => n ∈ A))
    (hNoncyl : ¬ (OneOneReducible (fun n => n ∈ A) (fun n => n ∈ cylinder A) ∧
      OneOneReducible (fun n => n ∈ cylinder A) (fun n => n ∈ A)))
    (T : PriorityRequirements.VerificationTrace φ stage Aᶜ)
    (hSigma : {xs : Fin 1 → Nat | xs 0 ∈ T.output} ∈
      (ArithmeticalHierarchyLevels 2 1 (Nat.le_succ 1)).1) :
    ∃ C : Set Nat, ManyOneDegree.of C = ManyOneDegree.of A ∧
      FiniteOneReducible A C ∧ ¬ FiniteOneReducible C A ∧
      FiniteOneReducible C (cylinder A) ∧ ¬ FiniteOneReducible (cylinder A) C := by
  classical
  let P : Set Nat := T.outputᶜ
  have hPi : {xs : Fin 1 → Nat | xs 0 ∈ P} ∈
      (ArithmeticalHierarchyLevels 2 1 (Nat.le_succ 1)).2.1 := by
    change ({xs : Fin 1 → Nat | xs 0 ∈ T.output}ᶜᶜ : Set (Fin 1 → Nat)) ∈
      (ArithmeticalHierarchyLevels 2 1 (Nat.le_succ 1)).1
    simpa using hSigma
  obtain ⟨p, hp, hSurjP, hProfile, s, hs, hSection⟩ := ProfileRealization P hPi
  let C : Set Nat := p ⁻¹' A
  obtain ⟨_, hAC, _, hDegree⟩ :=
    PullbackReductions A P p s hp hSurjP hProfile hs hSection
  have hCyl := (CylinderGreatestFiniteOneDegree A).2 C hDegree
  obtain ⟨_, hSurj, hUniversal, _⟩ :=
    HaltingSigmaOneCompleteness.canonicalNumbering_acceptable
  refine ⟨C, hDegree, hAC, ?_, hCyl, ?_⟩
  · rintro ⟨h, hh, hFibres, hMem⟩
    let f (y : Nat) : Part Nat :=
      Part.map h (Nat.rfind (fun u => Part.some (decide (p u = y ∧ y < h u))))
    have hfSpec : Partrec f ∧
        (∀ y z : Nat, z ∈ f y → y < z ∧ (z ∈ A ↔ y ∈ A)) ∧
        P ⊆ {y | (f y).Dom} :=
      AscendingSelfReductionFromPullbackReduction A P p h hp hSurjP ⟨s, hs, hSection⟩
        hProfile hh hFibres hMem
    obtain ⟨hf, hAsc, hDom⟩ := hfSpec
    obtain ⟨e, he⟩ := hSurj f hf
    obtain ⟨g, hg, hDomG, hAscG⟩ := advancingOnCE A hA hNonrec
    obtain ⟨race, hRace, hDomRace, hOutRace⟩ := CofiniteDomainLemma.partrec_union hf hg
    have hInf := CofiniteDomainLemma A race hNonrec hNoncyl hRace (fun x y hy =>
      (hOutRace x y hy).elim (hAsc x y) (hAscG x y))
    obtain ⟨m, _, hmN, hmDom⟩ := T.lower_met e (fun b => by
      obtain ⟨m, hm, hbm⟩ := hInf.exists_gt b
      change ¬ (race m).Dom at hm
      rw [hDomRace] at hm
      refine ⟨m, hbm, fun hmA => hm (Or.inr ((hDomG m).mpr hmA)), ?_⟩
      rw [he]
      exact fun hmf => hm (Or.inl hmf))
    exact hmDom (he ▸ hDom hmN)
  · rintro ⟨h, hh, hFibres, hMem⟩
    have hExhaust (W : Nat → Set Nat)
        (hCE : {z : Nat | ∃ x y : Nat, y ∈ W x ∧ z = Nat.pair x y} = ∅ ∨
          ∃ enum : Nat → Nat, Computable (fun n => List.replicate (enum n) true) ∧
            Set.range enum = {z : Nat | ∃ x y : Nat, y ∈ W x ∧ z = Nat.pair x y}) :
        ∃ e : Nat, ∀ x : Nat, W x = {y : Nat | ∃ t, y ∈ stage e x t} := by
      let G : Set Nat := {z | ∃ x y : Nat, y ∈ W x ∧ z = Nat.pair x y}
      have hRE := (ComputablyEnumerableSet.nat_rePred_iff true G).mpr hCE
      obtain ⟨e, he⟩ := HaltingSigmaOneCompleteness.exists_index_stages hRE
      refine ⟨e, fun x => Set.ext (fun y => Iff.trans ?_ (he x y))⟩
      constructor
      · exact fun hy => ⟨x, y, hy, rfl⟩
      · rintro ⟨a, b, hb, hab⟩
        obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp hab
        exact hb
    obtain ⟨_, ⟨e, he⟩, hHom⟩ :=
      HomogeneousRowsFromCylinderReduction A P p hp hSurjP ⟨s, hs, hSection⟩
        hProfile h hh hFibres hMem stage
        HaltingSigmaOneCompleteness.computable_rowAt_code
        HaltingSigmaOneCompleteness.monotone_rowAt hExhaust
    have hRow (x : Nat) : Set.range (fun n : Nat => p (h (Nat.pair x n))) = V e x :=
      (he x).trans (Set.ext (fun y =>
        (HaltingSigmaOneCompleteness.mem_row_iff_exists_stage e x y).symm))
    have hPacked : Computable (fun q : Nat × Nat × Nat => Nat.pair q.2.1 q.2.2) :=
      Primrec₂.natPair.to_comp.comp (Computable.fst.comp Computable.snd)
        (Computable.snd.comp Computable.snd)
    have hGraph : REPred (fun q : Nat × Nat × Nat => q.2.2 ∈ V q.1 q.2.1) :=
      (hUniversal.comp Computable.fst hPacked).dom_re
    have hCoCE : ¬ REPred (fun x => x ∈ Aᶜ) := fun h =>
      hNonrec (ComputablePred.computable_iff_re_compl_re'.mpr ⟨hA, h⟩)
    have hHomV (x y : Nat) (hy : y ∈ V e x) : y ∈ A ↔ x ∈ A :=
      hHom x y (by
        change y ∈ Set.range (fun n : Nat => p (h (Nat.pair x n)))
        rwa [hRow x])
    obtain ⟨x, hFinite, hInN⟩ :=
      T.upper_met V HaltingSigmaOneCompleteness.monotone_rowAt
        HaltingSigmaOneCompleteness.mem_row_iff_exists_stage e (fun Z hZ hZA =>
          FiniteMarkerAvoidance.of_nonCE_marker_colors A (V e) hNoncyl
            ((ComputablyEnumerableSet.nat_rePred_iff true _).mp
              (PriorityRequirements.rowGraphRE hGraph e))
            hHomV Z hZ (fun z hz =>
              ⟨fun hzA => False.elim ((hZA hz) hzA),
                fun _ h => hCoCE ((ComputablyEnumerableSet.nat_rePred_iff true _).mpr h)⟩))
    have hPreP : (p ⁻¹' (V e x)).Finite := hFinite.preimage' (fun y hy => by
      by_contra hInf
      have hyP : y ∈ P :=
        hProfile ▸ (show y ∈ {z : Nat | (p ⁻¹' ({z} : Set Nat)).Infinite} from hInf)
      exact hyP (hInN hy))
    have hPreH : (h ⁻¹' (p ⁻¹' (V e x))).Finite :=
      hPreP.preimage' (fun y _ => hFibres y)
    have hColumn : (Set.range (Nat.pair x)).Infinite :=
      Set.infinite_range_of_injective (fun _ _ hab => (Nat.pair_eq_pair.mp hab).2)
    apply hColumn (hPreH.subset ?_)
    rintro _ ⟨n, rfl⟩
    change p (h (Nat.pair x n)) ∈ V e x
    rw [← hRow x]
    exact ⟨n, rfl⟩

theorem existsStrictPullback (A : Set Nat)
    (hA : REPred (fun n => n ∈ A))
    (hNonrec : ¬ ComputablePred (fun n => n ∈ A))
    (hNoncyl : ¬ (OneOneReducible (fun n => n ∈ A) (fun n => n ∈ cylinder A) ∧
      OneOneReducible (fun n => n ∈ cylinder A) (fun n => n ∈ A))) :
    ∃ C : Set Nat, ManyOneDegree.of C = ManyOneDegree.of A ∧
      FiniteOneReducible A C ∧ ¬ FiniteOneReducible C A ∧
      FiniteOneReducible C (cylinder A) ∧ ¬ FiniteOneReducible (cylinder A) C := by
  classical
  obtain ⟨_, hSurj, hUniversal, _⟩ :=
    HaltingSigmaOneCompleteness.canonicalNumbering_acceptable
  let before (q r : Nat × Nat) : Prop := Nat.pair q.1 q.2 < Nat.pair r.1 r.2
  have hOrder : IsStrictTotalOrder (Nat × Nat) before :=
    Nat.pairEquiv.injective.isStrictTotalOrder_onFun (· < ·)
  have hCode : Primrec (fun q : Nat × Nat => Nat.pair q.1 q.2) :=
    Primrec₂.natPair.comp Primrec.fst Primrec.snd
  have hBefore : ComputablePred (fun p : (Nat × Nat) × (Nat × Nat) => before p.1 p.2) :=
    (Primrec.nat_lt.comp (hCode.comp Primrec.fst) (hCode.comp Primrec.snd)).computablePred

  let K := PriorityRequirements.haltingOracle φ
  let oracle (n : Nat) : Part Nat :=
    Part.some (@ite Nat (n ∈ K) (Classical.propDecidable _) 1 0)
  obtain ⟨code, hCodeDom⟩ := (ComputablyEnumerableSet.nat_rePred_iff_exists_code A).mp hA
  let e := Encodable.encode code
  have hQuerySpec (n : Nat) : Nat.pair e n ∈ K ↔ n ∈ A := by
    rw [show K = PriorityRequirements.haltingOracle φ from rfl,
      PriorityRequirements.pair_mem_haltingOracle]
    change ((Denumerable.ofNat Nat.Partrec.Code (Encodable.encode code)).eval n).Dom ↔ n ∈ A
    rw [Denumerable.ofNat_encode]
    exact hCodeDom n
  have hPairComputable : Computable (Nat.pair e) :=
    Primrec₂.natPair.to_comp.comp (Computable.const e) Computable.id
  have hFlipComputable : Computable (fun n : Nat => 1 - n) :=
    Primrec.nat_sub.to_comp.comp (Computable.const 1) Computable.id
  have hPair : Nat.RecursiveIn {oracle} (fun n => Part.some (Nat.pair e n)) :=
    RecursiveIn.iff_nat.mp hPairComputable.computableIn
  have hOracle : Nat.RecursiveIn {oracle} oracle :=
    Nat.RecursiveIn.oracle oracle (Set.mem_singleton oracle)
  have hFlip : Nat.RecursiveIn {oracle} (fun n => Part.some (1 - n)) :=
    RecursiveIn.iff_nat.mp hFlipComputable.computableIn
  have hM : Nat.RecursiveIn {oracle} (fun n =>
      Part.some (@ite Nat (n ∈ Aᶜ) (Classical.propDecidable _) 1 0)) := by
    refine (hFlip.comp (hOracle.comp hPair)).of_eq (fun n => ?_)
    by_cases h : n ∈ A <;> simp [oracle, hQuerySpec n, h]
  obtain ⟨T, _, hSigma⟩ :=
    PriorityRequirements.existsEffectiveTrace φ stage Aᶜ before hUniversal hSurj
      HaltingSigmaOneCompleteness.computable_rowAt_code hOrder hBefore hM
  exact strictPullback A hA hNonrec hNoncyl T hSigma

end MaslovaStrictness

#print axioms MaslovaStrictness.existsStrictPullback

theorem MaslovaCeDichotomy : (
let encode (n : _root_.Nat) := _root_.List.replicate n _root_.Bool.false
let decode (w : _root_.List _root_.Bool) :=
  if w = encode (_root_.List.length w) then _root_.Option.some (_root_.List.length w)
  else _root_.Option.none
let ce : _root_.Set _root_.Nat → Prop :=
  _root_.ComputablyEnumerableSet encode decode
    (_root_.List.replicate_left_injective _root_.Bool.false)
    (fun n => by simp [decode, encode])
    (fun w hw => _root_.ite_eq_right (fun h => hw ⟨_root_.List.length w, h.symm⟩))
let finiteOneReducible (X Y : _root_.Set _root_.Nat) : Prop :=
  ∃ f : _root_.Nat → _root_.Nat, _root_.Computable f ∧
    (∀ y : _root_.Nat, _root_.Set.Finite (_root_.Set.preimage f ({y} : _root_.Set _root_.Nat))) ∧
    (∀ x : _root_.Nat, x ∈ X ↔ f x ∈ Y)
let finiteOneDegree (X : _root_.Set _root_.Nat) : _root_.Set (_root_.Set _root_.Nat) :=
  {Y | finiteOneReducible Y X ∧ finiteOneReducible X Y}
∀ A : _root_.Set _root_.Nat,
  let d : _root_.Set (_root_.Set _root_.Nat) :=
    {X | _root_.ManyOneReducibilityOnNat X A ∧ _root_.ManyOneReducibilityOnNat A X}
  (¬ ∃ X ∈ d, _root_.ComputablePred (fun n : _root_.Nat => n ∈ X)) →
  (∃ X ∈ d, ce X) →
  let finiteOneDegrees := _root_.Set.image finiteOneDegree d
  _root_.ExistsUnique (fun D => D ∈ finiteOneDegrees) ∨ _root_.Set.Infinite finiteOneDegrees) := by
  classical
  intro encode decode ce fo degree A d hNonrec hCE F
  have hEq (X : Set Nat) : X ∈ d ↔ ManyOneDegree.of X = ManyOneDegree.of A :=
    ManyOneDegree.of_eq_of.symm
  obtain ⟨B, hBd, hBce⟩ := hCE
  have hB : REPred (fun n => n ∈ B) :=
    (ComputablyEnumerableSet.nat_rePred_iff false B).mpr hBce
  have hRE (X : Set Nat) (hXd : X ∈ d) : REPred (fun n => n ∈ X) := by
    have hXB := (hEq X).mp hXd |>.trans ((hEq B).mp hBd).symm
    obtain ⟨f, hf, hMem⟩ := (ManyOneDegree.of_eq_of.mp hXB).1
    let semi (n : Nat) : Part Unit := Part.assert (n ∈ B) (fun _ => Part.some ())
    have hSemi : Partrec semi := hB
    refine (hSemi.comp hf).dom_re.of_eq (fun n => ?_)
    simp [semi, hMem n, Part.dom_iff_mem]

  let top : F := ⟨degree (MaslovaStrictness.cylinder A),
    ⟨MaslovaStrictness.cylinder A, (hEq _).mpr (CylinderGreatestFiniteOneDegree A).1, rfl⟩⟩
  by_cases hFin : F.Finite
  · left
    by_cases hOnly : ∀ E : F, E = top
    · exact ⟨top.val, top.property, fun D hD => congrArg Subtype.val (hOnly ⟨D, hD⟩)⟩
    have hBelow : ({E : F | E ≠ top} : Set F).Nonempty := by
      push Not at hOnly
      exact hOnly
    let rep (E : F) : Set Nat := Classical.choose E.property
    have hRep (E : F) : rep E ∈ d ∧ finiteOneDegree (rep E) = E.val :=
      Classical.choose_spec E.property
    let _ : LE F := ⟨fun E D => FiniteOneReducible (rep E) (rep D)⟩
    let _ : IsTrans F (· ≤ ·) := ⟨fun _ _ _ => finiteOneTrans⟩
    let _ : Finite F := hFin.to_subtype
    obtain ⟨E, hMax⟩ := (Set.toFinite {E : F | E ≠ top}).exists_maximal hBelow

    let X := rep E
    have hXd : X ∈ d := (hRep E).1
    have hXDegree := (hEq X).mp hXd
    have hXT : finiteOneDegree (MaslovaStrictness.cylinder X) = top.val := by
      have hCylX := (CylinderGreatestFiniteOneDegree X).1
      have hCylA := (CylinderGreatestFiniteOneDegree A).1
      exact finiteOneDegree_eq_iff.mpr
        ⟨(CylinderGreatestFiniteOneDegree A).2 _ (hCylX.trans hXDegree),
          (CylinderGreatestFiniteOneDegree X).2 _ (hCylA.trans hXDegree.symm)⟩
    have hNoncyl : ¬ (OneOneReducible (fun n => n ∈ X)
        (fun n => n ∈ MaslovaStrictness.cylinder X) ∧
        OneOneReducible (fun n => n ∈ MaslovaStrictness.cylinder X) (fun n => n ∈ X)) := by
      rintro ⟨h1, h2⟩
      apply hMax.1
      apply Subtype.ext
      exact (hRep E).2.symm.trans ((finiteOneDegree_eq_iff.mpr
        ⟨(ReducibilityImplications _ _).1 h1, (ReducibilityImplications _ _).1 h2⟩).trans hXT)
    obtain ⟨C, hCX, hXC, hnCX, _, hnCylC⟩ :=
      MaslovaStrictness.existsStrictPullback X (hRE X hXd) (fun h => hNonrec ⟨X, hXd, h⟩) hNoncyl
    let D : F := ⟨finiteOneDegree C, ⟨C, (hEq C).mpr (hCX.trans hXDegree), rfl⟩⟩
    obtain ⟨_, hCD⟩ : FiniteOneReducible (rep D) C ∧ FiniteOneReducible C (rep D) :=
      finiteOneDegree_eq_iff.mp (hRep D).2
    have hDT : D ≠ top := by
      intro hDT
      apply hnCylC
      exact (finiteOneDegree_eq_iff.mp
        (hXT.trans (congrArg Subtype.val hDT).symm)).1
    exact False.elim (hnCX (finiteOneTrans hCD
      (hMax.2 (y := D) hDT (finiteOneTrans hXC hCD))))
  · exact Or.inr hFin

#print axioms MaslovaCeDichotomy
