import Proofs.CylinderGreatestFiniteOneDegree
import Proofs.ComputablyEnumerableSet
import Mathlib.Order.Preorder.Finite

namespace MaslovaDegreeOrder

open ReducibilityImplications (FiniteOneReducible finiteOneDegree finiteOneDegree_eq_iff
  finiteOneRefl finiteOneTrans)

abbrev manyOneClass (A : Set Nat) : Set (Set Nat) :=
  {X | ManyOneReducibilityOnNat X A ∧ ManyOneReducibilityOnNat A X}

abbrev finiteOneClasses (A : Set Nat) : Set (Set (Set Nat)) :=
  finiteOneDegree '' manyOneClass A

abbrev cylinder (A : Set Nat) : Set Nat :=
  {z | ∃ x n : Nat, x ∈ A ∧ z = Nat.pair x n}

abbrev IsCylinder (X : Set Nat) : Prop :=
  OneOneReducible (fun n => n ∈ X) (fun n => n ∈ cylinder X) ∧
  OneOneReducible (fun n => n ∈ cylinder X) (fun n => n ∈ X)

theorem mem_manyOneClass {X A : Set Nat} :
    X ∈ manyOneClass A ↔ ManyOneDegree.of X = ManyOneDegree.of A := by
  change ManyOneEquiv (fun n => n ∈ X) (fun n => n ∈ A) ↔ _
  exact (ManyOneDegree.of_eq_of (p := X) (q := A)).symm

theorem transport {X X' Y Y' : Set Nat}
    (hx : finiteOneDegree X = finiteOneDegree X')
    (hy : finiteOneDegree Y = finiteOneDegree Y')
    (h : FiniteOneReducible X' Y') : FiniteOneReducible X Y :=
  finiteOneTrans (finiteOneDegree_eq_iff.mp hx).1
    (finiteOneTrans h (finiteOneDegree_eq_iff.mp hy).2)

def classLE (D E : Set (Set Nat)) : Prop :=
  ∃ X Y, finiteOneDegree X = D ∧ finiteOneDegree Y = E ∧ FiniteOneReducible X Y

theorem classLE_iff (X Y : Set Nat) :
    classLE (finiteOneDegree X) (finiteOneDegree Y) ↔ FiniteOneReducible X Y := by
  constructor
  · rintro ⟨X', Y', hx, hy, h⟩
    exact transport hx.symm hy.symm h
  · intro h
    exact ⟨X, Y, rfl, rfl, h⟩

theorem classLE_trans {D E F : Set (Set Nat)} :
    classLE D E → classLE E F → classLE D F := by
  rintro ⟨X, Y, hX, hY, hXY⟩ ⟨Y', Z, hY', hZ, hYZ⟩
  have hYY' := (finiteOneDegree_eq_iff.mp (hY.trans hY'.symm)).1
  exact ⟨X, Z, hX, hZ, finiteOneTrans hXY (finiteOneTrans hYY' hYZ)⟩

theorem classLE_refl_of_mem {A : Set Nat} {D : Set (Set Nat)}
    (hD : D ∈ finiteOneClasses A) : classLE D D := by
  obtain ⟨X, _, rfl⟩ := hD
  exact (classLE_iff X X).mpr (finiteOneRefl X)

theorem classLE_antisymm {D E : Set (Set Nat)}
    (hDE : classLE D E) (hED : classLE E D) : D = E := by
  obtain ⟨X, Y, rfl, rfl, hXY⟩ := hDE
  exact finiteOneDegree_eq_iff.mpr ⟨hXY, (classLE_iff Y X).mp hED⟩

theorem top_mem (A : Set Nat) : finiteOneDegree (cylinder A) ∈ finiteOneClasses A :=
  ⟨cylinder A, mem_manyOneClass.mpr (CylinderGreatestFiniteOneDegree A).1, rfl⟩

theorem le_cylinder {X A : Set Nat} (hX : X ∈ manyOneClass A) :
    FiniteOneReducible X (cylinder A) :=
  (CylinderGreatestFiniteOneDegree A).2 X (mem_manyOneClass.mp hX)

theorem cylinder_eq_of_mem {A X : Set Nat} (hX : X ∈ manyOneClass A) :
    finiteOneDegree (cylinder X) = finiteOneDegree (cylinder A) := by
  have hAX : ManyOneDegree.of X = ManyOneDegree.of A := mem_manyOneClass.mp hX
  have hCX : ManyOneDegree.of (cylinder X) = ManyOneDegree.of X :=
    (CylinderGreatestFiniteOneDegree X).1
  have hCA : ManyOneDegree.of (cylinder A) = ManyOneDegree.of A :=
    (CylinderGreatestFiniteOneDegree A).1
  exact finiteOneDegree_eq_iff.mpr
    ⟨(CylinderGreatestFiniteOneDegree A).2 (cylinder X) (hCX.trans hAX),
     (CylinderGreatestFiniteOneDegree X).2 (cylinder A) (hCA.trans hAX.symm)⟩

theorem exists_nonCylinder_maximal (A : Set Nat)
    (hFin : (finiteOneClasses A).Finite)
    (hMulti : ¬ ∃! D, D ∈ finiteOneClasses A) :
    ∃ X ∈ manyOneClass A, ¬ IsCylinder X ∧
      ¬ FiniteOneReducible (cylinder X) X ∧
      ∀ Y ∈ manyOneClass A, FiniteOneReducible X Y →
        ¬ FiniteOneReducible (cylinder X) Y → FiniteOneReducible Y X := by
  classical
  let T := finiteOneDegree (cylinder A)
  have hT : T ∈ finiteOneClasses A := top_mem A
  let s := finiteOneClasses A \ {T}
  have hs : s.Finite := hFin.subset (fun _ h => h.1)
  have hsne : s.Nonempty := by
    by_contra h
    apply hMulti
    refine ⟨T, hT, ?_⟩
    intro D hD
    by_contra hDT
    exact h ⟨D, hD, fun hmem => hDT (Set.mem_singleton_iff.mp hmem)⟩
  obtain ⟨E, hE⟩ :=
    @Set.Finite.exists_maximal _ ⟨classLE⟩ ⟨fun _ _ _ => classLE_trans⟩ s hs hsne
  have hEs : E ∈ s := hE.1
  obtain ⟨X, hX, rfl⟩ := hEs.1
  have hXT : finiteOneDegree X ≠ T := fun h => hEs.2 (Set.mem_singleton_iff.mpr h)
  have hCylEq : finiteOneDegree (cylinder X) = T := cylinder_eq_of_mem hX
  have hNotBack : ¬ FiniteOneReducible (cylinder X) X := by
    intro hBack
    have hXC : FiniteOneReducible X (cylinder X) :=
      (CylinderGreatestFiniteOneDegree X).2 X rfl
    exact hXT ((finiteOneDegree_eq_iff.mpr ⟨hXC, hBack⟩).trans hCylEq)
  refine ⟨X, hX, fun h => hNotBack ((ReducibilityImplications (cylinder X) X).1 h.2),
    hNotBack, ?_⟩
  intro Y hY hXY hCY
  have hYT : finiteOneDegree Y ≠ T := by
    intro hYT
    exact hCY (finiteOneDegree_eq_iff.mp (hCylEq.trans hYT.symm)).1
  have hYs : finiteOneDegree Y ∈ s :=
    ⟨⟨Y, hY, rfl⟩, fun h => hYT (Set.mem_singleton_iff.mp h)⟩
  exact (classLE_iff Y X).mp (hE.2 hYs ((classLE_iff X Y).mpr hXY))

theorem dichotomy_of_interpolation (A : Set Nat)
    (interpolate : ∀ X ∈ manyOneClass A, ¬ IsCylinder X →
      ∃ Y ∈ manyOneClass A, FiniteOneReducible X Y ∧ ¬ FiniteOneReducible Y X ∧
        ¬ FiniteOneReducible (cylinder X) Y) :
    (∃! D, D ∈ finiteOneClasses A) ∨ (finiteOneClasses A).Infinite := by
  classical
  by_cases hFin : (finiteOneClasses A).Finite
  · left
    by_contra hMulti
    obtain ⟨X, hX, hNotCyl, _, hMax⟩ := exists_nonCylinder_maximal A hFin hMulti
    obtain ⟨Y, hY, hXY, hYX, hCY⟩ := interpolate X hX hNotCyl
    exact hYX (hMax Y hY hXY hCY)
  · exact Or.inr hFin

#print axioms exists_nonCylinder_maximal
#print axioms dichotomy_of_interpolation


theorem rePred_of_manyOne {X B : Set Nat} (hXB : ManyOneReducibilityOnNat X B)
    (hB : REPred (fun n => n ∈ B)) : REPred (fun n => n ∈ X) := by
  obtain ⟨f, hf, hfMem⟩ := hXB
  have hPull : REPred (fun n => f n ∈ B) := Partrec.comp hB hf
  exact hPull.of_eq fun n => (hfMem n).symm

theorem exact_endpoint_of_ce_interpolation
    (interpolate : ∀ X : Set Nat,
      (¬ ComputablePred (fun n => n ∈ X)) →
      REPred (fun n => n ∈ X) →
      (¬ REPred (fun n => n ∈ Xᶜ)) →
      (¬ IsCylinder X) →
      ∃ Y : Set Nat, ManyOneDegree.of Y = ManyOneDegree.of X ∧
        FiniteOneReducible X Y ∧ ¬ FiniteOneReducible Y X ∧
        ¬ FiniteOneReducible (cylinder X) Y) :

(let encode (n : _root_.Nat) := _root_.List.replicate n _root_.Bool.false
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
  intro encode decode ce fo degree A d hNonrec hCe F
  change (∃! D, D ∈ finiteOneClasses A) ∨ (finiteOneClasses A).Infinite
  obtain ⟨B, hB, hCeB⟩ := hCe
  have hReB : REPred (fun n => n ∈ B) :=
    (ComputablyEnumerableSet.nat_rePred_iff false B).mpr hCeB
  apply dichotomy_of_interpolation
  intro X hX hNotCyl
  have hNonrecX : ¬ ComputablePred (fun n => n ∈ X) :=
    fun h => hNonrec ⟨X, hX, h⟩
  have hReX : REPred (fun n => n ∈ X) :=
    rePred_of_manyOne
      ((ManyOneDegree.of_eq_of (p := X) (q := B)).mp
        ((mem_manyOneClass.mp hX).trans (mem_manyOneClass.mp hB).symm)).1 hReB
  have hNreX : ¬ REPred (fun n => n ∈ Xᶜ) :=
    fun h => hNonrecX (ComputablePred.computable_iff_re_compl_re'.mpr ⟨hReX, h⟩)
  obtain ⟨Y, hYX, hRest⟩ := interpolate X hNonrecX hReX hNreX hNotCyl
  exact ⟨Y, mem_manyOneClass.mpr (hYX.trans (mem_manyOneClass.mp hX)), hRest⟩

#print axioms exact_endpoint_of_ce_interpolation

end MaslovaDegreeOrder
