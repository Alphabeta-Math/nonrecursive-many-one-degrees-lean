import Mathlib

import Proofs.ReducibilityImplications

set_option maxHeartbeats 2000000

theorem ComplementationOrderIsomorphism : (∀ A : _root_.Set _root_.Nat,
  _root_.REPred (fun n : _root_.Nat => n ∈ Aᶜ) →
  let finiteOneReducible (X Y : _root_.Set _root_.Nat) : Prop :=
    ∃ f : _root_.Nat → _root_.Nat, _root_.Computable f ∧
      (∀ y : _root_.Nat, _root_.Set.Finite (_root_.Set.preimage f ({y} : _root_.Set _root_.Nat))) ∧
      (∀ x : _root_.Nat, x ∈ X ↔ f x ∈ Y)
  let finiteOneDegree (X : _root_.Set _root_.Nat) : _root_.Set (_root_.Set _root_.Nat) :=
    {Y | finiteOneReducible Y X ∧ finiteOneReducible X Y}
  let F (d : _root_.ManyOneDegree) : _root_.Set (_root_.Set (_root_.Set _root_.Nat)) :=
    _root_.Set.image finiteOneDegree {X | _root_.ManyOneDegree.of X = d}
  let degreeOrder (d : _root_.ManyOneDegree) : _root_.LE (F d) :=
    ⟨fun D E => ∃ X ∈ D.val, ∃ Y ∈ E.val, finiteOneReducible X Y⟩
  let d := _root_.ManyOneDegree.of A
  let dc := _root_.ManyOneDegree.of Aᶜ
  ∃ Φ : @_root_.OrderIso (F d) (F dc) (degreeOrder d) (degreeOrder dc),
    ∀ (X : _root_.Set _root_.Nat) (hX : _root_.ManyOneDegree.of X = d),
      (Φ ⟨finiteOneDegree X, ⟨X, hX, rfl⟩⟩).val =
        finiteOneDegree Xᶜ) :=
(by
  -- Cintioli, arXiv:2609.00419v1, §5, proof of Corollary 7, pp. 13–14.
  -- The article-specific Alphabeta Math portal and designated defect report
  -- returned HTTP 404.
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects
  -- Alphabeta Math's shared item def-computable-many-one-reducibility-interface,
  -- verification step 1.1, uses a total computable Nat map with a pointwise
  -- membership iff. Negating both predicates preserves that iff and the same
  -- witness, including all singleton fibres.
  -- https://alphabetamath.cc/item/def-computable-many-one-reducibility-interface
  -- The article's c.e. hypothesis is retained. The isomorphism itself uses
  -- only the many-one and finite-one reductions of the representatives.
  intro A _hA finiteOneReducible finiteOneDegree F degreeOrder d dc
  have manyOneCompl {X Y : Set Nat}
      (h : ManyOneReducible (· ∈ X) (· ∈ Y)) :
      ManyOneReducible (· ∈ Xᶜ) (· ∈ Yᶜ) := by
    obtain ⟨f, hf, hmem⟩ := h
    exact ⟨f, hf, fun x => (hmem x).not⟩
  have degreeCompl {X Y : Set Nat} (h : ManyOneDegree.of X = ManyOneDegree.of Y) :
      ManyOneDegree.of Xᶜ = ManyOneDegree.of Yᶜ := by
    obtain ⟨hXY, hYX⟩ := ManyOneDegree.of_eq_of.mp h
    exact ManyOneDegree.of_eq_of.mpr ⟨manyOneCompl hXY, manyOneCompl hYX⟩
  have finiteOneCompl {X Y : Set Nat} (h : finiteOneReducible X Y) :
      finiteOneReducible Xᶜ Yᶜ := by
    obtain ⟨f, hf, hfibre, hmem⟩ := h
    exact ⟨f, hf, hfibre, fun x => (hmem x).not⟩
  have finiteOneComplIff (X Y : Set Nat) :
      finiteOneReducible Xᶜ Yᶜ ↔ finiteOneReducible X Y :=
    ⟨fun h => by simpa only [compl_compl] using finiteOneCompl h, finiteOneCompl⟩
  have classCompl (X : Set Nat) :
      Set.image compl (finiteOneDegree X) = finiteOneDegree Xᶜ := by
    rw [Set.compl_image]
    ext Y
    change (finiteOneReducible Yᶜ X ∧ finiteOneReducible X Yᶜ) ↔
      (finiteOneReducible Y Xᶜ ∧ finiteOneReducible Xᶜ Y)
    simpa only [compl_compl] using
      and_congr (finiteOneComplIff Y Xᶜ) (finiteOneComplIff Xᶜ Y)
  -- The reviewed endpoint uses set-valued classes. Taking the image of each
  -- class under complement makes the representative independence explicit.
  let map {e e' : ManyOneDegree}
      (h : ∀ X : Set Nat, ManyOneDegree.of X = e → ManyOneDegree.of Xᶜ = e')
      (D : F e) : F e' :=
    ⟨Set.image compl D.val, by
      obtain ⟨X, hX, hD⟩ := D.property
      exact ⟨Xᶜ, h X hX, (classCompl X).symm.trans (congrArg (Set.image compl) hD)⟩⟩
  let forward : F d → F dc := map (fun _ hX => degreeCompl hX)
  let backward : F dc → F d := map (fun _ hX =>
    by simpa only [compl_compl] using degreeCompl hX)
  have imageComplCompl (D : Set (Set Nat)) :
      Set.image compl (Set.image compl D) = D := by
    simp only [Set.compl_image]
    ext X
    change Xᶜᶜ ∈ D ↔ X ∈ D
    rw [compl_compl]
  -- Alphabeta Math's verification step 1.1 also gives identity and composition.
  -- The local class and relation agree definitionally with the compiled
  -- supplier. Its finiteOneRefl and finiteOneTrans check finite fibres using
  -- singletons and finite preimages of finite sets, respectively. These
  -- proofs transport the existential witnesses to any representatives.
  have le_iff {e : ManyOneDegree} {D E : F e} {X Y : Set Nat}
      (hD : D.val = finiteOneDegree X) (hE : E.val = finiteOneDegree Y) :
      @LE.le (F e) (degreeOrder e) D E ↔ finiteOneReducible X Y := by
    change (∃ U ∈ D.val, ∃ V ∈ E.val, finiteOneReducible U V) ↔ _
    rw [hD, hE]
    constructor
    · rintro ⟨U, hU, V, hV, hUV⟩
      exact ReducibilityImplications.finiteOneTrans hU.2
        (ReducibilityImplications.finiteOneTrans hUV hV.1)
    · intro hXY
      exact ⟨X, ⟨ReducibilityImplications.finiteOneRefl X,
        ReducibilityImplications.finiteOneRefl X⟩,
        Y, ⟨ReducibilityImplications.finiteOneRefl Y,
        ReducibilityImplications.finiteOneRefl Y⟩, hXY⟩
  refine ⟨{
    toFun := forward
    invFun := backward
    left_inv := fun D => Subtype.ext (imageComplCompl D.val)
    right_inv := fun D => Subtype.ext (imageComplCompl D.val)
    map_rel_iff' := ?_ }, ?_⟩
  · intro D E
    obtain ⟨X, _, hD⟩ := D.property
    obtain ⟨Y, _, hE⟩ := E.property
    have hDX : (forward D).val = finiteOneDegree Xᶜ :=
      (congrArg (Set.image compl) hD.symm).trans (classCompl X)
    have hEY : (forward E).val = finiteOneDegree Yᶜ :=
      (congrArg (Set.image compl) hE.symm).trans (classCompl Y)
    change @LE.le (F dc) (degreeOrder dc) (forward D) (forward E) ↔
      @LE.le (F d) (degreeOrder d) D E
    rw [le_iff hDX hEY, le_iff hD.symm hE.symm]
    exact finiteOneComplIff X Y
  · intro X hX
    exact classCompl X
)
