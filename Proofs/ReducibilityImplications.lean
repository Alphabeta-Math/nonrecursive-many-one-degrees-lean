import Mathlib

import Proofs.ManyOneReducibilityOnNat

set_option maxHeartbeats 2000000

namespace ReducibilityImplications

/-- Finite-one reducibility on natural-number sets, with the article's singleton fibres. -/
abbrev FiniteOneReducible (X Y : Set Nat) : Prop :=
  ∃ f : Nat → Nat, Computable f ∧
    (∀ y : Nat, (Set.preimage f ({y} : Set Nat)).Finite) ∧
    (∀ x : Nat, x ∈ X ↔ f x ∈ Y)

theorem finiteOneRefl (X : Set Nat) : FiniteOneReducible X X := by
  -- Alphabeta Math, def-computable-many-one-reducibility-interface,
  -- verification step 1.1 gives the identity witness on Nat. Its fibres are singletons.
  exact ⟨id, Computable.id, fun y => Set.finite_singleton y, fun _ => Iff.rfl⟩

theorem finiteOneTrans {X Y Z : Set Nat}
    (hXY : FiniteOneReducible X Y) (hYZ : FiniteOneReducible Y Z) :
    FiniteOneReducible X Z := by
  -- The same verification step 1.1 gives computable composition and composes
  -- the membership equivalences. The finite-one hypothesis adds a fibre check.
  obtain ⟨f, hf, hfFinite, hfMem⟩ := hXY
  obtain ⟨g, hg, hgFinite, hgMem⟩ := hYZ
  refine ⟨g ∘ f, hg.comp hf, ?_, fun x => (hfMem x).trans (hgMem (f x))⟩
  intro y
  -- The composite fibre is the preimage under f of the finite g-fibre.
  -- All f-fibres over that target set are finite by hfFinite.
  change (Set.preimage f (Set.preimage g ({y} : Set Nat))).Finite
  exact (hgFinite y).preimage' (fun z _ => hfFinite z)

abbrev finiteOneDegree (X : Set Nat) : Set (Set Nat) :=
  {Y | FiniteOneReducible Y X ∧ FiniteOneReducible X Y}

theorem finiteOneDegree_eq_iff {X Y : Set Nat} :
    finiteOneDegree X = finiteOneDegree Y ↔
      FiniteOneReducible X Y ∧ FiniteOneReducible Y X := by
  -- Cintioli, §2, pp. 2–3: equal classes contain X in common by
  -- reflexivity. Mutual reductions transport every class member by transitivity.
  constructor
  · intro h
    have hXX : X ∈ finiteOneDegree X := ⟨finiteOneRefl X, finiteOneRefl X⟩
    rw [h] at hXX
    exact hXX
  · rintro ⟨hXY, hYX⟩
    ext Z
    change (FiniteOneReducible Z X ∧ FiniteOneReducible X Z) ↔
      (FiniteOneReducible Z Y ∧ FiniteOneReducible Y Z)
    exact ⟨fun ⟨hZX, hXZ⟩ => ⟨finiteOneTrans hZX hXY, finiteOneTrans hYX hXZ⟩,
      fun ⟨hZY, hYZ⟩ => ⟨finiteOneTrans hZY hYX, finiteOneTrans hXY hYZ⟩⟩

end ReducibilityImplications

theorem ReducibilityImplications : (∀ X Y : _root_.Set _root_.Nat,
  let finiteOneReducible : Prop :=
    ∃ f : _root_.Nat → _root_.Nat, _root_.Computable f ∧
      (∀ y : _root_.Nat, _root_.Set.Finite (_root_.Set.preimage f ({y} : _root_.Set _root_.Nat))) ∧
      (∀ x : _root_.Nat, x ∈ X ↔ f x ∈ Y)
  (_root_.OneOneReducible (fun x : _root_.Nat => x ∈ X) (fun y : _root_.Nat => y ∈ Y) → finiteOneReducible) ∧
  (finiteOneReducible → _root_.ManyOneReducibilityOnNat X Y)) :=
(by
  -- Cintioli, arXiv:2609.00419v1, §1, p. 1 and §2, p. 2.
  -- Alphabeta Math's def-computable-many-one-reducibility-interface,
  -- verification step 1.1 uses a total computable Nat map and a pointwise
  -- membership equivalence. Here both implications preserve that witness
  -- verbatim. The extra check is finiteness of singleton preimages.
  -- The article-specific Research Portal and its defect report returned HTTP 404.
  intro X Y
  dsimp only
  constructor
  · rintro ⟨f, hf, hfInjective, hfMem⟩
    refine ⟨f, hf, ?_, hfMem⟩
    intro y
    exact Set.Finite.preimage hfInjective.injOn (Set.finite_singleton y)
  · rintro ⟨f, hf, _, hfMem⟩
    unfold ManyOneReducibilityOnNat
    exact ⟨f, hf, hfMem⟩)
