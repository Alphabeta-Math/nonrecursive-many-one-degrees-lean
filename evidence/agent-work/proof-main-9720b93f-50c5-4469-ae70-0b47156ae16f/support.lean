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
