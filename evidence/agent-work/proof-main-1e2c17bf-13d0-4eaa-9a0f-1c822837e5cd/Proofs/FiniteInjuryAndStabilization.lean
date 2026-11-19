import Mathlib



set_option maxHeartbeats 2000000

namespace FiniteInjuryAndStabilization

/-- The marker part of the finite-injury argument in §4, p. 9.
It applies to any lower search whose visits never replace a live marker. -/
theorem of_trace
    (acts : ℕ → ℕ → Prop) (marker : ℕ → ℕ → ℕ → Option ℕ)
    (nextStage : ∀ s e, marker (s + 1) 0 e = marker s s e)
    (once : ∀ i s t, acts s i → acts t i → s = t)
    (cause : ∀ s k e m, k < s → marker s k e = some m →
      marker s (k + 1) e = none → ∃ i, k = 2 * i ∧ 2 * i < 2 * e + 1 ∧ acts s i)
    (noReplacement : ∀ s k e m, k < s → marker s k e = some m →
      marker s (k + 1) e = none ∨ marker s (k + 1) e = some m) :
    let injured (s k e : ℕ) : Prop :=
      k < s ∧ (∃ m, marker s k e = some m) ∧ marker s (k + 1) e = none
    let restraints (s k p : ℕ) : Set ℕ :=
      {m | ∃ e, 2 * e + 1 < p ∧ marker s k e = some m}
    (∀ e, Set.Finite {event : ℕ × ℕ | injured event.1 event.2 e}) ∧
    (∀ e, ∃ s₀,
      (∀ s i, s₀ < s → 2 * i < 2 * e + 1 → ¬ acts s i) ∧
      (∀ s k, s₀ < s → ¬ injured s k e) ∧
      (∀ m s k, marker s₀ s₀ e = some m →
        s₀ < s → k ≤ s → marker s k e = some m)) ∧
    (∀ e, ∃ s₁ final, ∀ s k, s₁ ≤ s → k ≤ s → marker s k e = final) ∧
    (∀ p, ∃ (s₁ : ℕ) (Z : Set ℕ), Z.Finite ∧
      ∀ s k, s₁ ≤ s → k ≤ s → restraints s k p = Z) := by
  classical
  intro injured restraints
  have stageBound {α : Type} (S : Set α) (finite : S.Finite) (stage : α → ℕ) :
      ∃ bound, ∀ a ∈ S, stage a ≤ bound := by
    by_cases nonempty : finite.toFinset.Nonempty
    · obtain ⟨a, _, maximal⟩ := Finset.exists_max_image finite.toFinset stage nonempty
      exact ⟨stage a, fun b hb => maximal b (finite.mem_toFinset.mpr hb)⟩
    · have empty := Finset.not_nonempty_iff_eq_empty.mp nonempty
      refine ⟨0, fun a ha => ?_⟩
      have mem := finite.mem_toFinset.mpr ha
      simp [empty] at mem

  -- Verification, paragraphs 1–3 (p. 9): charge each cancellation to its upper visit.
  -- The stage/visit pairs already identify actual cancellations. The two reviewed Tau Ceti
  -- suppliers use fresh entries at or below a restraint and a union of injuring numbers
  -- (Causes.lean:58 and Basic.lean:259 at 91942aa9ff8cea04d0d9905b80f75c07ce2379c4).
  -- Such a batch can be nonempty without the marker being cancelled. Here the finite graph
  -- of actual upper actions bounds both cancellation events and their stages directly.
  let higherActions (e : ℕ) : Set (ℕ × ℕ) :=
    {a | 2 * a.2 < 2 * e + 1 ∧ acts a.1 a.2}
  have finiteActions (e : ℕ) : (higherActions e).Finite := by
    have injective : Set.InjOn Prod.snd (higherActions e) := by
      rintro ⟨s, i⟩ hs ⟨t, j⟩ ht (rfl : i = j)
      exact Prod.ext (once i s t hs.2 ht.2) rfl
    apply (Set.finite_image_iff injective).mp
    apply (Set.finite_le_nat e).subset
    rintro _ ⟨⟨s, i⟩, hi, rfl⟩
    have priority : 2 * i < 2 * e + 1 := hi.1
    change i ≤ e
    omega
  have finiteInjuries (e : ℕ) : Set.Finite {a : ℕ × ℕ | injured a.1 a.2 e} := by
    apply ((finiteActions e).image (fun a => (a.1, 2 * a.2))).subset
    rintro ⟨s, k⟩ ⟨visit, ⟨m, before⟩, after⟩
    obtain ⟨i, rfl, priority, action⟩ := cause s k e m visit before after
    exact ⟨(s, i), ⟨priority, action⟩, rfl⟩
  have noLateActions (e : ℕ) :
      ∃ s₀, ∀ s i, s₀ < s → 2 * i < 2 * e + 1 → ¬ acts s i := by
    obtain ⟨s₀, bound⟩ := stageBound (higherActions e) (finiteActions e) Prod.fst
    exact ⟨s₀, fun s i late priority action =>
      (Nat.not_le_of_lt late) (bound (s, i) ⟨priority, action⟩)⟩
  have afterBound (e s₀ : ℕ)
      (noAction : ∀ s i, s₀ < s → 2 * i < 2 * e + 1 → ¬ acts s i) :
      (∀ s k, s₀ < s → ¬ injured s k e) ∧
      (∀ m s k, marker s₀ s₀ e = some m →
        s₀ < s → k ≤ s → marker s k e = some m) ∧
      (∃ s₁ final, ∀ s k, s₁ ≤ s → k ≤ s → marker s k e = final) := by
    have noInjury (s k : ℕ) (late : s₀ < s) : ¬ injured s k e := by
      rintro ⟨visit, ⟨m, before⟩, after⟩
      obtain ⟨i, _, priority, action⟩ := cause s k e m visit before after
      exact noAction s i late priority action

    -- Verification, paragraph 4: propagate a live marker through individual visits,
    -- then across the stage boundary. The first persistence argument starts at
    -- the *end* of the bound stage, as required by the stage/visit convention.
    have throughVisits (m s k : ℕ) (late : s₀ < s)
        (live : marker s k e = some m) (j : ℕ) (fromVisit : k ≤ j) (valid : j ≤ s) :
        marker s j e = some m := by
      induction j, fromVisit using Nat.le_induction with
      | base => exact live
      | succ j _ ih =>
        have visit : j < s := by omega
        have before := ih (Nat.le_of_lt visit)
        rcases noReplacement s j e m visit before with after | after
        · exact (noInjury s j late ⟨visit, ⟨m, before⟩, after⟩).elim
        · exact after
    have carryLater (m r : ℕ) (pastBound : s₀ ≤ r) (live : marker r r e = some m)
        (s : ℕ) (later : r < s) : ∀ k ≤ s, marker s k e = some m := by
      have later' : r + 1 ≤ s := later
      clear later
      induction s, later' using Nat.le_induction with
      | base =>
        intro k valid
        exact throughVisits m (r + 1) 0 (by omega)
          ((nextStage r e).trans live) k (Nat.zero_le k) valid
      | succ s _ ih =>
        intro k valid
        exact throughVisits m (s + 1) 0 (by omega)
          ((nextStage s e).trans (ih s le_rfl)) k (Nat.zero_le k) valid
    refine ⟨noInjury, fun m s k live late valid => carryLater m s₀ le_rfl live s late k valid, ?_⟩
    by_cases laterMarker : ∃ s k m, s₀ < s ∧ k ≤ s ∧ marker s k e = some m
    · obtain ⟨s, k, m, late, valid, live⟩ := laterMarker
      have endLive := throughVisits m s k late live s valid le_rfl
      -- Any later live visit supplies a bound, so no least allocation stage is needed.
      exact ⟨s + 1, some m, fun t j ht hj =>
        carryLater m s (Nat.le_of_lt late) endLive t ht j hj⟩
    · refine ⟨s₀ + 1, none, fun s k late valid => ?_⟩
      cases seen : marker s k e with
      | none => rfl
      | some m => exact (laterMarker ⟨s, k, m, late, valid, seen⟩).elim

  have quiet (e : ℕ) : ∃ s₀,
      (∀ s i, s₀ < s → 2 * i < 2 * e + 1 → ¬ acts s i) ∧
      (∀ s k, s₀ < s → ¬ injured s k e) ∧
      (∀ m s k, marker s₀ s₀ e = some m →
        s₀ < s → k ≤ s → marker s k e = some m) := by
    obtain ⟨s₀, noAction⟩ := noLateActions e
    exact ⟨s₀, noAction, (afterBound e s₀ noAction).1, (afterBound e s₀ noAction).2.1⟩
  have stable (e : ℕ) : ∃ s₁ final, ∀ s k, s₁ ≤ s → k ≤ s → marker s k e = final := by
    obtain ⟨s₀, noAction⟩ := noLateActions e
    exact (afterBound e s₀ noAction).2.2

  -- Verification, final paragraph: take one bound for the finitely many higher
  -- lower requirements and collect the live values of their final options.
  refine ⟨finiteInjuries, quiet, stable, fun p => ?_⟩
  choose stage value fixed using stable
  let higher : Set ℕ := {e | 2 * e + 1 < p}
  have finiteHigher : higher.Finite := (Set.finite_lt_nat p).subset (by
    intro e h
    change 2 * e + 1 < p at h
    change e < p
    omega)
  obtain ⟨s₁, bound⟩ := stageBound higher finiteHigher stage
  let Z : Set ℕ := {m | ∃ e ∈ higher, value e = some m}
  refine ⟨s₁, Z, ?_, ?_⟩
  · apply (finiteHigher.image (fun e => (value e).getD 0)).subset
    rintro m ⟨e, he, hm⟩
    exact ⟨e, he, by simp [hm]⟩
  · intro s k hs hk
    ext m
    change (∃ e ∈ higher, marker s k e = some m) ↔ ∃ e ∈ higher, value e = some m
    constructor <;> rintro ⟨e, he, hm⟩ <;> refine ⟨e, he, ?_⟩
    · rwa [fixed e s k ((bound e he).trans hs) hk] at hm
    · rwa [fixed e s k ((bound e he).trans hs) hk]

end FiniteInjuryAndStabilization


theorem FiniteInjuryAndStabilization : (∀ (φ : _root_.Nat → _root_.Nat → _root_.Part _root_.Nat)
  (V : _root_.Nat → _root_.Nat → _root_.Set _root_.Nat)
  (rowAt : _root_.Nat → _root_.Nat → _root_.Nat → _root_.Finset _root_.Nat)
  (pairBefore : (_root_.Nat × _root_.Nat) → (_root_.Nat × _root_.Nat) → Prop)
  (chosenPair : _root_.Nat → _root_.Nat → _root_.Option (_root_.Nat × _root_.Nat))
  (satisfied : _root_.Nat → _root_.Nat → Prop)
  (content : _root_.Nat → _root_.Nat → _root_.Finset _root_.Nat)
  (marker : _root_.Nat → _root_.Nat → _root_.Nat → _root_.Option _root_.Nat),
  let upper (i : _root_.Nat) := 2 * i
  let lower (e : _root_.Nat) := 2 * e + 1
  let acts (s i : _root_.Nat) : Prop :=
    ∃ q, chosenPair s i = _root_.Option.some q
  let injured (s k e : _root_.Nat) : Prop :=
    k < s ∧ (∃ m, marker s k e = _root_.Option.some m) ∧
      marker s (k + 1) e = _root_.Option.none
  let restraints (s k p : _root_.Nat) : _root_.Set _root_.Nat :=
    {m | ∃ e, lower e < p ∧ marker s k e = _root_.Option.some m}
  let upperCandidate (s i : _root_.Nat) (q : _root_.Nat × _root_.Nat) : Prop :=
    let F := rowAt i q.1 q.2
    q.1 ≤ s ∧ q.2 ≤ s ∧
      (∀ m ∈ F, m ≤ s ∧ m ∉ restraints s (upper i) (upper i)) ∧
      (∀ r, q.2 ≤ r → rowAt i q.1 r = F)
  let lowerCandidate (s e m : _root_.Nat) : Prop :=
    m ≤ s ∧ ¬ _root_.Part.Dom (φ e m) ∧ m ∉ content s (lower e) ∧
      (∀ j, marker s (lower e) j ≠ _root_.Option.some m)
  ∀ (_effectiveFunctions : _root_.Partrec₂ φ)
    (_allPartialComputable : ∀ f : _root_.Nat → _root_.Part _root_.Nat,
      _root_.Partrec f → ∃ e, φ e = f)
    (_effectiveFamilies : _root_.REPred
      (fun p : _root_.Nat × _root_.Nat × _root_.Nat => p.2.2 ∈ V p.1 p.2.1))
    (_allUniformCEFamilies : ∀ i : _root_.Nat, ∃ e : _root_.Nat, ∀ x y : _root_.Nat,
      y ∈ V e x ↔ _root_.Part.Dom (φ i (_root_.Nat.pair x y)))
    (_computableStages : _root_.Computable
      (fun p : _root_.Nat × _root_.Nat × _root_.Nat =>
        (_root_.Equiv.symm _root_.Finset.equivBitIndices) (rowAt p.1 p.2.1 p.2.2)))
    (_increasingStages : ∀ i x, _root_.Monotone (rowAt i x))
    (_stageUnions : ∀ i x y, y ∈ V i x ↔ ∃ r : _root_.Nat, y ∈ rowAt i x r)
    (_pairOrder : _root_.IsStrictTotalOrder (_root_.Nat × _root_.Nat) pairBefore)
    (_computablePairOrder : _root_.ComputablePred
      (fun p : (_root_.Nat × _root_.Nat) × (_root_.Nat × _root_.Nat) =>
        pairBefore p.1 p.2))
    (_initial : content 0 0 = ∅ ∧
      (∀ e, marker 0 0 e = _root_.Option.none) ∧ (∀ i, ¬ satisfied 0 i))
    (_nextStage : ∀ s, content (s + 1) 0 = content s s ∧
      (∀ e, marker (s + 1) 0 e = marker s s e))
    (_activeMarkers : ∀ s k e m, k ≤ s → marker s k e = _root_.Option.some m →
      m ∉ content s k ∧ (∀ j, marker s k j = _root_.Option.some m → j = e))
    (_eligible : ∀ s i, acts s i → upper i < s ∧ ¬ satisfied s i)
    (_permanent : ∀ s i, satisfied (s + 1) i ↔ satisfied s i ∨ acts s i)
    (_upperVisit : ∀ s i, upper i < s →
      let k := upper i
      match chosenPair s i with
      | _root_.Option.none =>
        (satisfied s i ∨ ∀ q, ¬ upperCandidate s i q) ∧
        content s (k + 1) = content s k ∧
        (∀ e, marker s (k + 1) e = marker s k e)
      | _root_.Option.some q =>
        let F := rowAt i q.1 q.2
        upperCandidate s i q ∧
        (∀ p, upperCandidate s i p → ¬ pairBefore p q) ∧
        content s (k + 1) = content s k ∪ F ∧
        (∀ e, marker s (k + 1) e =
          match marker s k e with
          | _root_.Option.none => _root_.Option.none
          | _root_.Option.some m =>
            if k < lower e ∧ m ∈ F then _root_.Option.none else _root_.Option.some m))
    (_lowerVisit : ∀ s e, lower e < s →
      let k := lower e
      content s (k + 1) = content s k ∧
      (∀ j, j ≠ e → marker s (k + 1) j = marker s k j) ∧
      (match marker s k e with
      | _root_.Option.some m => marker s (k + 1) e = _root_.Option.some m
      | _root_.Option.none =>
        match marker s (k + 1) e with
        | _root_.Option.none => ∀ m, ¬ lowerCandidate s e m
        | _root_.Option.some m =>
          lowerCandidate s e m ∧ (∀ n, lowerCandidate s e n → m ≤ n))),
    (∀ s k e, injured s k e →
      ∃ i q m, k = upper i ∧ upper i < lower e ∧
        chosenPair s i = _root_.Option.some q ∧
        marker s k e = _root_.Option.some m ∧ m ∈ rowAt i q.1 q.2) ∧
    (∀ i s t, acts s i → acts t i → s = t) ∧
    (∀ e, _root_.Set.Finite {event : _root_.Nat × _root_.Nat | injured event.1 event.2 e}) ∧
    (∀ e, ∃ s₀,
      (∀ s i, s₀ < s → upper i < lower e → ¬ acts s i) ∧
      (∀ s k, s₀ < s → ¬ injured s k e) ∧
      (∀ m s k, marker s₀ s₀ e = _root_.Option.some m →
        s₀ < s → k ≤ s → marker s k e = _root_.Option.some m)) ∧
    (∀ e, ∃ s₁ final, ∀ s k, s₁ ≤ s → k ≤ s → marker s k e = final) ∧
    (∀ p, ∃ (s₁ : _root_.Nat) (Z : _root_.Set _root_.Nat), _root_.Set.Finite Z ∧
      ∀ s k, s₁ ≤ s → k ≤ s → restraints s k p = Z)) :=
(by
  classical
  intro φ V rowAt pairBefore chosenPair satisfied content marker
    upper lower acts injured restraints upperCandidate lowerCandidate
    _effectiveFunctions _allPartialComputable _effectiveFamilies _allUniformCEFamilies
    _computableStages _increasingStages _stageUnions _pairOrder _computablePairOrder
    _initial nextStage _activeMarkers eligible permanent upperVisit lowerVisit
  /- Source: arXiv:2609.00419v1, §4, p. 9, unnumbered Verification.
     The article's Research Portal and designated defect-report routes both returned
     HTTP 404, and there is no verified numbered Alphabeta proof for this endpoint.
     The comments follow the paragraphs of the article's Verification. -/
  -- Verification, paragraph 1: check the exact visit at which a live marker changes.
  -- The visit equations incorporate row disjointness and cancellation order.
  have visitEffect (s k e m : ℕ) (visit : k < s) (live : marker s k e = some m) :
      marker s (k + 1) e = some m ∨
        (marker s (k + 1) e = none ∧
          ∃ i q, k = upper i ∧ upper i < lower e ∧ chosenPair s i = some q ∧
            m ∈ rowAt i q.1 q.2) := by
    have kind : k = upper (k / 2) ∨ k = lower (k / 2) := by
      dsimp [upper, lower]
      omega
    rcases kind with upperIndex | lowerIndex
    · let i := k / 2
      have atUpper : upper i < s := upperIndex ▸ visit
      have step := upperVisit s i atUpper
      rw [upperIndex]
      cases selected : chosenPair s i with
      | none =>
        simp only [selected] at step
        exact Or.inl ((step.2.2 e).trans (upperIndex ▸ live))
      | some q =>
        simp only [selected] at step
        have before : marker s (upper i) e = some m := upperIndex ▸ live
        have after := step.2.2.2 e
        rw [before] at after
        by_cases cancels : upper i < lower e ∧ m ∈ rowAt i q.1 q.2
        · exact Or.inr ⟨by simpa [cancels] using after, i, q, rfl, cancels.1, selected, cancels.2⟩
        · exact Or.inl (by simpa [cancels] using after)
    · let j := k / 2
      have atLower : lower j < s := lowerIndex ▸ visit
      have step := lowerVisit s j atLower
      rw [lowerIndex]
      left
      by_cases same : e = j
      · subst e
        have before : marker s (lower j) j = some m := lowerIndex ▸ live
        have after := step.2.2
        simpa only [before] using after
      · exact (step.2.1 e same).trans (lowerIndex ▸ live)

  have cause (s k e : ℕ) (event : injured s k e) :
      ∃ i q m, k = upper i ∧ upper i < lower e ∧
        chosenPair s i = some q ∧ marker s k e = some m ∧ m ∈ rowAt i q.1 q.2 := by
    obtain ⟨visit, ⟨m, live⟩, cancelled⟩ := event
    rcases visitEffect s k e m visit live with kept | ⟨_, i, q, hi, priority, selected, mem⟩
    · rw [cancelled] at kept
      cases kept
    · exact ⟨i, q, m, hi, priority, selected, live, mem⟩

  -- Verification, paragraphs 2–3: satisfaction persists from the stage immediately
  -- after an action. Eligibility then rules out a second action at any later stage.
  have satisfiedLater (i s : ℕ) (action : acts s i) (t : ℕ) (later : s < t) :
      satisfied t i := by
    have later' : s + 1 ≤ t := later
    clear later
    induction t, later' using Nat.le_induction with
    | base => exact (permanent s i).mpr (Or.inr action)
    | succ t _ ih => exact (permanent t i).mpr (Or.inl ih)
  have once (i s t : ℕ) (first : acts s i) (second : acts t i) : s = t := by
    rcases lt_trichotomy s t with earlier | same | later
    · exact ((eligible t i second).2 (satisfiedLater i s first t earlier)).elim
    · exact same
    · exact ((eligible s i first).2 (satisfiedLater i t second s later)).elim

  exact ⟨cause, once, FiniteInjuryAndStabilization.of_trace acts marker
    (fun s e => (nextStage s).2 e) once
    (fun s k e m visit live cancelled => by
      obtain ⟨i, q, _, hi, priority, selected, _, _⟩ :=
        cause s k e ⟨visit, ⟨m, live⟩, cancelled⟩
      exact ⟨i, hi, priority, q, selected⟩)
    (fun s k e m visit live => by
      rcases visitEffect s k e m visit live with kept | ⟨cancelled, _⟩
      · exact Or.inr kept
      · exact Or.inl cancelled)⟩
)
