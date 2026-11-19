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
