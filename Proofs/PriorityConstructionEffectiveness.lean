import Mathlib

import Proofs.PriorityRequirements
import Proofs.RelativeComputabilityAndEnumerability
import Proofs.ComputablyEnumerableSet
import Proofs.FixedStageRowStability
import Proofs.OracleNegativePullbackDecision
import Proofs.PriorityBoundedOracleSearches
import Proofs.PriorityCodedVisitTrace
import Proofs.SingletonOracleTapeCompilation
import Proofs.FiniteMarkerAvoidance
import Proofs.CofiniteDomainLemma

set_option maxHeartbeats 2000000

theorem PriorityConstructionEffectiveness : (∀ (φ : _root_.Nat → _root_.Nat → _root_.Part _root_.Nat)
  (V : _root_.Nat → _root_.Nat → _root_.Set _root_.Nat)
  (rowAt : _root_.Nat → _root_.Nat → _root_.Nat → _root_.Finset _root_.Nat)
  (pairBefore : (_root_.Nat × _root_.Nat) → (_root_.Nat × _root_.Nat) → Prop),
  _root_.Partrec₂ φ →
  (∀ f : _root_.Nat → _root_.Part _root_.Nat,
    _root_.Partrec f → ∃ e, φ e = f) →
  _root_.REPred (fun p : _root_.Nat × _root_.Nat × _root_.Nat =>
    p.2.2 ∈ V p.1 p.2.1) →
  (∀ i : _root_.Nat, ∃ e : _root_.Nat, ∀ x y : _root_.Nat,
    y ∈ V e x ↔ _root_.Part.Dom (φ i (_root_.Nat.pair x y))) →
  _root_.Computable (fun p : _root_.Nat × _root_.Nat × _root_.Nat =>
    (_root_.Equiv.symm _root_.Finset.equivBitIndices) (rowAt p.1 p.2.1 p.2.2)) →
  (∀ e x, _root_.Monotone (rowAt e x)) →
  (∀ e x y, y ∈ V e x ↔ ∃ r : _root_.Nat, y ∈ rowAt e x r) →
  _root_.IsStrictTotalOrder (_root_.Nat × _root_.Nat) pairBefore →
  _root_.ComputablePred (fun p : (_root_.Nat × _root_.Nat) × (_root_.Nat × _root_.Nat) =>
    pairBefore p.1 p.2) →
  let K : _root_.Set _root_.Nat :=
    {n |
      let (e, m) := _root_.Nat.unpair n
      _root_.Part.Dom (φ e m)}
  let relative := _root_.RelativeComputabilityAndEnumerability K
  let bits := _root_.Finset.equivBitIndices
  let upperCandidate (e s : _root_.Nat) (Z : _root_.Finset _root_.Nat)
      (q : _root_.Nat × _root_.Nat) : Prop :=
    let F := rowAt e q.1 q.2
    q.1 ≤ s ∧ q.2 ≤ s ∧
      (∀ m ∈ F, m ≤ s ∧ m ∉ Z) ∧
      ∀ r, q.2 ≤ r → rowAt e q.1 r = F
  let lowerCandidate (e s : _root_.Nat) (content active : _root_.Finset _root_.Nat)
      (m : _root_.Nat) : Prop :=
    m ≤ s ∧ ¬ _root_.Part.Dom (φ e m) ∧ m ∉ content ∧ m ∉ active
  relative.1 (Kᶜ) ∧
  ∃ (upperSearch : _root_.Nat → _root_.Nat → _root_.Finset _root_.Nat →
        _root_.Option (_root_.Nat × _root_.Nat))
    (lowerSearch : _root_.Nat → _root_.Nat → _root_.Finset _root_.Nat →
        _root_.Finset _root_.Nat → _root_.Option _root_.Nat),
    relative.2.2 (fun n =>
      let (e, args) := _root_.Nat.unpair n
      let (s, z) := _root_.Nat.unpair args
      match upperSearch e s (bits z) with
      | _root_.Option.none => 0
      | _root_.Option.some (x, t) => _root_.Nat.succ (_root_.Nat.pair x t)) ∧
    relative.2.2 (fun n =>
      let (e, args) := _root_.Nat.unpair n
      let (s, sets) := _root_.Nat.unpair args
      let (content, active) := _root_.Nat.unpair sets
      match lowerSearch e s (bits content) (bits active) with
      | _root_.Option.none => 0
      | _root_.Option.some m => _root_.Nat.succ m) ∧
    (∀ e s Z,
      match upperSearch e s Z with
      | _root_.Option.none => ∀ q, ¬ upperCandidate e s Z q
      | _root_.Option.some q =>
        upperCandidate e s Z q ∧ ∀ p, upperCandidate e s Z p → ¬ pairBefore p q) ∧
    (∀ e s content active,
      match lowerSearch e s content active with
      | _root_.Option.none => ∀ m, ¬ lowerCandidate e s content active m
      | _root_.Option.some m =>
        lowerCandidate e s content active m ∧
          ∀ n, lowerCandidate e s content active n → m ≤ n) ∧
    let upper (e : _root_.Nat) := 2 * e
    let lower (e : _root_.Nat) := 2 * e + 1
    let markerSet (marker : _root_.Nat → _root_.Option _root_.Nat) (p : _root_.Nat) :=
      _root_.Finset.biUnion (_root_.Finset.range p) (fun j =>
        if lower j < p then
          match marker j with
          | _root_.Option.none => ∅
          | _root_.Option.some m => {m}
        else (∅ : _root_.Finset _root_.Nat))
    let State := _root_.Finset _root_.Nat ×
      (_root_.Nat → _root_.Option _root_.Nat) × (_root_.Nat → _root_.Bool)
    let initial : State := (∅, fun _ => _root_.Option.none, fun _ => _root_.Bool.false)
    let upperAction (s e : _root_.Nat) (state : State) :=
      if state.2.2 e then _root_.Option.none
      else upperSearch e s (markerSet state.2.1 (upper e))
    let visit (s k : _root_.Nat) (state : State) : State :=
      let e := k / 2
      if k % 2 = 0 then
        match upperAction s e state with
        | _root_.Option.none => state
        | _root_.Option.some (x, t) =>
          let F := rowAt e x t
          let remaining (j : _root_.Nat) :=
            match state.2.1 j with
            | _root_.Option.none => _root_.Option.none
            | _root_.Option.some m =>
              if k < lower j ∧ m ∈ F then _root_.Option.none else _root_.Option.some m
          (state.1 ∪ F, remaining, _root_.Function.update state.2.2 e _root_.Bool.true)
      else
        match state.2.1 e with
        | _root_.Option.some _ => state
        | _root_.Option.none =>
          let next := lowerSearch e s state.1 (markerSet state.2.1 s)
          (state.1, _root_.Function.update state.2.1 e next, state.2.2)
    let visits (s : _root_.Nat) (initialState : State) (k : _root_.Nat) : State :=
      _root_.Nat.rec initialState (fun p state => visit s p state) k
    let state (s k : _root_.Nat) : State :=
      let start := _root_.Nat.rec initial (fun r prev => visits r prev r) s
      visits s start (_root_.Nat.min k s)
    let chosenPair (s e : _root_.Nat) :=
      if upper e < s then upperAction s e (state s (upper e)) else _root_.Option.none
    let restraints (s e : _root_.Nat) :=
      markerSet (state s (upper e)).2.1 (upper e)
    let N : _root_.Set _root_.Nat := {m | ∃ s, m ∈ (state s s).1}
    relative.2.2 (fun n =>
      let (s, e) := _root_.Nat.unpair n
      (_root_.Equiv.symm bits) (restraints s e)) ∧
    (∀ s k e m, (state s k).2.1 e = _root_.Option.some m →
      ¬ _root_.Part.Dom (φ e m) ∧ m ∉ (state s k).1 ∧
        ∀ j, (state s k).2.1 j = _root_.Option.some m → j = e) ∧
    (∀ s e q m, chosenPair s e = _root_.Option.some q → m ∈ rowAt e q.1 q.2 → m ≤ s) ∧
    (∀ s m, s < m → m ∉ (state s s).1) ∧
    (∀ s e m, lower e < s →
      (state s (lower e)).2.1 e = _root_.Option.none →
      (state s (lower e + 1)).2.1 e = _root_.Option.some m →
      (∀ r i, s < r → upper i < lower e → chosenPair r i = _root_.Option.none) →
      m ∉ N ∧
        ∀ r i q, lower e < upper i → chosenPair r i = _root_.Option.some q →
          m ∉ rowAt i q.1 q.2) ∧
    ∀ A : _root_.Set _root_.Nat,
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
      ¬ _root_.ComputablePred (fun x : _root_.Nat => x ∈ A) →
      ¬ (_root_.OneOneReducible (fun x : _root_.Nat => x ∈ A) (fun z : _root_.Nat => z ∈ cyl) ∧
         _root_.OneOneReducible (fun z : _root_.Nat => z ∈ cyl) (fun x : _root_.Nat => x ∈ A)) →
      ¬ ce A → ¬ ce (Aᶜ) →
      (∀ e, (∀ x y, y ∈ V e x → (y ∈ A ↔ x ∈ A)) →
        ∀ Z : _root_.Finset _root_.Nat, (∃ S, ∀ s, S ≤ s → restraints s e = Z) →
        (∃ x, _root_.Set.Finite (V e x) ∧ V e x ∩ (Z : _root_.Set _root_.Nat) = ∅) ∧
        (∃ S, ∀ s, S ≤ s →
          ∃ q, upperSearch e s (restraints s e) = _root_.Option.some q) ∧
        (∃ s q, chosenPair s e = _root_.Option.some q)) ∧
      (∀ e, (∀ x y, y ∈ φ e x → x < y ∧ (y ∈ A ↔ x ∈ A)) →
        ∀ b : _root_.Nat, ∃ m : _root_.Nat, b < m ∧ ¬ _root_.Part.Dom (φ e m))) :=
(by
  classical
  intro φ V row pairBefore hφ hsurj hgraph _huniversal hrow hmono hunion horder hbefore
    K relative bits upperCandidate lowerCandidate
  -- Cintioli, §4, pp. 8–9 and Remark 6, p. 13.
  -- https://arxiv.org/pdf/2609.00419v1#page=13
  -- The article-specific Alphabeta Math portal and its defect report returned
  -- HTTP 404, and the local Research Portal has no matching collection.
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects
  -- The numbered steps cited here come from the shared library.
  -- Halting is Σ₁-complete, Steps 1.2 and 2.1:
  -- https://alphabetamath.cc/item/thm-halting-is-sigma-one-complete
  -- Search for a later changed row code and query its halting status. The
  -- supplied unary surjectivity gives one fixed index for this search with
  -- the triple packed into its input. FixedStageRowStability requires an
  -- acceptable numbering, so we use the query for these weaker hypotheses.
  have hK : K = PriorityRequirements.haltingOracle φ := by
    ext n
    change (let (e, m) := n.unpair; (φ e m).Dom) ↔ (φ n.unpair.1 n.unpair.2).Dom
    cases n.unpair
    rfl
  obtain ⟨query, hquery, hstable⟩ := PriorityRequirements.stabilityQuery φ hsurj row hrow
  let O : Set (Nat →. Nat) := {fun n => Part.some (if n ∈ K then 1 else 0)}
  have hM : Nat.RecursiveIn O (fun m => Part.some (@ite Nat (m ∈ (Set.univ : Set Nat)) (Classical.propDecidable _) 1 0)) := by
    simpa only [Set.mem_univ, ite_true] using
      (RecursiveIn.iff_nat.mp (ComputableIn.const (O := O) (α := Nat) (1 : Nat)))
  -- Keep the bounded searches and the decoded trace from one supplier
  -- instance. PriorityCodedVisitTrace obtains both witnesses from
  -- PriorityBoundedOracleSearches and uses mathlib's Nat.RecursiveIn.prec
  -- for the packed visit and stage recursions.
  -- https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Computability/RecursiveIn.lean#L71
  -- Its all-active invariant identifies the lower search mask with the
  -- active values. With univ, every natural is admissible for this test.
  have hM' : Nat.RecursiveIn
      {fun n => Part.some (if n ∈ PriorityRequirements.haltingOracle φ then 1 else 0)}
      (fun m => Part.some (@ite Nat (m ∈ (Set.univ : Set Nat)) (Classical.propDecidable _) 1 0)) := by
    rw [← hK]
    exact hM
  obtain ⟨U, L, hUcode, hLcode, hU, hL, _, _, hZcode, laws⟩ :=
    PriorityCodedVisitTrace φ row pairBefore query Set.univ
      hrow horder hbefore hquery hstable hM'
  -- The one-query theorem decides Kᶜ. The total-output compiler implements
  -- the two packed search outputs and the restraint code on the oracle tape.
  have decideComplement : relative.1 (Kᶜ) :=
    OracleNegativePullbackDecision K id Computable.id
  have compile := (SingletonOracleTapeCompilation K).2
  have hO : O =
      {fun n => Part.some (if n ∈ PriorityRequirements.haltingOracle φ then 1 else 0)} := by
    rw [← hK]
  refine ⟨decideComplement, U, L,
    compile (PriorityCodedTrace.upperCode U) (hO.symm ▸ hUcode),
    compile (PriorityCodedTrace.lowerCode L) (hO.symm ▸ hLcode), hU, ?_, ?_⟩
  · intro e s content active
    have correct := hL e s content active
    cases h : L e s content active <;>
      simpa only [h, lowerCandidate, PriorityCodedTrace.LowerCandidate, Set.mem_univ, true_and]
        using correct
  intro upper lower markerSet State initial upperAction visit visits state chosenPair restraints N
  -- The decoded supplier definitions reduce to the reviewed nested Nat.rec
  -- with these exact search witnesses. Splitting the decoded input identifies
  -- the restraint output expressed using projections with the pair match.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply compile
    have hcode := (hO.symm ▸ hZcode : Nat.RecursiveIn O
      (fun n => Part.some (bits.symm (PriorityCodedTrace.restraints row U L
        n.unpair.1 n.unpair.2))))
    apply hcode.of_eq
    intro n
    cases n.unpair
    rfl
  · intro s k e m hm
    exact ⟨(laws.active s k e m hm).2.1, (laws.active s k e m hm).2.2,
      fun j hj => laws.unique s k e j m hm hj⟩
  · intro s e q m hq hm
    obtain ⟨_, _, hcand, _⟩ := laws.action s e q hq
    exact (hcand.2.2.1 m hm).1
  · intro s m hsm hm
    exact (Nat.not_le_of_gt hsm) (laws.contentBound s s m hm)
  · -- A live marker is outside the current content. Propagate that marker
    -- from the very visit that installs it. Cancellation at the same stage
    -- would require an earlier visit; at a later stage quietness forbids it.
    intro s e m hvisit _ hnew hquiet
    change PriorityCodedTrace.marker row U L s (2 * e + 2) e = some m at hnew
    have retain (r k : Nat) (hrs : s ≤ r) (hk : k < r)
        (hindex : r = s → 2 * e + 2 ≤ k)
        (hm : PriorityCodedTrace.marker row U L r k e = some m) :
        PriorityCodedTrace.marker row U L r (k + 1) e = some m := by
      rcases laws.noReplacement r k e m hk hm with hcancel | hsame
      · obtain ⟨i, q, hki, hi, hq, _⟩ := laws.cancellation r k e m hk hm hcancel
        by_cases heq : r = s
        · have := hindex heq
          omega
        · have hn := hquiet r i (lt_of_le_of_ne hrs (Ne.symm heq)) hi
          change PriorityCodedTrace.chosenPair row U L r i = none at hn
          rw [hn] at hq
          contradiction
      · exact hsame
    have advance (r a : Nat) (hrs : s ≤ r) (ha : r = s → 2 * e + 2 ≤ a)
        (hm : PriorityCodedTrace.marker row U L r a e = some m) :
        ∀ k, a ≤ k → k ≤ r → PriorityCodedTrace.marker row U L r k e = some m := by
      intro k hak hkr
      induction k, hak using Nat.le_induction with
      | base => exact hm
      | succ k hak ih =>
        exact retain r k hrs (by omega) (fun hr => le_trans (ha hr) hak) (ih (by omega))
    have now (k : Nat) (hk : 2 * e + 2 ≤ k) (hks : k ≤ s) :
        PriorityCodedTrace.marker row U L s k e = some m :=
      advance s (2 * e + 2) le_rfl (fun _ => le_rfl) hnew k hk hks
    have finalMarker (r : Nat) (hrs : s ≤ r) :
        PriorityCodedTrace.marker row U L r r e = some m := by
      induction r, hrs using Nat.le_induction with
      | base => exact now s (by change 2 * e + 1 < s at hvisit; omega) le_rfl
      | succ r hrs ih =>
        have hstart := (laws.markerCarry r e).trans ih
        exact advance (r + 1) 0 (by omega) (fun h => by omega) hstart
          (r + 1) (Nat.zero_le _) le_rfl
    have later (r k : Nat) (hrs : s < r) (hkr : k ≤ r) :
        PriorityCodedTrace.marker row U L r k e = some m := by
      cases r with
      | zero => omega
      | succ r =>
        have hstart := (laws.markerCarry r e).trans (finalMarker r (by omega))
        exact advance (r + 1) 0 (by omega) (fun h => by omega) hstart k (Nat.zero_le _) hkr
    have contentAcross (a b : Nat) (hab : a ≤ b) :
        PriorityCodedTrace.content row U L a a ⊆ PriorityCodedTrace.content row U L b b := by
      induction b, hab using Nat.le_induction with
      | base => exact fun _ h => h
      | succ b _ ih =>
        exact Finset.Subset.trans ih (by
          rw [← laws.contentCarry b]
          exact laws.contentPersists (b + 1) 0 (b + 1) (Nat.zero_le _) le_rfl)
    constructor
    · rintro ⟨r, hr⟩
      change m ∈ PriorityCodedTrace.content row U L r r at hr
      by_cases hrs : r ≤ s
      · exact (laws.active s s e m (finalMarker s le_rfl)).2.2 (contentAcross r s hrs hr)
      · exact (laws.active r r e m (finalMarker r (by omega))).2.2 hr
    · intro r i q hi hq hm
      obtain ⟨hri, _, hcand, hcontent⟩ := laws.action r i q hq
      by_cases hrs : r < s
      · exact (laws.active s s e m (finalMarker s le_rfl)).2.2
          (contentAcross r s hrs.le (hcontent hm))
      · -- In stage s a lower-priority visit follows the allocation.
        -- In later stages the marker already persists from the start.
        change 2 * e + 1 < 2 * i at hi
        have live : PriorityCodedTrace.marker row U L r (2 * i) e = some m := by
          by_cases heq : r = s
          · subst r
            exact now (2 * i) (by omega) hri.le
          · exact later r (2 * i) (by omega) hri.le
        have restrained : m ∈ PriorityCodedTrace.restraints row U L r i :=
          (PriorityCodedTrace.memMarkerSet ..).mpr ⟨e, hi, live⟩
        exact (hcand.2.2.1 m hm).2 restrained
  · intro A cyl encode decode ce hnonrec hnoncyl hnonCE hnoncoCE
    constructor
    · intro e homogeneous Z hZ
      obtain ⟨S, hS⟩ := hZ
      -- Recognizable iff enumerable, Steps 1.2, 2.1 and 3.1:
      -- https://alphabetamath.cc/item/thm-recognizable-iff-enumerable
      -- Specialize the RE triple graph at e and unpack natural pair codes.
      -- The true-bit bridge treats both the empty graph and a computable
      -- range for the nonempty graph. Lemma 2 supplies an existential row.
      obtain ⟨x, hfinite, hdisjoint⟩ := FiniteMarkerAvoidance A (V e) hnoncyl hnonCE
        hnoncoCE ((ComputablyEnumerableSet.nat_rePred_iff true _).mp
          (PriorityRequirements.rowGraphRE hgraph e)) homogeneous Z (Finset.finite_toSet Z)
      obtain ⟨t, hexhausted, hstableRow⟩ :=
        PriorityRequirements.finiteRowExhaustion (hmono e x) (hunion e x) hfinite
      -- The bound certifies a candidate at each subsequent stage. The
      -- bounded searches themselves take only their current finite inputs.
      let bound := max (max S (2 * e + 1)) (max (max x t) ((row e x t).sup id))
      have candidate (s : Nat) (hs : bound ≤ s) :
          PriorityCodedTrace.UpperCandidate row e s (PriorityCodedTrace.restraints row U L s e)
            (x, t) := by
        have hbound : max (max S (2 * e + 1)) (max (max x t) ((row e x t).sup id)) ≤ s := hs
        simp only [max_le_iff] at hbound
        refine ⟨hbound.2.1.1, hbound.2.1.2, ?_, hstableRow⟩
        intro m hm
        refine ⟨(Finset.le_sup (f := id) hm).trans hbound.2.2, ?_⟩
        change m ∉ restraints s e
        rw [hS s hbound.1.1]
        intro hz
        have hv : m ∈ V e x := by
          rw [← hexhausted]
          exact hm
        have hmem : m ∈ V e x ∩ (Z : Set Nat) := ⟨hv, hz⟩
        rw [hdisjoint] at hmem
        exact hmem
      refine ⟨⟨x, hfinite, hdisjoint⟩, ⟨bound, ?_⟩, ?_⟩
      · intro s hs
        cases hresult : U e s (PriorityCodedTrace.restraints row U L s e) with
        | some q => exact ⟨q, hresult⟩
        | none =>
          have hspec := hU e s (PriorityCodedTrace.restraints row U L s e)
          rw [hresult] at hspec
          exact (hspec (x, t) (candidate s hs)).elim
      · -- An earlier action already witnesses success. In its absence the
        -- done flag is false, and the certified candidate forces an action.
        change ∃ s q, PriorityCodedTrace.chosenPair row U L s e = some q
        by_contra absent
        have notDone (s : Nat) : ¬ PriorityCodedTrace.done row U L s e := by
          induction s with
          | zero => exact laws.doneInitial e
          | succ s ih =>
            intro hd
            rcases (laws.doneNext s e).mp hd with hp | hq
            · exact ih hp
            · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hq
              exact absent ⟨s, q, hq⟩
        have hvisit : 2 * e < bound :=
          (Nat.lt_succ_self (2 * e)).trans_le ((le_max_right S (2 * e + 1)).trans (le_max_left ..))
        obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp
          (laws.upperProgress bound e (x, t) hvisit (notDone bound) (candidate bound le_rfl))
        exact absent ⟨bound, q, hq⟩
    · intro e ascending b
      -- Lemma 4 gives infinitely many omissions for the partial-recursive
      -- e-th section. The bound is used only in verification.
      have omissions := CofiniteDomainLemma A (φ e) hnonrec hnoncyl
        (hφ.comp (Computable.const e) Computable.id) ascending
      obtain ⟨m, hm, hb⟩ := omissions.exists_gt b
      exact ⟨m, hb, hm⟩)
