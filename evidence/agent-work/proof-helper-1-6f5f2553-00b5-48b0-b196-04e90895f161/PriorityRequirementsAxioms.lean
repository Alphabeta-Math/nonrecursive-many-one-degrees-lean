import Mathlib

import Proofs.FiniteMarkerAvoidance
import Proofs.CofiniteDomainLemma
import Proofs.FixedStageRowStability
import Proofs.FiniteInjuryAndStabilization
import Proofs.RelativeComputabilityAndEnumerability
import Proofs.ArithmeticalHierarchyLevels
import Proofs.AcceptableNumbering
import Proofs.ComputablyEnumerableSet
import Proofs.OracleNegativePullbackDecision
import Proofs.PriorityBoundedOracleSearches
import Proofs.PriorityCodedVisitTrace
import Proofs.SingletonOracleTapeCompilation
import Proofs.CETapeOracleSigmaTwo

set_option maxHeartbeats 2000000

namespace PriorityRequirements

def haltingOracle (φ : ℕ → ℕ → Part ℕ) : Set ℕ :=
  {n | (φ n.unpair.1 n.unpair.2).Dom}

theorem pair_mem_haltingOracle (φ : ℕ → ℕ → Part ℕ) (e x : ℕ) :
    Nat.pair e x ∈ haltingOracle φ ↔ (φ e x).Dom := by
  simp [haltingOracle]

-- Alphabeta Math, thm-halting-is-sigma-one-complete, Step 1.1.
-- Joint partial recursiveness of φ suffices for c.e. membership in its
-- paired domain.
theorem haltingOracle_re (φ : ℕ → ℕ → Part ℕ) (hφ : Partrec₂ φ) :
    REPred (fun n => n ∈ haltingOracle φ) := by
  exact (hφ.comp (Computable.fst.comp Computable.unpair)
    (Computable.snd.comp Computable.unpair)).dom_re

/-- One query for the fixed-stage stability test in §4, p. 8. -/
theorem stabilityQuery
    (φ : ℕ → ℕ → Part ℕ)
    (surjective : ∀ f : ℕ → Part ℕ, Partrec f → ∃ e, φ e = f)
    (row : ℕ → ℕ → ℕ → Finset ℕ)
    (hrow : Computable fun p : ℕ × ℕ × ℕ =>
      Finset.equivBitIndices.symm (row p.1 p.2.1 p.2.2)) :
    ∃ query : ℕ → ℕ, Computable query ∧ ∀ e x t,
      query (Nat.pair e (Nat.pair x t)) ∉ haltingOracle φ ↔
        ∀ r, t ≤ r → row e x r = row e x t := by
  classical
  -- Alphabeta Math, thm-halting-is-sigma-one-complete, Step 1.2.
  -- https://alphabetamath.cc/item/thm-halting-is-sigma-one-complete
  -- Search offsets d at or after t. Comparing the two computable row codes
  -- gives a total computable witness predicate, which suffices for the
  -- minimization in Step 1.2 even without a primitive-recursive matrix.
  let input (p : ℕ × ℕ) : ℕ × ℕ × ℕ :=
    (p.1.unpair.1, p.1.unpair.2.unpair.1, p.1.unpair.2.unpair.2 + p.2)
  let code (p : ℕ × ℕ) := Finset.equivBitIndices.symm
    (row (input p).1 (input p).2.1 (input p).2.2)
  have outer : Computable (fun p : ℕ × ℕ => p.1.unpair) :=
    Computable.unpair.comp Computable.fst
  have inner : Computable (fun p : ℕ × ℕ => p.1.unpair.2.unpair) :=
    Computable.unpair.comp (Computable.snd.comp outer)
  have offset : Computable (fun p : ℕ × ℕ => p.1.unpair.2.unpair.2 + p.2) :=
    Primrec.nat_add.to_comp.comp (Computable.snd.comp inner) Computable.snd
  have hcode : Computable code := hrow.comp
    ((Computable.fst.comp outer).pair ((Computable.fst.comp inner).pair offset))
  let changed (p : ℕ × ℕ) := code p ≠ code (p.1, 0)
  have hchanged : ComputablePred changed :=
    ((Primrec.eq.decide.to_comp.comp hcode
      (hcode.comp (Computable.fst.pair (Computable.const 0)))).computablePred).not
  let search (n : ℕ) := Nat.rfind (fun d => Part.some (decide (changed (n, d))))
  have hsearch : Partrec search := Partrec.rfind hchanged.decide.partrec
  have hdom (n : ℕ) : (search n).Dom ↔ ∃ d, changed (n, d) := by
    simpa [search] using (Nat.rfind_dom (p := fun d => Part.some (decide (changed (n, d)))))
  -- Step 2.1 uses an index depending on the parameter and queries it at 0.
  -- Unary surjectivity supplies one index here, and the query input carries
  -- the packed triple. This recovers the test in FixedStageRowStability
  -- under the endpoint’s enumeration hypotheses and supplies the query
  -- argument required by the coded visits.
  obtain ⟨i, hi⟩ := surjective search hsearch
  refine ⟨Nat.pair i, (Primrec₂.natPair.comp (Primrec.const i) Primrec.id).to_comp, ?_⟩
  intro e x t
  rw [show Nat.pair i (Nat.pair e (Nat.pair x t)) ∉ haltingOracle φ ↔
    ¬ (φ i (Nat.pair e (Nat.pair x t))).Dom from not_congr (pair_mem_haltingOracle ..),
    hi, hdom, not_exists]
  simp only [changed, not_not, code, input, Nat.unpair_pair, Nat.add_zero,
    EmbeddingLike.apply_eq_iff_eq]
  constructor
  · intro h r hr
    simpa [Nat.add_sub_of_le hr] using h (r - t)
  · intro h d
    exact h (t + d) (Nat.le_add_right t d)

theorem finiteRowExhaustion
    {row : ℕ → Finset ℕ} {V : Set ℕ}
    (monotone : Monotone row) (union : ∀ y, y ∈ V ↔ ∃ s, y ∈ row s)
    (finite : V.Finite) :
    ∃ t, (↑(row t) : Set ℕ) = V ∧ ∀ r, t ≤ r → row r = row t := by
  classical
  let witness (y : ℕ) : ℕ := if hy : y ∈ V then ((union y).mp hy).choose else 0
  let t := finite.toFinset.sup witness
  have exhausted : (↑(row t) : Set ℕ) = V := by
    ext y
    constructor
    · intro hy
      exact (union y).mpr ⟨t, hy⟩
    · intro hy
      have hw : y ∈ row (witness y) := by
        rw [show witness y = ((union y).mp hy).choose by simp [witness, hy]]
        exact ((union y).mp hy).choose_spec
      exact monotone (Finset.le_sup (f := witness) (finite.mem_toFinset.mpr hy)) hw
  refine ⟨t, exhausted, fun r hr => Finset.Subset.antisymm ?_ (monotone hr)⟩
  intro y hy
  change y ∈ (↑(row t) : Set ℕ)
  rw [exhausted]
  exact (union y).mpr ⟨r, hy⟩

theorem stabilizedRow
    {row : ℕ → Finset ℕ} {V : Set ℕ} (monotone : Monotone row)
    (union : ∀ y, y ∈ V ↔ ∃ s, y ∈ row s)
    {t : ℕ} (stable : ∀ r, t ≤ r → row r = row t) :
    (↑(row t) : Set ℕ) = V := by
  ext y
  constructor
  · intro hy
    exact (union y).mpr ⟨t, hy⟩
  · intro hy
    obtain ⟨s, hs⟩ := (union y).mp hy
    have hm := monotone (le_max_left s t) hs
    rwa [stable (max s t) (le_max_right s t)] at hm

theorem rowGraphRE {V : ℕ → ℕ → Set ℕ}
    (graphRE : REPred (fun p : ℕ × ℕ × ℕ => p.2.2 ∈ V p.1 p.2.1)) (e : ℕ) :
    REPred (fun z : ℕ => z ∈ {z | ∃ x y, y ∈ V e x ∧ z = Nat.pair x y}) := by
  have decode : Computable (fun z : ℕ => (e, z.unpair)) :=
    (Computable.const e).pair Computable.unpair
  apply REPred.of_eq (graphRE.comp decode)
  intro z
  change z.unpair.2 ∈ V e z.unpair.1 ↔ ∃ x y, y ∈ V e x ∧ z = Nat.pair x y
  constructor
  · intro hz
    exact ⟨z.unpair.1, z.unpair.2, hz, (Nat.pair_unpair z).symm⟩
  · rintro ⟨x, y, h, rfl⟩
    simpa using h


def UpperCandidate (row : ℕ → ℕ → ℕ → Finset ℕ)
    (s e : ℕ) (Z : Set ℕ) (q : ℕ × ℕ) : Prop :=
  q.1 ≤ s ∧ q.2 ≤ s ∧
    (∀ m ∈ row e q.1 q.2, m ≤ s ∧ m ∉ Z) ∧
    ∀ r, q.2 ≤ r → row e q.1 r = row e q.1 q.2

/-- Laws needed for verification of the concrete bounded-visit construction.
The trace data themselves depend on the enumerations and admissible markers. -/
structure VerificationTrace (φ : ℕ → ℕ → Part ℕ)
    (row : ℕ → ℕ → ℕ → Finset ℕ) (M : Set ℕ) where
  content : ℕ → ℕ → Finset ℕ
  marker : ℕ → ℕ → ℕ → Option ℕ
  chosenPair : ℕ → ℕ → Option (ℕ × ℕ)
  done : ℕ → ℕ → Prop
  contentInitial : content 0 0 = ∅
  markerInitial : ∀ e, marker 0 0 e = none
  doneInitial : ∀ e, ¬ done 0 e
  contentCarry : ∀ s, content (s + 1) 0 = content s s
  contentPersists : ∀ s j k, j ≤ k → k ≤ s → content s j ⊆ content s k
  markerCarry : ∀ s e, marker (s + 1) 0 e = marker s s e
  doneNext : ∀ s e, done (s + 1) e ↔ done s e ∨ (chosenPair s e).isSome
  action : ∀ s e q, chosenPair s e = some q →
    2 * e < s ∧ ¬ done s e ∧
    UpperCandidate row s e {m | ∃ j, 2 * j + 1 < 2 * e ∧ marker s (2 * e) j = some m} q ∧
    row e q.1 q.2 ⊆ content s s
  upperProgress : ∀ s e q, 2 * e < s → ¬ done s e →
    UpperCandidate row s e {m | ∃ j, 2 * j + 1 < 2 * e ∧ marker s (2 * e) j = some m} q →
    (chosenPair s e).isSome
  lowerProgress : ∀ s e m, 2 * e + 1 < s → marker s (2 * e + 1) e = none →
    m ≤ s → m ∈ M → ¬ (φ e m).Dom → m ∉ content s (2 * e + 1) →
    (∀ j, marker s (2 * e + 1) j ≠ some m) → (marker s (2 * e + 2) e).isSome
  enterContent : ∀ s k m, k < s → m ∈ content s (k + 1) → m ∉ content s k →
    ∃ i q, k = 2 * i ∧ chosenPair s i = some q ∧ m ∈ row i q.1 q.2
  enterMarker : ∀ s k e m, k < s → marker s (k + 1) e = some m → marker s k e ≠ some m →
    k = 2 * e + 1 ∧ m ≤ s
  active : ∀ s k e m, k ≤ s → marker s k e = some m →
    m ∈ M ∧ ¬ (φ e m).Dom ∧ m ∉ content s k
  cancellation : ∀ s k e m, k < s → marker s k e = some m → marker s (k + 1) e = none →
    ∃ i q, k = 2 * i ∧ 2 * i < 2 * e + 1 ∧ chosenPair s i = some q
  noReplacement : ∀ s k e m, k < s → marker s k e = some m →
    marker s (k + 1) e = none ∨ marker s (k + 1) e = some m
  contentBound : ∀ s k m, m ∈ content s k → m ≤ s
  markerBound : ∀ s k e m, marker s k e = some m → m ≤ s

namespace VerificationTrace

variable {φ : ℕ → ℕ → Part ℕ} {row : ℕ → ℕ → ℕ → Finset ℕ} {M : Set ℕ}

def output (T : VerificationTrace φ row M) : Set ℕ :=
  {m | ∃ s, m ∈ T.content s s}

theorem once (T : VerificationTrace φ row M) (e s t : ℕ)
    (hs : ∃ q, T.chosenPair s e = some q) (ht : ∃ q, T.chosenPair t e = some q) : s = t := by
  obtain ⟨q, hq⟩ := hs
  obtain ⟨p, hp⟩ := ht
  have persists (u v : ℕ) (huv : u ≤ v) (h : T.done u e) : T.done v e := by
    induction v, huv using Nat.le_induction with
    | base => exact h
    | succ v _ ih => exact (T.doneNext v e).mpr (.inl ih)
  rcases lt_trichotomy s t with hl | he | hg
  · exact ((T.action t e p hp).2.1
      (persists (s + 1) t hl ((T.doneNext s e).mpr (.inr (by simp [hq]))))).elim
  · exact he
  · exact ((T.action s e q hq).2.1
      (persists (t + 1) s hg ((T.doneNext t e).mpr (.inr (by simp [hp]))))).elim

theorem stabilization (T : VerificationTrace φ row M) :
    (∀ e, ∃ s₀, ∀ s i, s₀ < s → 2 * i < 2 * e + 1 →
      ¬ ∃ q, T.chosenPair s i = some q) ∧
    (∀ e, ∃ s₁ final, ∀ s k, s₁ ≤ s → k ≤ s → T.marker s k e = final) ∧
    (∀ p, ∃ (s₁ : ℕ) (Z : Set ℕ), Z.Finite ∧ ∀ s k, s₁ ≤ s → k ≤ s →
      {m | ∃ e, 2 * e + 1 < p ∧ T.marker s k e = some m} = Z) := by
  -- §4, p. 9 charges each cancellation to a higher upper action.
  -- The trace supplier supplies that attribution and its permanent flags
  -- prove once-only action. The stabilization supplier needs neither the
  -- allocation criterion for markers nor how the searches are computed.
  have h := FiniteInjuryAndStabilization.of_trace
    (fun s e => ∃ q, T.chosenPair s e = some q) T.marker T.markerCarry T.once
    (fun s k e m hk hm hn => by
      obtain ⟨i, q, hki, hei, hq⟩ := T.cancellation s k e m hk hm hn
      exact ⟨i, hki, hei, q, hq⟩)
    T.noReplacement
  refine ⟨fun e => ?_, h.2.2.1, h.2.2.2⟩
  obtain ⟨s₀, hquiet, _, _⟩ := h.2.1 e
  exact ⟨s₀, hquiet⟩

theorem upper_met (T : VerificationTrace φ row M) (V : ℕ → ℕ → Set ℕ)
    (monotone : ∀ e x, Monotone (row e x))
    (union : ∀ e x y, y ∈ V e x ↔ ∃ s, y ∈ row e x s)
    (e : ℕ)
    (avoid : ∀ Z : Set ℕ, Z.Finite → Z ⊆ M →
      ∃ x, (V e x).Finite ∧ V e x ∩ Z = ∅) :
    ∃ x, (V e x).Finite ∧ V e x ⊆ T.output := by
  classical
  -- Cintioli, §4, p. 10, upper verification. First reduce to showing
  -- there was an action. The selected row is the full finite row by stability.
  suffices action : ∃ s q, T.chosenPair s e = some q by
    obtain ⟨s, q, hq⟩ := action
    obtain ⟨_, _, hcand, hcontent⟩ := T.action s e q hq
    have eq := stabilizedRow (monotone e q.1) (union e q.1) hcand.2.2.2
    refine ⟨q.1, eq ▸ Finset.finite_toSet _, ?_⟩
    intro m hm
    rw [← eq] at hm
    exact ⟨s, hcontent hm⟩
  by_contra absent
  have notDone (s : ℕ) : ¬ T.done s e := by
    induction s with
    | zero => exact T.doneInitial e
    | succ s ih =>
      intro hs
      rcases (T.doneNext s e).mp hs with hd | hq
      · exact ih hd
      · exact absent ⟨s, Option.isSome_iff_exists.mp hq⟩
  obtain ⟨S, Z, hfinite, hrestraints⟩ := T.stabilization.2.2 (2 * e)
  have hM : Z ⊆ M := by
    intro m hm
    rw [← hrestraints S 0 le_rfl (Nat.zero_le S)] at hm
    obtain ⟨j, _, hj⟩ := hm
    exact (T.active S 0 j m (Nat.zero_le S) hj).1
  obtain ⟨x, hfin, hdisjoint⟩ := avoid Z hfinite hM
  obtain ⟨t, heq, ht⟩ := finiteRowExhaustion (monotone e x) (union e x) hfin
  let s := max (max S (2 * e + 1)) (max (max x t) ((row e x t).sup id))
  have hS : S ≤ s := by dsimp [s]; omega
  have he : 2 * e < s := by dsimp [s]; omega
  have hs : UpperCandidate row s e
      {m | ∃ j, 2 * j + 1 < 2 * e ∧ T.marker s (2 * e) j = some m} (x, t) := by
    refine ⟨by dsimp [s]; omega, by dsimp [s]; omega, ?_, ht⟩
    intro m hm
    refine ⟨?_, ?_⟩
    · have bound : m ≤ (row e x t).sup id := Finset.le_sup (f := id) hm
      dsimp [s]
      omega
    · rw [hrestraints s (2 * e) hS he.le]
      intro hz
      have hv : m ∈ V e x := (union e x m).mpr ⟨t, hm⟩
      have hempty : m ∈ V e x ∩ Z := ⟨hv, hz⟩
      simp [hdisjoint] at hempty
  exact absent ⟨s, Option.isSome_iff_exists.mp (T.upperProgress s e (x, t) he (notDone s) hs)⟩

theorem lower_met (T : VerificationTrace φ row M) (e : ℕ)
    (unbounded : ∀ b, ∃ m, b < m ∧ m ∈ M ∧ ¬ (φ e m).Dom) :
    ∃ m, m ∈ M ∧ m ∉ T.output ∧ ¬ (φ e m).Dom := by
  classical
  -- Cintioli, §4, pp. 9–10, lower verification. Work after all higher
  -- actions, all higher restraints and the chosen lower strategy stabilize.
  obtain ⟨S₀, hquiet⟩ := T.stabilization.1 e
  obtain ⟨S₁, final, hfinal⟩ := T.stabilization.2.1 e
  obtain ⟨S₂, Z, hZ, hrestraints⟩ := T.stabilization.2.2 (2 * e + 1)
  let bound := max (max S₀ S₁) (max (max S₂ (2 * e + 1)) (hZ.toFinset.sup id))
  obtain ⟨m, hm, hM, hdom⟩ := unbounded bound
  have large₀ : S₀ < m := by dsimp [bound] at hm; omega
  have large₁ : S₁ ≤ m := by dsimp [bound] at hm; omega
  have large₂ : S₂ ≤ m := by dsimp [bound] at hm; omega
  let k := 2 * e + 1
  have visit : k < m := by dsimp [k, bound] at *; omega
  have freshContent (j : ℕ) (hj : j ≤ k) : m ∉ T.content m j := by
    induction j with
    | zero =>
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      rw [T.contentCarry]
      exact fun hc => by have := T.contentBound r r (r + 1) hc; omega
    | succ j ih =>
      intro hc
      obtain ⟨i, q, hi, hq, _⟩ := T.enterContent m j m (by omega) hc (ih (by omega))
      exact hquiet m i large₀ (by dsimp [k] at hj; omega) ⟨q, hq⟩
  have freshMarker (i : ℕ) : T.marker m k i ≠ some m := by
    by_cases higher : 2 * i + 1 < k
    · intro hmi
      have hz : m ∈ Z := by
        rw [← hrestraints m k large₂ visit.le]
        exact ⟨i, higher, hmi⟩
      have leZ : m ≤ hZ.toFinset.sup id := Finset.le_sup (f := id) (hZ.mem_toFinset.mpr hz)
      dsimp [bound] at hm
      omega
    · suffices ∀ j ≤ k, T.marker m j i ≠ some m from this k le_rfl
      intro j hj
      induction j with
      | zero =>
        obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
        rw [T.markerCarry]
        exact fun hmi => by have := T.markerBound r r i (r + 1) hmi; omega
      | succ j ih =>
        intro hmi
        have := (T.enterMarker m j i m (by omega) hmi (ih (by omega))).1
        omega
  have live : ∃ a, final = some a := by
    cases hmk : T.marker m k e with
    | some a => exact ⟨a, (hfinal m k large₁ visit.le).symm.trans hmk⟩
    | none =>
      have hnew := T.lowerProgress m e m visit hmk le_rfl hM hdom
        (freshContent k le_rfl) freshMarker
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hnew
      exact ⟨a, (hfinal m (2 * e + 2) large₁ (by dsimp [k] at visit; omega)).symm.trans ha⟩
  obtain ⟨a, ha⟩ := live
  have late (s : ℕ) (hs : S₁ ≤ s) := T.active s s e a le_rfl ((hfinal s s hs le_rfl).trans ha)
  refine ⟨a, (late m large₁).1, ?_, (late m large₁).2.1⟩
  rintro ⟨s, hs⟩
  -- A live final marker lies outside every sufficiently late content.
  -- Across-stage monotonicity carries any earlier entry to such a stage.
  have forward (s : ℕ) (hs : a ∈ T.content s s) : a ∈ T.content (s + 1) (s + 1) := by
    have start : a ∈ T.content (s + 1) 0 := by rwa [T.contentCarry]
    exact T.contentPersists (s + 1) 0 (s + 1) (Nat.zero_le _) le_rfl start
  have persisted : ∀ r, s ≤ r → a ∈ T.content r r := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base => exact hs
    | succ r _ ih => exact forward r ih
  exact (late (max s S₁) (le_max_right _ _)).2.2 (persisted _ (le_max_left _ _))

end VerificationTrace

/-- A total stage-code computation gives a semidecision by searching its stages. -/
theorem stageDomain {O : Set (ℕ →. ℕ)} (content : ℕ → Finset ℕ)
    (hcode : Nat.RecursiveIn O (fun s => Part.some (Finset.equivBitIndices.symm (content s)))) :
    ∃ f : ℕ →. ℕ, Nat.RecursiveIn O f ∧ ∀ m, (f m).Dom ↔ ∃ s, m ∈ content s := by
  -- Alphabeta Math, thm-sigma-one-sets-are-exactly-ce-sets, Step 1.1.
  -- https://alphabetamath.cc/item/thm-sigma-one-sets-are-exactly-ce-sets
  -- Replace the primitive-recursive matrix by the total oracle test from
  -- hcode and the bit test. Relative minimization searches these stage codes.
  let code (s : ℕ) := Finset.equivBitIndices.symm (content s)
  let test (n : ℕ) := bif n.unpair.1.testBit n.unpair.2 then 0 else 1
  have pow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := by
    apply Primrec₂.nat_iff.mpr
    simpa [Nat.unpaired] using Nat.Primrec.succ.comp Nat.Primrec.pow
  have testBit : Primrec₂ Nat.testBit := by
    apply (Primrec.eq.decide.comp
      (Primrec.nat_mod.comp (Primrec.nat_div.comp Primrec.fst
        (pow.comp (Primrec.const 2) Primrec.snd)) (Primrec.const 2)) (Primrec.const 1)).of_eq
    intro p
    exact Nat.testBit_eq_decide_div_mod_eq.symm
  have htest : Primrec test :=
    Primrec.cond (testBit.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.snd.comp Primrec.unpair)) (Primrec.const 0) (Primrec.const 1)
  have testRec : Nat.RecursiveIn O (fun n => Part.some (test n)) :=
    RecursiveIn.iff_nat.mp htest.computableIn
  have readCode : Nat.RecursiveIn O (fun n => Part.some (code n.unpair.2)) := by
    apply (hcode.comp (Nat.RecursiveIn.right (O := O))).of_eq
    intro n
    change (Part.some n.unpair.2).bind (fun s => Part.some (code s)) = _
    rw [Part.bind_some]
  let f (m : ℕ) := Nat.rfind fun s => Part.some ((code s).testBit m)
  have indicator : Nat.RecursiveIn O
      (fun n => Part.some (test (Nat.pair (code n.unpair.2) n.unpair.1))) := by
    apply (testRec.comp (readCode.pair Nat.RecursiveIn.left)).of_eq
    intro n
    change ((Part.some (Nat.pair (code n.unpair.2)) <*> Part.some n.unpair.1).bind
      (fun p => Part.some (test p))) = _
    rw [show (Part.some (Nat.pair (code n.unpair.2)) <*> Part.some n.unpair.1) =
        Part.some (Nat.pair (code n.unpair.2) n.unpair.1) from (pure_seq ..), Part.bind_some]
  refine ⟨f, indicator.rfind.of_eq ?_, ?_⟩
  · intro m
    dsimp [f]
    congr 1
    funext s
    simp only [Nat.unpair_pair, Part.map_some, test]
    cases (code s).testBit m <;> rfl
  · intro m
    have testMem (s : ℕ) : (code s).testBit m ↔ m ∈ content s := by
      rw [← Nat.mem_bitIndices, ← List.mem_toFinset, ← Finset.equivBitIndices_apply]
      simp [code]
    change (Nat.rfind fun s => Part.some ((code s).testBit m)).Dom ↔ _
    rw [Nat.rfind_dom (p := fun s => Part.some ((code s).testBit m))]
    constructor
    · rintro ⟨s, hs, _⟩
      exact ⟨s, (testMem s).mp (Part.mem_some_iff.mp hs).symm⟩
    · rintro ⟨s, hs⟩
      exact ⟨s, Part.mem_some_iff.mpr ((testMem s).mpr hs).symm, fun _ => Part.some_dom _⟩


/-- Assemble the reviewed endpoint once the concrete trace and its two
effectivity certificates are supplied. -/
theorem finish
    (φ : ℕ → ℕ → Part ℕ) (V : ℕ → ℕ → Set ℕ) (stage : ℕ → ℕ → ℕ → Finset ℕ)
    (hφ : Partrec₂ φ)
    (hV : REPred (fun p : ℕ × ℕ × ℕ => p.2.2 ∈ V p.1 p.2.1))
    (hmono : ∀ e x, Monotone (stage e x))
    (hunion : ∀ e x y, y ∈ V e x ↔ ∃ s, y ∈ stage e x s)
    (T : VerificationTrace φ stage Set.univ)
    (hce : (RelativeComputabilityAndEnumerability (haltingOracle φ)).2.1 T.output)
    (hsigma : {xs : Fin 1 → ℕ | xs 0 ∈ T.output} ∈
      (ArithmeticalHierarchyLevels 2 1 (Nat.le_succ 1)).1) :
  let levelTwo := _root_.ArithmeticalHierarchyLevels 2 1 (_root_.Nat.le_succ 1)
  let unary (B : _root_.Set _root_.Nat) : _root_.Set (_root_.Fin 1 → _root_.Nat) :=
    {xs | xs 0 ∈ B}
  let encode (n : _root_.Nat) := _root_.List.replicate n _root_.Bool.true
  let decode (w : _root_.List _root_.Bool) : _root_.Option _root_.Nat :=
    if encode (_root_.List.length w) = w then _root_.Option.some (_root_.List.length w)
    else _root_.Option.none
  let ce : _root_.Set _root_.Nat → Prop :=
    _root_.ComputablyEnumerableSet encode decode
      (_root_.List.replicate_left_injective _root_.Bool.true)
      (fun n => by simp [decode, encode])
      (fun w hw => _root_.ite_eq_right (fun h => hw ⟨_root_.List.length w, h⟩))
  ∃ N : _root_.Set _root_.Nat,
    let P : _root_.Set _root_.Nat := Nᶜ
    (_root_.RelativeComputabilityAndEnumerability (haltingOracle φ)).2.1 N ∧
    unary N ∈ levelTwo.1 ∧
    unary P ∈ levelTwo.2.1 ∧
    ∀ A : _root_.Set _root_.Nat,
      let cyl : _root_.Set _root_.Nat :=
        {z | ∃ x n : _root_.Nat, x ∈ A ∧ z = _root_.Nat.pair x n}
      ¬ _root_.ComputablePred (fun x : _root_.Nat => x ∈ A) →
      ¬ (_root_.OneOneReducible (fun x : _root_.Nat => x ∈ A) (fun x : _root_.Nat => x ∈ cyl) ∧
         _root_.OneOneReducible (fun x : _root_.Nat => x ∈ cyl) (fun x : _root_.Nat => x ∈ A)) →
      ¬ ce A →
      ¬ ce (Aᶜ) →
      let upper (e : _root_.Nat) : Prop :=
        (∀ x y : _root_.Nat, y ∈ V e x → (y ∈ A ↔ x ∈ A)) →
          ∃ x : _root_.Nat, _root_.Set.Finite (V e x) ∧ V e x ⊆ N
      let lower (e : _root_.Nat) : Prop :=
        (∀ x y : _root_.Nat, y ∈ φ e x → x < y ∧ (y ∈ A ↔ x ∈ A)) →
          ∃ m : _root_.Nat, m ∉ N ∪ {x : _root_.Nat | _root_.Part.Dom (φ e x)}
      ∀ p : _root_.Nat, if p % 2 = 0 then upper (p / 2) else lower (p / 2) := by
  -- Cintioli, arXiv:2609.00419v1, §4, pp. 8–10.
  -- https://arxiv.org/pdf/2609.00419v1#page=8
  -- The article-specific Alphabeta Math portal and defect report both
  -- returned HTTP 404. The numbered citations refer to the shared library.
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects
  intro levelTwo unary encode decode ce
  refine ⟨T.output, ?_⟩
  intro P
  refine ⟨hce, hsigma, ?_, ?_⟩
  · change ({xs : Fin 1 → ℕ | xs 0 ∈ T.output}ᶜᶜ : Set (Fin 1 → ℕ)) ∈
      (ArithmeticalHierarchyLevels 2 1 (Nat.le_succ 1)).1
    simpa using hsigma
  intro A cyl hnonrec hnoncyl hnonCE hncoCE upper lower p
  by_cases even : p % 2 = 0
  · rw [ite_eq_left even]
    intro homogeneous
    -- Lemma 2 consumes the c.e. graph with the true-bit encoding.
    -- ComputablyEnumerableSet.nat_rePred_iff implements the conversion.
    exact T.upper_met V hmono hunion (p / 2) fun Z hZ _ =>
      FiniteMarkerAvoidance A (V (p / 2)) hnoncyl hnonCE hncoCE
        ((ComputablyEnumerableSet.nat_rePred_iff true _).mp (rowGraphRE hV _))
        homogeneous Z hZ
  · rw [ite_eq_right even]
    intro ascending
    -- Lemma 4 applies to the partial-recursive e-th section of the
    -- supplied enumeration and gives arbitrarily large omitted inputs.
    have complementInfinite := CofiniteDomainLemma A (φ (p / 2)) hnonrec hnoncyl
      (hφ.comp (Computable.const (p / 2)) Computable.id) ascending
    obtain ⟨m, _, hm, hnotdom⟩ := T.lower_met (p / 2) fun b => by
      obtain ⟨m, hmdom, hmb⟩ := complementInfinite.exists_gt b
      exact ⟨m, hmb, Set.mem_univ m, hmdom⟩
    exact ⟨m, fun h => h.elim hm hnotdom⟩


/-- Read the verification data directly from the decoded visits. The
    construction and its invariants work for any admissible marker set. -/
def VerificationTrace.ofCoded {φ : ℕ → ℕ → Part ℕ}
    {row : PriorityCodedTrace.Rows} {M : Set ℕ}
    {U : PriorityCodedTrace.UpperSearch} {L : PriorityCodedTrace.LowerSearch}
    (laws : PriorityCodedTrace.Laws φ row M U L) : VerificationTrace φ row M where
  content := PriorityCodedTrace.content row U L
  marker := PriorityCodedTrace.marker row U L
  chosenPair := PriorityCodedTrace.chosenPair row U L
  done := PriorityCodedTrace.done row U L
  contentInitial := laws.contentInitial
  markerInitial := laws.markerInitial
  doneInitial := laws.doneInitial
  contentCarry := laws.contentCarry
  contentPersists := laws.contentPersists
  markerCarry := laws.markerCarry
  doneNext := laws.doneNext
  action := fun s e q hq => by
    -- The concrete upper search holds the higher markers in a bit mask.
    -- Its membership statement gives the set restraint used in §4, p. 10.
    obtain ⟨hvisit, hdone, hcand, hcontent⟩ := laws.action s e q hq
    exact ⟨hvisit, hdone,
      by simpa only [UpperCandidate, PriorityCodedTrace.UpperCandidate,
        PriorityCodedTrace.restraints, PriorityCodedTrace.memMarkerSet, Set.mem_ofPred_eq]
        using hcand,
      hcontent⟩
  upperProgress := fun s e q hvisit hdone hcand =>
    laws.upperProgress s e q hvisit hdone (by
      simpa only [UpperCandidate, PriorityCodedTrace.UpperCandidate,
        PriorityCodedTrace.restraints, PriorityCodedTrace.memMarkerSet, Set.mem_ofPred_eq]
        using hcand)
  lowerProgress := laws.lowerProgress
  enterContent := laws.enterContent
  enterMarker := laws.enterMarker
  active := fun s k e m _ hm => laws.active s k e m hm
  cancellation := fun s k e m hk hm hn => by
    obtain ⟨i, q, hi, hpriority, hq, _⟩ := laws.cancellation s k e m hk hm hn
    exact ⟨i, q, hi, hpriority, hq⟩
  noReplacement := laws.noReplacement
  contentBound := laws.contentBound
  markerBound := laws.markerBound

/-- Relative enumeration and the unary hierarchy bound for a trace with
    a recursive final-content code in the paired halting oracle. -/
theorem VerificationTrace.output_effective
    {φ : ℕ → ℕ → Part ℕ} {row : ℕ → ℕ → ℕ → Finset ℕ} {M : Set ℕ}
    (T : VerificationTrace φ row M) (hφ : Partrec₂ φ)
    (hcode : Nat.RecursiveIn
      {(by classical exact fun n => Part.some (if n ∈ haltingOracle φ then 1 else 0))}
      (fun s => Part.some (Finset.equivBitIndices.symm (T.content s s)))) :
    (RelativeComputabilityAndEnumerability (haltingOracle φ)).2.1 T.output ∧
      {xs : Fin 1 → ℕ | xs 0 ∈ T.output} ∈
        (ArithmeticalHierarchyLevels 2 1 (Nat.le_succ 1)).1 := by
  -- Article §4, p. 10 passes from finite stage actions to an oracle
  -- enumeration. Search the final contents using their total recursive-in-K
  -- code. The singleton compiler identifies the domain of that partial
  -- computation with an acceptance set in the reviewed tape model.
  obtain ⟨f, hf, hdom⟩ := stageDomain (fun s => T.content s s) hcode
  have heq : {m | (f m).Dom} = T.output := Set.ext hdom
  have hce : (RelativeComputabilityAndEnumerability (haltingOracle φ)).2.1 T.output := by
    rw [← heq]
    exact (SingletonOracleTapeCompilation (haltingOracle φ)).1 f hf
  -- Alphabeta Math, Post's theorem, Step 2.1, at n = 0.
  -- https://alphabetamath.cc/item/thm-posts-theorem
  -- The accepting-run supplier needs only that the oracle is c.e.
  -- haltingOracle_re supplies that hypothesis from the uniform φ.
  exact ⟨hce, CETapeOracleSigmaTwo (haltingOracle φ) T.output (haltingOracle_re φ hφ) hce⟩

/-- Build and certify a trace with the given computable pair order and
    halting-oracle-computable admissibility test for lower markers. -/
theorem existsEffectiveTrace
    (φ : ℕ → ℕ → Part ℕ) (row : PriorityCodedTrace.Rows)
    (M : Set ℕ) (pairBefore : (ℕ × ℕ) → (ℕ × ℕ) → Prop)
    (hφ : Partrec₂ φ)
    (hsurj : ∀ f : ℕ → Part ℕ, Partrec f → ∃ e, φ e = f)
    (hrow : Computable fun p : ℕ × ℕ × ℕ =>
      Finset.equivBitIndices.symm (row p.1 p.2.1 p.2.2))
    (horder : IsStrictTotalOrder (ℕ × ℕ) pairBefore)
    (hbefore : ComputablePred (fun p : (ℕ × ℕ) × (ℕ × ℕ) => pairBefore p.1 p.2))
    (hM : Nat.RecursiveIn
      {(by classical exact fun n => Part.some (if n ∈ haltingOracle φ then 1 else 0))}
      (by classical exact fun m => Part.some (if m ∈ M then 1 else 0))) :
    ∃ T : VerificationTrace φ row M,
      (RelativeComputabilityAndEnumerability (haltingOracle φ)).2.1 T.output ∧
      {xs : Fin 1 → ℕ | xs 0 ∈ T.output} ∈
        (ArithmeticalHierarchyLevels 2 1 (Nat.le_succ 1)).1 := by
  obtain ⟨query, hquery, hstable⟩ := stabilityQuery φ hsurj row hrow
  -- Keep the content code and visit laws from the same supplier witness.
  -- Its U and L already implement PriorityBoundedOracleSearches.
  obtain ⟨U, L, _, _, _, _, _, hcontent, _, laws⟩ :=
    PriorityCodedVisitTrace φ row pairBefore query M hrow horder hbefore hquery hstable hM
  exact ⟨VerificationTrace.ofCoded laws,
    (VerificationTrace.ofCoded laws).output_effective hφ hcontent⟩

end PriorityRequirements

theorem PriorityRequirements : (∀ (φ : _root_.Nat → _root_.Nat → _root_.Part _root_.Nat)
    (V : _root_.Nat → _root_.Nat → _root_.Set _root_.Nat)
    (stage : _root_.Nat → _root_.Nat → _root_.Nat → _root_.Finset _root_.Nat),
  _root_.Partrec₂ φ →
  (∀ f : _root_.Nat → _root_.Part _root_.Nat,
    _root_.Partrec f → ∃ e : _root_.Nat, φ e = f) →
  _root_.REPred (fun p : _root_.Nat × _root_.Nat × _root_.Nat =>
    p.2.2 ∈ V p.1 p.2.1) →
  (∀ i : _root_.Nat, ∃ e : _root_.Nat, ∀ x y : _root_.Nat,
    y ∈ V e x ↔ _root_.Part.Dom (φ i (_root_.Nat.pair x y))) →
  _root_.Computable (fun p : _root_.Nat × _root_.Nat × _root_.Nat =>
    (_root_.Equiv.symm _root_.Finset.equivBitIndices) (stage p.1 p.2.1 p.2.2)) →
  (∀ e x : _root_.Nat, _root_.Monotone (stage e x)) →
  (∀ e x y : _root_.Nat, y ∈ V e x ↔ ∃ s : _root_.Nat, y ∈ stage e x s) →
  let K : _root_.Set _root_.Nat := {n |
    let (e, x) := _root_.Nat.unpair n
    _root_.Part.Dom (φ e x)}
  let levelTwo := _root_.ArithmeticalHierarchyLevels 2 1 (_root_.Nat.le_succ 1)
  let unary (B : _root_.Set _root_.Nat) : _root_.Set (_root_.Fin 1 → _root_.Nat) :=
    {xs | xs 0 ∈ B}
  let encode (n : _root_.Nat) := _root_.List.replicate n _root_.Bool.true
  let decode (w : _root_.List _root_.Bool) : _root_.Option _root_.Nat :=
    if encode (_root_.List.length w) = w then _root_.Option.some (_root_.List.length w)
    else _root_.Option.none
  let ce : _root_.Set _root_.Nat → Prop :=
    _root_.ComputablyEnumerableSet encode decode
      (_root_.List.replicate_left_injective _root_.Bool.true)
      (fun n => by simp [decode, encode])
      (fun w hw => _root_.ite_eq_right (fun h => hw ⟨_root_.List.length w, h⟩))
  ∃ N : _root_.Set _root_.Nat,
    let P : _root_.Set _root_.Nat := Nᶜ
    (_root_.RelativeComputabilityAndEnumerability K).2.1 N ∧
    unary N ∈ levelTwo.1 ∧
    unary P ∈ levelTwo.2.1 ∧
    ∀ A : _root_.Set _root_.Nat,
      let cyl : _root_.Set _root_.Nat :=
        {z | ∃ x n : _root_.Nat, x ∈ A ∧ z = _root_.Nat.pair x n}
      ¬ _root_.ComputablePred (fun x : _root_.Nat => x ∈ A) →
      ¬ (_root_.OneOneReducible (fun x : _root_.Nat => x ∈ A) (fun x : _root_.Nat => x ∈ cyl) ∧
         _root_.OneOneReducible (fun x : _root_.Nat => x ∈ cyl) (fun x : _root_.Nat => x ∈ A)) →
      ¬ ce A →
      ¬ ce (Aᶜ) →
      let upper (e : _root_.Nat) : Prop :=
        (∀ x y : _root_.Nat, y ∈ V e x → (y ∈ A ↔ x ∈ A)) →
          ∃ x : _root_.Nat, _root_.Set.Finite (V e x) ∧ V e x ⊆ N
      let lower (e : _root_.Nat) : Prop :=
        (∀ x y : _root_.Nat, y ∈ φ e x → x < y ∧ (y ∈ A ↔ x ∈ A)) →
          ∃ m : _root_.Nat, m ∉ N ∪ {x : _root_.Nat | _root_.Part.Dom (φ e x)}
      ∀ p : _root_.Nat, if p % 2 = 0 then upper (p / 2) else lower (p / 2)) :=
(by
  intro φ V stage hφ hsurj hV _ hstage hmono hunion K
  -- Cintioli, arXiv:2609.00419v1, §4, pp. 8–10.
  -- https://arxiv.org/pdf/2609.00419v1#page=8
  -- Use the fixed computable order by pair codes and allow every number as
  -- a marker. The trace is selected before the hypotheses on A are used.
  -- Family coverage is used when applying these requirements to a newly
  -- constructed family. This endpoint verifies each family in the given list.
  let before (q r : ℕ × ℕ) : Prop := Nat.pair q.1 q.2 < Nat.pair r.1 r.2
  have horder : IsStrictTotalOrder (ℕ × ℕ) before :=
    Nat.pairEquiv.injective.isStrictTotalOrder_onFun (· < ·)
  have hpairCode : Primrec (fun q : ℕ × ℕ => Nat.pair q.1 q.2) :=
    Primrec₂.natPair.comp Primrec.fst Primrec.snd
  have hbefore : ComputablePred (fun p : (ℕ × ℕ) × (ℕ × ℕ) => before p.1 p.2) :=
    (Primrec.nat_lt.comp (hpairCode.comp Primrec.fst) (hpairCode.comp Primrec.snd)).computablePred
  have hM : Nat.RecursiveIn
      {(by classical exact fun n => Part.some (if n ∈ PriorityRequirements.haltingOracle φ then 1 else 0))}
      (fun m : ℕ => Part.some (@ite ℕ (m ∈ (Set.univ : Set ℕ)) (Classical.propDecidable _) 1 0)) := by
    have hconst : Nat.RecursiveIn
        {(by classical exact fun n => Part.some (if n ∈ PriorityRequirements.haltingOracle φ then 1 else 0))}
        (fun _ => Part.some 1) :=
      RecursiveIn.iff_nat.mp (Computable.const 1).computableIn
    refine hconst.of_eq fun m => ?_
    simp
  obtain ⟨T, hce, hsigma⟩ :=
    PriorityRequirements.existsEffectiveTrace φ stage Set.univ before
      hφ hsurj hstage horder hbefore hM
  exact PriorityRequirements.finish φ V stage hφ hV hmono hunion T hce hsigma)

#print axioms PriorityRequirements
