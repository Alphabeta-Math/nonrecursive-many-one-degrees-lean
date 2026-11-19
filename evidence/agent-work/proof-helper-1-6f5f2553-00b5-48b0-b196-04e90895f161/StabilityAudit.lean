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

end PriorityRequirements

#print axioms PriorityRequirements.stabilityQuery

example (φ : Nat → Nat → Part Nat)
    (row : PriorityCodedTrace.Rows)
    (pairBefore : (Nat × Nat) → (Nat × Nat) → Prop)
    (M : Set Nat)
    (hsurj : ∀ f : Nat → Part Nat, Partrec f → ∃ i, φ i = f)
    (hrow : Computable fun p : Nat × Nat × Nat =>
      Finset.equivBitIndices.symm (row p.1 p.2.1 p.2.2))
    (horder : IsStrictTotalOrder (Nat × Nat) pairBefore)
    (hbefore : ComputablePred (fun p : (Nat × Nat) × (Nat × Nat) =>
      pairBefore p.1 p.2))
    (hM : Nat.RecursiveIn
      {(by classical exact fun n => Part.some (if n ∈ PriorityRequirements.haltingOracle φ then 1 else 0))}
      (by classical exact fun m => Part.some (if m ∈ M then 1 else 0))) :
    ∃ (U : PriorityCodedTrace.UpperSearch) (L : PriorityCodedTrace.LowerSearch),
      PriorityCodedTrace.Laws φ row M U L := by
  obtain ⟨query, hquery, hstable⟩ := PriorityRequirements.stabilityQuery φ hsurj row hrow
  obtain ⟨U, L, _, _, _, _, _, _, _, laws⟩ :=
    PriorityCodedVisitTrace φ row pairBefore query M hrow horder hbefore hquery hstable hM
  exact ⟨U, L, laws⟩

#print axioms PriorityCodedVisitTrace
