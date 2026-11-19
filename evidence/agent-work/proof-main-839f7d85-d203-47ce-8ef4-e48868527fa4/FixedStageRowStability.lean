import Mathlib
import Proofs.HaltingSigmaOneCompleteness
import Proofs.RelativeComputabilityAndEnumerability
import Proofs.AcceptableNumbering
import Proofs.OracleNegativePullbackDecision

theorem FixedStageRowStability : (∀ φ : _root_.Nat → _root_.Nat → _root_.Part _root_.Nat,
  _root_.AcceptableNumbering φ →
  ∀ stage : _root_.Nat → _root_.Nat → _root_.Nat → _root_.Finset _root_.Nat,
    _root_.Computable (fun p : _root_.Nat × _root_.Nat × _root_.Nat =>
      (_root_.Equiv.symm _root_.Finset.equivBitIndices)
        (stage p.1 p.2.1 p.2.2)) →
    (∀ e x : _root_.Nat, _root_.Monotone (stage e x)) →
    let V : _root_.Nat → _root_.Nat → _root_.Set _root_.Nat :=
      fun e x => {y | ∃ s : _root_.Nat, y ∈ stage e x s}
    (∀ i : _root_.Nat, ∃ e : _root_.Nat, ∀ x y : _root_.Nat,
      y ∈ V e x ↔ _root_.Part.Dom (φ i (_root_.Nat.pair x y))) →
    let K : _root_.Set _root_.Nat := {n |
      let (i, z) := _root_.Nat.unpair n
      _root_.Part.Dom (φ i z)}
    (_root_.RelativeComputabilityAndEnumerability K).1 {n |
      let (e, p) := _root_.Nat.unpair n
      let (x, t) := _root_.Nat.unpair p
      ∀ r : _root_.Nat, t ≤ r → stage e x r = stage e x t}) :=
(by
  -- Cintioli, arXiv:2609.00419v1, §4, p. 8, upper strategy:
  -- failure of stability at t is witnessed by a later stage with a different row.
  -- Monotonicity identifies such a change with a new entry. The stability test
  -- itself needs only computable stage codes, independently of row exhaustion.
  -- https://arxiv.org/pdf/2609.00419v1#page=8
  -- The article-specific Alphabeta Math collection and defect report returned
  -- HTTP 404. The numbered steps below refer to the shared-library proof.
  -- https://alphabetamath.cc/item/thm-halting-is-sigma-one-complete
  intro φ hφ stage hstage _hmonotone _V _hexhaustion
  classical
  -- Step 1.2 searches a total witness test. Here stage-code computability
  -- supplies the test directly, so a primitive-recursive matrix is unnecessary.
  -- The offset d ensures that every tested stage is at least t.
  let stageCode (n d : Nat) : Nat :=
    Finset.equivBitIndices.symm
      (stage n.unpair.1 n.unpair.2.unpair.1 (n.unpair.2.unpair.2 + d))
  have hcode : Computable₂ stageCode := by
    have houter : Computable (fun p : Nat × Nat => p.1.unpair) :=
      Computable.unpair.comp Computable.fst
    have hinner : Computable (fun p : Nat × Nat => p.1.unpair.2.unpair) :=
      Computable.unpair.comp (Computable.snd.comp houter)
    exact hstage.comp ((Computable.fst.comp houter).pair
      ((Computable.fst.comp hinner).pair
        (Primrec.nat_add.to_comp.comp (Computable.snd.comp hinner) Computable.snd)))
  let changed (n d : Nat) : Prop := stageCode n d ≠ stageCode n 0
  have hchanged : ComputablePred (fun p : Nat × Nat => changed p.1 p.2) :=
    ((Primrec.eq.decide.to_comp.comp hcode
      (hcode.comp Computable.fst (Computable.const 0))).computablePred).not
  -- Adapt TauCeti's ComputablePred.rePred_exists. Retain the partial
  -- function itself for indexing, and use totality to discharge the
  -- smaller-input domain premises of Nat.rfind_dom.
  let search (n : Nat) := Nat.rfind (fun d => Part.some (decide (changed n d)))
  have hsearch : Partrec search := Partrec.rfind hchanged.decide.partrec
  have hdomain (n : Nat) : (search n).Dom ↔ ∃ d : Nat, changed n d := by
    simpa [search] using
      (Nat.rfind_dom (p := fun d => Part.some (decide (changed n d))))
  -- Step 2.1 hard-wires the parameter into the index and queries at 0.
  -- Surjectivity of the reviewed numbering gives one fixed search index i.
  -- Carry the packed triple as its input, so the query map is n ↦ ⟨i, n⟩.
  -- This proves the needed halting reduction directly. The compiled tape
  -- decision theorem implements the negative answer in the reviewed model.
  obtain ⟨i, hi⟩ := hφ.2.1 search hsearch
  intro K
  have hquery := OracleNegativePullbackDecision K (Nat.pair i)
    (Primrec₂.natPair.comp (Primrec.const i) Primrec.id).to_comp
  convert hquery using 1
  ext n
  change (∀ r : Nat, n.unpair.2.unpair.2 ≤ r →
    stage n.unpair.1 n.unpair.2.unpair.1 r =
      stage n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2) ↔
    ¬ (φ (Nat.pair i n).unpair.1 (Nat.pair i n).unpair.2).Dom
  rw [Nat.unpair_pair]
  change _ ↔ ¬ (φ i n).Dom
  rw [hi, hdomain, not_exists]
  -- The binary code is injective. Recover every r ≥ t with d = r - t.
  simp only [changed, not_not, stageCode, Nat.add_zero, EmbeddingLike.apply_eq_iff_eq]
  constructor
  · intro h d
    exact h _ (Nat.le_add_right _ _)
  · intro h r hr
    simpa [Nat.add_sub_of_le hr] using h (r - n.unpair.2.unpair.2))

#check OracleNegativePullbackDecision
#print axioms OracleNegativePullbackDecision
#print axioms FixedStageRowStability
