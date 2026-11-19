import Mathlib
import Proofs.HaltingSigmaOneCompleteness
import Proofs.RelativeComputabilityAndEnumerability
import Proofs.AcceptableNumbering

set_option maxHeartbeats 2000000

section
variable (bridge : ∀ (X : Set Nat) (f : Nat → Nat), Computable f →
  (RelativeComputabilityAndEnumerability X).1 {n | f n ∉ X})
include bridge

namespace FixedStageRowStability

/-- The fixed-stage decision needs only a numbering that includes every unary
partial recursive function and a computable code for each finite stage. -/
theorem of_surjective
    {φ : Nat → Nat → Part Nat}
    (hsurj : ∀ f : Nat → Part Nat, Partrec f → ∃ e, φ e = f)
    {stage : Nat → Nat → Nat → Finset Nat}
    (hstage : Computable (fun p : Nat × Nat × Nat =>
      Finset.equivBitIndices.symm (stage p.1 p.2.1 p.2.2))) :
    let K : Set Nat := {n | let (i, z) := n.unpair; (φ i z).Dom}
    (RelativeComputabilityAndEnumerability K).1 {n |
      let (e, p) := n.unpair
      let (x, t) := p.unpair
      ∀ r : Nat, t ≤ r → stage e x r = stage e x t} := by
  -- Cintioli, arXiv:2609.00419v1, §4, p. 8, upper strategy.
  -- https://arxiv.org/pdf/2609.00419v1#page=8
  -- The article-specific Alphabeta Math collection and defect report both returned HTTP 404.
  -- Following Alphabeta Math's halting-completeness proof, step 1.2, search
  -- for a witness using a total test. The hypothesis supplies computable
  -- stage codes. Search the offset d from t to impose r ≥ t.
  -- https://alphabetamath.cc/item/thm-halting-is-sigma-one-complete
  classical
  let stageCode (n d : Nat) : Nat :=
    Finset.equivBitIndices.symm
      (stage n.unpair.1 n.unpair.2.unpair.1 (n.unpair.2.unpair.2 + d))
  have hcode : Computable₂ stageCode := by
    have hpair : Computable (fun p : Nat × Nat => p.1.unpair) :=
      Primrec.unpair.to_comp.comp Computable.fst
    have hrowStage : Computable (fun p : Nat × Nat => p.1.unpair.2.unpair) :=
      Primrec.unpair.to_comp.comp (Computable.snd.comp hpair)
    exact hstage.comp ((Computable.fst.comp hpair).pair
      ((Computable.fst.comp hrowStage).pair
        (Primrec.nat_add.to_comp.comp (Computable.snd.comp hrowStage) Computable.snd)))
  let changed (n d : Nat) : Prop := stageCode n d ≠ stageCode n 0
  have hchanged : ComputablePred (fun p : Nat × Nat => changed p.1 p.2) :=
    ((Primrec.eq.decide.to_comp.comp hcode
      (hcode.comp Computable.fst (Computable.const 0))).computablePred).not
  -- Adapt TauCeti's ComputablePred.rePred_exists by retaining the natural
  -- output of minimization for the subsequent use of unary surjectivity.
  let search (n : Nat) := Nat.rfind (fun d => Part.some (decide (changed n d)))
  have hsearch : Partrec search := Partrec.rfind hchanged.decide.partrec
  have hdomain (n : Nat) : (search n).Dom ↔ ∃ d : Nat, changed n d := by
    simpa [search] using
      (Nat.rfind_dom (p := fun d => Part.some (decide (changed n d))))
  -- For step 2.1, pass the entire packed triple as input to one unary search.
  -- Surjectivity supplies a single index for that search. This is the
  -- specialization of the halting reduction to these stage codes, using
  -- computability directly and skipping the conversion to a primitive-recursive
  -- Σ₁ matrix. The tape theorem implements the negative answer to the query.
  obtain ⟨i, hi⟩ := hsurj search hsearch
  intro K
  have hquery := bridge K (Nat.pair i)
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
  simp only [changed, not_not, stageCode, Nat.add_zero, EmbeddingLike.apply_eq_iff_eq]
  constructor
  · intro h d
    exact h _ (Nat.le_add_right _ _)
  · intro h r hr
    simpa [Nat.add_sub_of_le hr] using h (r - n.unpair.2.unpair.2)

end FixedStageRowStability

theorem fixedStageRowStabilityAfterBridge : (∀ φ : _root_.Nat → _root_.Nat → _root_.Part _root_.Nat,
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
  intro φ hφ stage hstage _hmonotone _V _hexhaustion
  -- Monotonicity and exhaustion describe the family of c.e. rows. The
  -- decision at the specified stage uses just the computable stage codes.
  exact FixedStageRowStability.of_surjective bridge hφ.2.1 hstage)

end

#check fixedStageRowStabilityAfterBridge
#print axioms fixedStageRowStabilityAfterBridge
