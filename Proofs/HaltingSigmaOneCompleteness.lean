import Mathlib

import Proofs.AcceptableNumbering
import Proofs.ArithmeticalHierarchyLevels

set_option maxHeartbeats 2000000

namespace HaltingSigmaOneCompleteness

/- Cintioli, arXiv:2609.00419v1, §4, p. 8, fixes effective enumerations
   of the partial functions and uniformly c.e. families, with uniformly
   computable increasing finite stages. The canonical enumeration below
   supplies those data. https://arxiv.org/pdf/2609.00419v1#page=8 -/

/-- The numbering of unary partial recursive functions by mathlib codes. -/
noncomputable def canonicalNumbering (e x : Nat) : Part Nat :=
  (Denumerable.ofNat Nat.Partrec.Code e).eval x

theorem canonicalNumbering_acceptable : AcceptableNumbering canonicalNumbering := by
  have huniversal : Partrec₂ canonicalNumbering := by
    change Partrec (fun p : Nat × Nat => (Denumerable.ofNat Nat.Partrec.Code p.1).eval p.2)
    exact Nat.Partrec.Code.eval_part.comp ((Computable.ofNat _).comp Computable.fst) Computable.snd
  refine ⟨fun e => huniversal.comp (Computable.const e) Computable.id, ?_, huniversal, ?_⟩
  · intro f hf
    obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hf)
    refine ⟨Encodable.encode c, ?_⟩
    unfold canonicalNumbering
    rw [Denumerable.ofNat_encode, hc]
  · -- Code.smn expects Nat.pair on its input. Compute the reviewed
    -- two-entry sequence code before calling the original evaluator.
    let G (n : Nat) : Part Nat :=
      let e := n.unpair.1.unpair.1
      let a := n.unpair.1.unpair.2
      let x := n.unpair.2
      let appendEntry (initialWord entry : Nat) : Nat :=
        let place := 2 ^ (Nat.log2 entry + 1)
        let withLength := initialWord * place + (place - 1)
        withLength * (2 * place) + entry
      canonicalNumbering e (appendEntry (appendEntry 0b1110 a) x)
    have hleft : Computable (fun n : Nat => n.unpair.1.unpair) :=
      Primrec.unpair.to_comp.comp ((Primrec.fst.comp Primrec.unpair).to_comp)
    have hG : Partrec G :=
      huniversal.comp (Computable.fst.comp hleft)
        (AcceptableNumbering.computable₂_sequenceCode.comp (Computable.snd.comp hleft)
          (Primrec.snd.comp Primrec.unpair).to_comp)
    obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hG)
    obtain ⟨specialize, hspecialize, heval⟩ := Nat.Partrec.Code.smn
    refine ⟨fun e a => Encodable.encode (specialize c (Nat.pair e a)), ?_, ?_⟩
    · exact Computable.encode.comp₂
        (hspecialize.comp₂ (Computable.const c) Primrec₂.natPair.to_comp)
    · intro e a x
      simp only [canonicalNumbering, Denumerable.ofNat_encode, heval, hc, G, Nat.unpair_pair]

/-- The row of the c.e. graph coded by e at x. -/
def row (e x : Nat) : Set Nat :=
  {y | (canonicalNumbering e (Nat.pair x y)).Dom}

/-- At stage s, retain y < s for which the packed input halts with fuel s. -/
def rowAt (e x s : Nat) : Finset Nat :=
  (Finset.range s).filter (fun y =>
    (Nat.Partrec.Code.evaln s (Denumerable.ofNat Nat.Partrec.Code e) (Nat.pair x y)).isSome)

theorem monotone_rowAt (e x : Nat) : Monotone (rowAt e x) := by
  intro s t hst y
  simp only [rowAt, Finset.mem_filter, Finset.mem_range, Option.isSome_iff_exists]
  rintro ⟨hy, z, hz⟩
  exact ⟨lt_of_lt_of_le hy hst, z, Nat.Partrec.Code.evaln_mono hst hz⟩

theorem mem_row_iff_exists_stage (e x y : Nat) :
    y ∈ row e x ↔ ∃ s, y ∈ rowAt e x s := by
  change (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code e) (Nat.pair x y)).Dom ↔ _
  simp only [Part.dom_iff_mem, Nat.Partrec.Code.evaln_complete, rowAt, Finset.mem_filter,
    Finset.mem_range, Option.isSome_iff_exists]
  constructor
  · rintro ⟨z, s, hz⟩
    exact ⟨max s (y + 1), lt_of_lt_of_le (Nat.lt_succ_self y) (le_max_right _ _), z,
      Nat.Partrec.Code.evaln_mono (le_max_left _ _) hz⟩
  · rintro ⟨s, _, z, hz⟩
    exact ⟨z, s, hz⟩

/--
The binary code is a bounded sum over y, keeping e, x and the fuel s fixed
throughout the recursion. TauCeti's optional domStage suppliers operate on
unary code inputs. These stages evaluate the paired input and sum powers
with exponent y directly, producing row codes on the required triple.
-/
theorem computable_rowAt_code :
    Computable (fun p : Nat × Nat × Nat => Finset.equivBitIndices.symm (rowAt p.1 p.2.1 p.2.2)) := by
  let test (p : Nat × Nat × Nat) (y : Nat) : Bool :=
    (Nat.Partrec.Code.evaln p.2.2 (Denumerable.ofNat Nat.Partrec.Code p.1)
      (Nat.pair p.2.1 y)).isSome
  have htest : Primrec₂ test := by
    change Primrec (fun q : (Nat × Nat × Nat) × Nat => test q.1 q.2)
    have fuel : Primrec (fun q : (Nat × Nat × Nat) × Nat => q.1.2.2) :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
    have code : Primrec (fun q : (Nat × Nat × Nat) × Nat =>
        Denumerable.ofNat Nat.Partrec.Code q.1.1) :=
      (Primrec.ofNat _).comp (Primrec.fst.comp Primrec.fst)
    have input : Primrec (fun q : (Nat × Nat × Nat) × Nat => Nat.pair q.1.2.1 q.2) :=
      Primrec₂.natPair.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
    exact Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp ((fuel.pair code).pair input))
  let term (p : Nat × Nat × Nat) (y : Nat) : Nat := bif test p y then 2 ^ y else 0
  have hterm : Primrec₂ term := by
    change Primrec (fun q : (Nat × Nat × Nat) × Nat => term q.1 q.2)
    have pow : Primrec₂ ((· ^ ·) : Nat → Nat → Nat) :=
      Primrec₂.unpaired'.mp Nat.Primrec.pow
    exact Primrec.cond htest (pow.comp (Primrec.const 2) Primrec.snd) (Primrec.const 0)
  have hstep : Primrec₂ (fun (p : Nat × Nat × Nat) (q : Nat × Nat) => q.2 + term p q.1) :=
    Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
      (hterm.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
  have hsum (p : Nat × Nat × Nat) (k : Nat) :
      Nat.rec 0 (fun y acc => acc + term p y) k = ∑ y ∈ Finset.range k, term p y := by
    induction k with
    | zero => simp
    | succ k ih =>
      change Nat.rec 0 (fun y acc => acc + term p y) k + term p k = _
      rw [Finset.sum_range_succ, ih]
  refine (Primrec.nat_rec' (Primrec.snd.comp Primrec.snd) (Primrec.const 0) hstep).to_comp.of_eq ?_
  intro p
  rw [hsum, Finset.equivBitIndices_symm_apply, rowAt, Finset.sum_filter]
  exact Finset.sum_congr rfl fun y _ => by cases test p y <;> simp [term, test, *]

/-- Each numbered partial domain occurs among the unions of stage rows. -/
theorem rowAt_exhausts_numbering (i : Nat) :
    ∃ e : Nat, ∀ x y : Nat, (∃ s, y ∈ rowAt e x s) ↔
      (canonicalNumbering i (Nat.pair x y)).Dom :=
  ⟨i, fun x y => (mem_row_iff_exists_stage i x y).symm⟩

/-- Every c.e. predicate of packed pairs is exhausted by a single index. -/
theorem exists_index_stages {P : Nat → Prop} (hP : REPred P) :
    ∃ e : Nat, ∀ x y : Nat, P (Nat.pair x y) ↔ ∃ s, y ∈ rowAt e x s := by
  -- A total continuation replaces the semidecider's Unit output with 0.
  -- The domain is preserved, so code selection applies to a Nat output.
  let f (n : Nat) := (Part.assert (P n) (fun _ => Part.some ())).bind (fun _ => Part.some (0 : Nat))
  have hf : Partrec f := Partrec.bind hP (Computable.const (0 : Nat)).partrec
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hf)
  refine ⟨Encodable.encode c, fun x y => (Iff.trans ?_ (mem_row_iff_exists_stage _ x y))⟩
  change P (Nat.pair x y) ↔ (canonicalNumbering (Encodable.encode c) (Nat.pair x y)).Dom
  by_cases h : P (Nat.pair x y) <;> simp [canonicalNumbering, hc, f, Part.assert_pos, Part.assert_neg, h]

end HaltingSigmaOneCompleteness

theorem HaltingSigmaOneCompleteness : (∀ φ : _root_.Nat → _root_.Nat → _root_.Part _root_.Nat,
  _root_.AcceptableNumbering φ →
  let K : _root_.Set _root_.Nat := {n |
    let p := _root_.Nat.unpair n
    _root_.Part.Dom (φ (_root_.Prod.fst p) (_root_.Prod.snd p))}
  let sigmaOne : _root_.Set _root_.Nat → Prop := fun A =>
    _root_.Set.preimage (fun xs : _root_.Fin 1 → _root_.Nat => xs 0) A ∈
      _root_.Prod.fst (_root_.ArithmeticalHierarchyLevels 1 1 (_root_.Nat.le_refl 1))
  sigmaOne K ∧
    ∀ A : _root_.Set _root_.Nat, sigmaOne A →
      ∃ f : _root_.Nat → _root_.Nat, _root_.Computable f ∧
        ∀ n : _root_.Nat, n ∈ A ↔ f n ∈ K) :=
(by
  -- Alphabeta Math, thm-halting-is-sigma-one-complete, Proof.
  -- https://alphabetamath.cc/item/thm-halting-is-sigma-one-complete
  -- The article-specific Research Portal and defect-report routes returned HTTP 404.
  -- TauCeti's rePred_iff_exists_code and rePred_exists concern REPred.
  -- Here code selection and total Boolean minimization directly connect
  -- the universal partial function and the reviewed primitive-recursive matrix.
  classical
  intro φ hφ K sigmaOne
  obtain ⟨_, hsurj, huniversal, _⟩ := hφ
  have hSigma (A : Set Nat) :
      sigmaOne A ↔ ∃ R : (Fin 1 → Nat) → (Fin 1 → Nat) → Prop,
        PrimrecRel R ∧ ∀ xs : Fin 1 → Nat, xs 0 ∈ A ↔
          ∃ y : Nat, R xs (Fin.cons y Fin.elim0) := by
    rfl
  constructor
  · -- Alphabeta Math, thm-halting-is-sigma-one-complete, step 1.1.
    -- Joint partial recursiveness applies after decoding the input pair.
    -- Bounded evaluation of a code gives the required primitive-recursive
    -- matrix directly in the reviewed singleton-tuple encoding.
    have hpacked : Partrec (fun n : Nat => φ n.unpair.1 n.unpair.2) :=
      huniversal.comp (Primrec.fst.comp Primrec.unpair).to_comp
        (Primrec.snd.comp Primrec.unpair).to_comp
    obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hpacked)
    have hcoord : Primrec (fun xs : Fin 1 → Nat => xs 0) :=
      Primrec.fin_app.comp Primrec.id (Primrec.const 0)
    have htest : Primrec (fun p : (Fin 1 → Nat) × (Fin 1 → Nat) =>
        (Nat.Partrec.Code.evaln (p.2 0) c (p.1 0)).isSome) :=
      Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp
        (((hcoord.comp Primrec.snd).pair (Primrec.const c)).pair (hcoord.comp Primrec.fst)))
    apply (hSigma K).mpr
    refine ⟨fun xs ys => (Nat.Partrec.Code.evaln (ys 0) c (xs 0)).isSome, ?_, ?_⟩
    · exact Primrec.eq.comp htest (Primrec.const true)
    · intro xs
      change (φ (xs 0).unpair.1 (xs 0).unpair.2).Dom ↔
        ∃ y : Nat, (Nat.Partrec.Code.evaln y c (xs 0)).isSome = true
      rw [← congrFun hc (xs 0), Part.dom_iff_mem]
      simp only [Nat.Partrec.Code.evaln_complete, Option.isSome_iff_exists, Option.mem_def]
      exact exists_comm
  · -- Step 1.2. Use the given primitive-recursive matrix on singleton
    -- tuples. Minimization is valid because every witness test is total.
    intro A hA
    obtain ⟨R, hR, hmem⟩ := (hSigma A).mp hA
    let singleton (n : Nat) : Fin 1 → Nat := Fin.cons n Fin.elim0
    have hsingleton : Primrec singleton := by
      apply Primrec.fin_curry.mpr
      convert (Primrec₂.left : Primrec₂ (fun n : Nat => fun _ : Fin 1 => n)) using 1
      funext n i
      rw [Fin.eq_zero i]
      rfl
    let P (n y : Nat) := R (singleton n) (singleton y)
    have hP : ComputablePred (fun p : Nat × Nat => P p.1 p.2) :=
      PrimrecPred.computablePred (hR.comp (hsingleton.comp Primrec.fst) (hsingleton.comp Primrec.snd))
    let search (n : Nat) := Nat.rfind (fun y => Part.some (decide (P n y)))
    have hsearch : Partrec search := Partrec.rfind hP.decide.partrec
    have hdom (n : Nat) : (search n).Dom ↔ n ∈ A := by
      rw [show (search n).Dom ↔ ∃ y, P n y from by
        simpa [search] using (Nat.rfind_dom (p := fun y => Part.some (decide (P n y))))]
      exact (hmem (singleton n)).symm
    -- Step 2.1 uses n ↦ ⟨eₙ, 0⟩ after hard-wiring n in step 1.2.
    -- Here surjectivity supplies a single index for the unary search, so
    -- the computable reduction carries n in the input as n ↦ ⟨e, n⟩.
    obtain ⟨e, he⟩ := hsurj search hsearch
    refine ⟨Nat.pair e, Primrec₂.natPair.comp (Primrec.const e) Primrec.id |>.to_comp, ?_⟩
    intro n
    change n ∈ A ↔ (φ (Nat.unpair (Nat.pair e n)).1 (Nat.unpair (Nat.pair e n)).2).Dom
    rw [Nat.unpair_pair, he]
    exact (hdom n).symm)
