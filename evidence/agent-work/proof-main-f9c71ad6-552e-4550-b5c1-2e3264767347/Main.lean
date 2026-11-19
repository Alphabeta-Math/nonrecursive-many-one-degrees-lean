import Proofs.AcceptableNumbering
import Proofs.ArithmeticalHierarchyLevels

set_option maxHeartbeats 2000000

theorem HaltingSigmaOneCompleteness :
∀ φ : _root_.Nat → _root_.Nat → _root_.Part _root_.Nat,
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
        ∀ n : _root_.Nat, n ∈ A ↔ f n ∈ K :=
by
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
    -- matrix directly, without the general c.e./Σ₁ equivalence.
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
    exact (hdom n).symm
  -- The article-specific Alphabeta Math Research Portal and prerequisite
  -- defect report both returned HTTP 404. The cited shared-library proof
  -- steps come from https://alphabetamath.cc/item/thm-halting-is-sigma-one-complete.

#print axioms HaltingSigmaOneCompleteness
