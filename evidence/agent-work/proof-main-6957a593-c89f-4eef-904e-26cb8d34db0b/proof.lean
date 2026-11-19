by
  classical
  intro φ rowAt pairBefore query M K oracle hrow horder hbefore hquery hstable hM
    upperCandidate lowerCandidate
  -- The coordinator passes the computable query map and its pointwise stability law.
  -- The terminal tape decision has a different interface. The two scans use the
  -- native singleton oracle for repeated queries. Taking M = Set.univ recovers
  -- the marker eligibility of Cintioli's construction, independently of A.
  let Rel := PriorityBoundedSearch.OracleTotal oracle
  have liftOrdinary {f : Nat → Nat} (hf : Computable f) : Rel f :=
    PriorityBoundedSearch.liftOrdinary hf
  have relComp {f g : Nat → Nat} (hf : Rel f) (hg : Rel g) :
      Rel (fun n => f (g n)) := PriorityBoundedSearch.relComp hf hg
  have rel₂ {f g : Nat → Nat} {op : Nat → Nat → Nat} (hop : Computable₂ op)
      (hf : Rel f) (hg : Rel g) : Rel (fun n => op (f n) (g n)) :=
    PriorityBoundedSearch.rel₂ hop hf hg
  let answer (n : Nat) : Nat := if n ∈ K then 1 else 0
  have hanswer : Rel answer := Nat.RecursiveIn.oracle _ (Set.mem_singleton _)
  have answerZero (n : Nat) : answer n = 0 ↔ n ∉ K := by simp [answer]
  let admissible (m : Nat) : Nat := if m ∈ M then 1 else 0
  have admissibleOne (m : Nat) : admissible m = 1 ↔ m ∈ M := by simp [admissible]

  let req (a : Nat) := a.unpair.1
  let stage (a : Nat) := a.unpair.2.unpair.1
  let masks (a : Nat) := a.unpair.2.unpair.2
  have hreq : Computable req := Computable.fst.comp Computable.unpair
  have hparams : Computable (fun a : Nat => a.unpair.2.unpair) :=
    Computable.unpair.comp (Computable.snd.comp Computable.unpair)
  have hstage : Computable stage := Computable.fst.comp hparams
  have hmasks : Computable masks := Computable.snd.comp hparams
  have hinput : Computable (fun p : Nat => Nat.pair (req p.unpair.1) p.unpair.2) :=
    Primrec₂.natPair.to_comp.comp (hreq.comp (Computable.fst.comp Computable.unpair))
      (Computable.snd.comp Computable.unpair)
  let upperBefore (i j : Nat) := pairBefore i.unpair j.unpair
  have hupperBefore : ComputablePred (fun p : Nat × Nat => upperBefore p.1 p.2) := by
    have hdecode : Computable (fun p : Nat × Nat => (p.1.unpair, p.2.unpair)) :=
      (Computable.unpair.comp Computable.fst).pair (Computable.unpair.comp Computable.snd)
    exact (hbefore.decide.comp hdecode).computablePred
  let upperBound (a : Nat) := (stage a + 1) ^ 2
  have hupperBound : Computable upperBound := by
    have h := Computable.succ.comp hstage
    exact (Primrec.nat_mul.to_comp.comp h h).of_eq (fun a => by simp only [upperBound, pow_two])
  let upperTest (a i : Nat) := PriorityBoundedSearch.gate (answer (query (Nat.pair (req a) i)))
    (if PriorityBoundedSearch.fits (Finset.equivBitIndices.symm (rowAt (req a) i.unpair.1 i.unpair.2),
      stage a, masks a) then 1 else 0)
  have hupperTest : Rel (fun p => upperTest p.unpair.1 p.unpair.2) := by
    have ha : Computable (fun p : Nat => p.unpair.1) := Computable.fst.comp Computable.unpair
    have hq : Computable (fun p : Nat => p.unpair.2.unpair) :=
      Computable.unpair.comp (Computable.snd.comp Computable.unpair)
    have hc := hrow.comp ((hreq.comp ha).pair hq)
    have hf := PriorityBoundedSearch.hfits.decide.to_comp.comp (hc.pair ((hstage.comp ha).pair (hmasks.comp ha)))
    have hflag := Computable.cond hf (Computable.const (1 : Nat)) (Computable.const 0)
    refine (rel₂ PriorityBoundedSearch.hgate (relComp hanswer (liftOrdinary (hquery.comp hinput)))
      (liftOrdinary hflag)).of_eq ?_
    intro p
    simp [upperTest, Bool.cond_eq_ite]
  let upperInput (e s z : Nat) := Nat.pair e (Nat.pair s z)
  have upperSpec (e s z i : Nat) :
      (i < upperBound (upperInput e s z) ∧ upperTest (upperInput e s z) i = 1) ↔
        upperCandidate e s (Finset.equivBitIndices z) i.unpair := by
    have hi := PriorityBoundedSearch.square s i.unpair
    rw [Nat.pair_unpair] at hi
    have hs := hstable e i.unpair.1 i.unpair.2
    rw [Nat.pair_unpair] at hs
    simp only [upperCandidate, upperBound, upperTest, upperInput, req, stage, masks,
      Nat.unpair_pair, PriorityBoundedSearch.gateOne, answerZero, ite_eq_left_iff, Nat.zero_ne_one,
      imp_false, not_not, PriorityBoundedSearch.fits, Equiv.apply_symm_apply, hi, hs]
    constructor
    · rintro ⟨⟨hx, ht⟩, hstable, PriorityBoundedSearch.hfits⟩
      exact ⟨hx, ht, PriorityBoundedSearch.hfits, hstable⟩
    · rintro ⟨hx, ht, PriorityBoundedSearch.hfits, hstable⟩
      exact ⟨⟨hx, ht⟩, hstable, PriorityBoundedSearch.hfits⟩

  let lowerBound (a : Nat) := (stage a).succ
  let lowerFree (a m : Nat) : Prop :=
    m ∉ Finset.equivBitIndices (masks a).unpair.1 ∧
    m ∉ Finset.equivBitIndices (masks a).unpair.2
  let lowerTest (a m : Nat) := PriorityBoundedSearch.gate
    (answer (Nat.pair (req a) m) + (if lowerFree a m then 0 else 1)) (admissible m)
  have hlowerTest : Rel (fun p => lowerTest p.unpair.1 p.unpair.2) := by
    have hm : Computable (fun p : Nat => p.unpair.2) := Computable.snd.comp Computable.unpair
    have hc := Computable.unpair.comp (hmasks.comp (Computable.fst.comp Computable.unpair))
    have hfree : Computable (fun p : Nat => decide (lowerFree p.unpair.1 p.unpair.2)) := by
      have h₁ := Primrec.not.to_comp.comp (PriorityBoundedSearch.testBit.to_comp.comp (Computable.fst.comp hc) hm)
      have h₂ := Primrec.not.to_comp.comp (PriorityBoundedSearch.testBit.to_comp.comp (Computable.snd.comp hc) hm)
      refine (Primrec.and.to_comp.comp h₁ h₂).of_eq ?_
      intro p
      simp [lowerFree]
    have hreject := rel₂ Primrec.nat_add.to_comp (relComp hanswer (liftOrdinary hinput))
      (liftOrdinary (Computable.cond hfree (Computable.const (0 : Nat)) (Computable.const 1)))
    exact (rel₂ PriorityBoundedSearch.hgate hreject (relComp (f := admissible) hM (liftOrdinary hm))).of_eq (fun p => by
      simp [lowerTest, Bool.cond_eq_ite])
  let lowerInput (e s c a : Nat) := upperInput e s (Nat.pair c a)
  have lowerSpec (e s c a m : Nat) :
      (m < lowerBound (lowerInput e s c a) ∧ lowerTest (lowerInput e s c a) m = 1) ↔
        lowerCandidate e s (Finset.equivBitIndices c) (Finset.equivBitIndices a) m := by
    simp only [lowerCandidate, lowerBound, lowerTest, lowerInput, upperInput, req, stage,
      lowerFree, masks, Nat.unpair_pair, Nat.lt_succ_iff, PriorityBoundedSearch.gateOne, Nat.add_eq_zero_iff,
      answerZero, admissibleOne, ite_eq_left_iff, Nat.one_ne_zero, imp_false, not_not]
    have hk : Nat.pair e m ∉ K ↔ ¬ (φ e m).Dom := by
      simp [K]
    rw [hk]
    constructor
    · rintro ⟨hle, ⟨hdiv, hcontent, hactive⟩, hmem⟩
      exact ⟨hle, hmem, hdiv, hcontent, hactive⟩
    · rintro ⟨hle, hmem, hdiv, hcontent, hactive⟩
      exact ⟨hle, ⟨hdiv, hcontent, hactive⟩, hmem⟩

  let upperCode (a : Nat) := PriorityBoundedSearch.scan upperTest upperBefore a (upperBound a)
  let lowerCode (a : Nat) := PriorityBoundedSearch.scan lowerTest Nat.lt a (lowerBound a)
  have hu : Rel upperCode := PriorityBoundedSearch.scanRelative upperTest upperBefore hupperTest hupperBefore
    upperBound hupperBound
  have hl : Rel lowerCode := PriorityBoundedSearch.scanRelative lowerTest Nat.lt hlowerTest (Primrec.nat_lt.decide.to_comp.computablePred)
    lowerBound (Computable.succ.comp hstage)
  let upperSearch (e s : Nat) (Z : Finset Nat) : Option (Nat × Nat) :=
    PriorityBoundedSearch.pairResult (upperCode (upperInput e s (Finset.equivBitIndices.symm Z)))
  let lowerSearch (e s : Nat) (content active : Finset Nat) : Option Nat :=
    PriorityBoundedSearch.natResult (lowerCode (lowerInput e s (Finset.equivBitIndices.symm content)
      (Finset.equivBitIndices.symm active)))
  refine ⟨upperSearch, lowerSearch, hu.of_eq ?_, hl.of_eq ?_, ?_, ?_⟩
  · intro p
    cases hp : p.unpair with
    | mk e args =>
      cases ha : args.unpair with
      | mk s z =>
        have hinner : Nat.pair s z = args := by simpa only [ha] using Nat.pair_unpair args
        have houter : Nat.pair e args = p := by simpa only [hp] using Nat.pair_unpair p
        simp only [ha, upperSearch, Equiv.symm_apply_apply,
          upperInput, hinner, houter, PriorityBoundedSearch.pairRoundTrip]
  · intro p
    cases hp : p.unpair with
    | mk e args =>
      cases ha : args.unpair with
      | mk s sets =>
        cases hz : sets.unpair with
        | mk c a =>
          have hsets : Nat.pair c a = sets := by simpa only [hz] using Nat.pair_unpair sets
          have hinner : Nat.pair s sets = args := by simpa only [ha] using Nat.pair_unpair args
          have houter : Nat.pair e args = p := by simpa only [hp] using Nat.pair_unpair p
          simp only [ha, hz, lowerSearch, Equiv.symm_apply_apply, lowerInput,
            upperInput, hsets, hinner, houter, PriorityBoundedSearch.natRoundTrip]
  · intro e s Z
    let z := Finset.equivBitIndices.symm Z
    let input := upperInput e s z
    refine PriorityBoundedSearch.pairResult_correct upperTest pairBefore horder input
      (upperBound input) (upperCandidate e s Z) ?_
    intro i
    exact (upperSpec e s z i).trans (by rw [Equiv.apply_symm_apply])
  · intro e s content active
    let c := Finset.equivBitIndices.symm content
    let a := Finset.equivBitIndices.symm active
    let input := lowerInput e s c a
    refine PriorityBoundedSearch.natResult_correct lowerTest input (lowerBound input)
      (lowerCandidate e s content active) ?_
    intro m
    exact (lowerSpec e s c a m).trans (by rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply])
