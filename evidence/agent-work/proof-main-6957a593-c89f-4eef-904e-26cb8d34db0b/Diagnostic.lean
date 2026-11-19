import Mathlib

set_option maxHeartbeats 150000

theorem PriorityBoundedOracleSearches : (
∀ (φ : Nat → Nat → Part Nat)
    (rowAt : Nat → Nat → Nat → Finset Nat)
    (pairBefore : (Nat × Nat) → (Nat × Nat) → Prop)
    (query : Nat → Nat) (M : Set Nat),
  let K : Set Nat := {n | (φ n.unpair.1 n.unpair.2).Dom}
  let oracle : Set (Nat →. Nat) :=
    {(by classical exact fun n => Part.some (if n ∈ K then 1 else 0))}
  Computable (fun p : Nat × Nat × Nat =>
    Finset.equivBitIndices.symm (rowAt p.1 p.2.1 p.2.2)) →
  IsStrictTotalOrder (Nat × Nat) pairBefore →
  ComputablePred (fun p : (Nat × Nat) × (Nat × Nat) => pairBefore p.1 p.2) →
  Computable query →
  (∀ e x t, query (Nat.pair e (Nat.pair x t)) ∉ K ↔
    ∀ r, t ≤ r → rowAt e x r = rowAt e x t) →
  Nat.RecursiveIn oracle (by classical exact fun m => Part.some (if m ∈ M then 1 else 0)) →
  let upperCandidate (e s : Nat) (Z : Finset Nat) (q : Nat × Nat) : Prop :=
    q.1 ≤ s ∧ q.2 ≤ s ∧
    (∀ m ∈ rowAt e q.1 q.2, m ≤ s ∧ m ∉ Z) ∧
    ∀ r, q.2 ≤ r → rowAt e q.1 r = rowAt e q.1 q.2
  let lowerCandidate (e s : Nat) (content active : Finset Nat) (m : Nat) : Prop :=
    m ≤ s ∧ m ∈ M ∧ ¬ (φ e m).Dom ∧ m ∉ content ∧ m ∉ active
  ∃ (upperSearch : Nat → Nat → Finset Nat → Option (Nat × Nat))
    (lowerSearch : Nat → Nat → Finset Nat → Finset Nat → Option Nat),
    Nat.RecursiveIn oracle (fun n =>
      let (e, args) := n.unpair
      let (s, z) := args.unpair
      Part.some (match upperSearch e s (Finset.equivBitIndices z) with
        | none => 0
        | some (x, t) => (Nat.pair x t).succ)) ∧
    Nat.RecursiveIn oracle (fun n =>
      let (e, args) := n.unpair
      let (s, sets) := args.unpair
      let (content, active) := sets.unpair
      Part.some (match lowerSearch e s (Finset.equivBitIndices content)
          (Finset.equivBitIndices active) with
        | none => 0
        | some m => m.succ)) ∧
    (∀ e s Z,
      match upperSearch e s Z with
      | none => ∀ q, ¬ upperCandidate e s Z q
      | some q => upperCandidate e s Z q ∧
          ∀ p, upperCandidate e s Z p → ¬ pairBefore p q) ∧
    (∀ e s content active,
      match lowerSearch e s content active with
      | none => ∀ m, ¬ lowerCandidate e s content active m
      | some m => lowerCandidate e s content active m ∧
          ∀ n, lowerCandidate e s content active n → m ≤ n)
) :=
by
  classical
  intro φ rowAt pairBefore query M K oracle hrow horder hbefore hquery hstable hM
    upperCandidate lowerCandidate
  let Rel (f : Nat → Nat) := Nat.RecursiveIn oracle (fun n => Part.some (f n))
  have liftOrdinary {f : Nat → Nat} (hf : Computable f) : Rel f :=
    RecursiveIn.iff_nat.mp hf.computableIn
  have relComp {f g : Nat → Nat} (hf : Rel f) (hg : Rel g) :
      Rel (fun n => f (g n)) :=
    (Nat.RecursiveIn.comp hf hg).of_eq (fun _ => Part.bind_some _ _)
  have relPair {f g : Nat → Nat} (hf : Rel f) (hg : Rel g) :
      Rel (fun n => Nat.pair (f n) (g n)) :=
    (Nat.RecursiveIn.pair hf hg).of_eq (fun n => by
      change Part.map Nat.pair (Part.some (f n)) <*> Part.some (g n) = _
      rw [Part.map_some, ← Part.pure_eq_some (Nat.pair (f n)), pure_seq]
      exact Part.map_some _ _)
  have rel₂ {f g : Nat → Nat} {op : Nat → Nat → Nat} (hop : Computable₂ op)
      (hf : Rel f) (hg : Rel g) : Rel (fun n => op (f n) (g n)) := by
    have h : Computable (fun n : Nat => op n.unpair.1 n.unpair.2) :=
      hop.comp (Computable.fst.comp Computable.unpair) (Computable.snd.comp Computable.unpair)
    exact relComp (liftOrdinary h) (relPair hf hg) |>.of_eq (fun n => by
      simp only [Nat.unpair_pair])
  let answer (n : Nat) : Nat := if n ∈ K then 1 else 0
  have hanswer : Rel answer := Nat.RecursiveIn.oracle _ (Set.mem_singleton _)
  have answerZero (n : Nat) : answer n = 0 ↔ n ∉ K := by simp [answer]
  let admissible (m : Nat) : Nat := if m ∈ M then 1 else 0
  have admissibleOne (m : Nat) : admissible m = 1 ↔ m ∈ M := by simp [admissible]

  -- Alphabeta Math, Basic arithmetic operations and bounded quantification
  -- are primitive recursive, Steps 1.1, 2.1 and 3.1.
  -- https://alphabetamath.cc/item/prop-basic-arithmetic-and-bounded-quantification-are-primitive-recursive
  -- Arithmetic and a bounded universal test suffice for the ordinary part of
  -- the upper test, even though the supplied row codes are only computable.
  have powTwo : Primrec (fun i : Nat => 2 ^ i) := by
    exact ((Primrec.nat_rec (α := Unit) (Primrec.const 1)
      (Primrec.nat_mul.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 2))).comp
        (Primrec.const ()) Primrec.id).of_eq (fun i => by
          induction i with
          | zero => rfl
          | succ i ih => rw [Nat.pow_succ]; exact congrArg (· * 2) ih)
  have testBit : Primrec₂ Nat.testBit := by
    have hdiv : Primrec (fun p : Nat × Nat => p.1 / 2 ^ p.2) :=
      Primrec.nat_div.comp Primrec.fst (powTwo.comp Primrec.snd)
    exact (Primrec.eq.decide.comp
      (Primrec.nat_mod.comp hdiv (Primrec.const 2)) (Primrec.const 1)).of_eq
        (fun p => Nat.testBit_eq_decide_div_mod_eq.symm)
  have memBits (c m : Nat) : m ∈ Finset.equivBitIndices c ↔ c.testBit m = true := by
    simp [Finset.equivBitIndices_apply]
  have bitBound (c m : Nat) (hm : m ∈ Finset.equivBitIndices c) : m < c := by
    have h : 2 ^ m ≤ c := Nat.two_pow_le_of_mem_bitIndices (by
      simpa [Finset.equivBitIndices_apply] using hm)
    exact Nat.lt_of_lt_of_le Nat.lt_two_pow_self h
  let fits (p : Nat × Nat × Nat) : Prop :=
    ∀ m ∈ Finset.equivBitIndices p.1, m ≤ p.2.1 ∧ m ∉ Finset.equivBitIndices p.2.2
  have hfits : PrimrecPred fits := by
    let bitAllowed (m : Nat) (p : Nat × Nat × Nat) : Prop :=
      p.1.testBit m = false ∨ (m ≤ p.2.1 ∧ p.2.2.testBit m = false)
    have hleft : PrimrecPred (fun p : Nat × (Nat × Nat × Nat) =>
        p.2.1.testBit p.1 = false) :=
      Primrec.eq.comp (testBit.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
        (Primrec.const false)
    have hright : PrimrecPred (fun p : Nat × (Nat × Nat × Nat) =>
        p.2.2.2.testBit p.1 = false) :=
      Primrec.eq.comp (testBit.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
        Primrec.fst) (Primrec.const false)
    have hall : PrimrecRel bitAllowed := hleft.or
      ((Primrec.nat_le.comp Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).and hright)
    refine (hall.forall_mem_list.comp (Primrec.list_range.comp Primrec.fst) Primrec.id).of_eq ?_
    intro p
    change (∀ m ∈ List.range p.1, bitAllowed m p) ↔ fits p
    simp only [fits, List.mem_range, bitAllowed, memBits]
    constructor
    · intro h m hm
      exact (h m (bitBound p.1 m ((memBits _ _).mpr hm))).resolve_left (by simp [hm])
    · intro h m _
      cases b : p.1.testBit m with
      | false => exact Or.inl rfl
      | true =>
        obtain ⟨hle, hout⟩ := h m b
        exact Or.inr ⟨hle, Bool.eq_false_iff.mpr hout⟩

  -- Cintioli, arXiv:2609.00419v1, §4, pp. 8–9, upper and lower strategies.
  -- https://arxiv.org/pdf/2609.00419v1#page=8
  -- The article-specific Alphabeta Math portal and defect report returned 404.
  -- Step 2.2 of the shared-library proof inspires the finite accumulator.
  -- Here the step can query K, so use singleton-oracle recursion. The
  -- accumulator records the best candidate and its invariant proves minimality.
  let scan (test : Nat → Nat → Nat) (before : Nat → Nat → Prop) (a n : Nat) : Nat :=
    Nat.rec 0 (fun i best =>
      if test a i = 1 ∧ (best = 0 ∨ before i best.pred) then i.succ else best) n
  have scanCorrect (test : Nat → Nat → Nat) (before : Nat → Nat → Prop)
      (hirr : ∀ i, ¬ before i i)
      (htrans : ∀ i j k, before i j → before j k → before i k) (a n : Nat) :
      match scan test before a n with
      | 0 => ∀ k < n, test a k ≠ 1
      | j + 1 => (j < n ∧ test a j = 1) ∧
          ∀ k < n, test a k = 1 → ¬ before k j := by
    induction n with
    | zero => simp [scan]
    | succ n ih =>
      change (match (if test a n = 1 ∧
          (scan test before a n = 0 ∨ before n (scan test before a n).pred)
          then n.succ else scan test before a n) with
        | 0 => ∀ k < n.succ, test a k ≠ 1
        | j + 1 => (j < n.succ ∧ test a j = 1) ∧
            ∀ k < n.succ, test a k = 1 → ¬ before k j)
      cases hb : scan test before a n with
      | zero =>
        rw [hb] at ih ⊢
        by_cases hn : test a n = 1
        · simp only [hn, and_true, true_or, or_true, Nat.pred_zero, ↓reduceIte, true_and]
          refine ⟨⟨Nat.lt_succ_self n, hn⟩, ?_⟩
          intro k hk hv
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
          · exact (ih k hlt hv).elim
          · exact hirr k
        · simp only [hn, false_and, ↓reduceIte]
          intro k hk hv
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
          · exact ih k hlt hv
          · exact hn hv
      | succ j =>
        rw [hb] at ih ⊢
        simp only [Nat.succ_ne_zero, false_or, Nat.pred_succ]
        by_cases hn : test a n = 1 ∧ before n j
        · rw [if_pos hn]
          refine ⟨⟨Nat.lt_succ_self n, hn.1⟩, ?_⟩
          intro k hk hv hkn
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
          · exact ih.2 k hlt hv (htrans _ _ _ hkn hn.2)
          · exact hirr k hkn
        · rw [if_neg hn]
          refine ⟨⟨Nat.lt.step ih.1.1, ih.1.2⟩, ?_⟩
          intro k hk hv
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
          · exact ih.2 k hlt hv
          · exact fun h => hn ⟨hv, h⟩
  have scanRelative (test : Nat → Nat → Nat) (before : Nat → Nat → Prop)
      (htest : Rel (fun p => test p.unpair.1 p.unpair.2))
      (hcmp : ComputablePred (fun p : Nat × Nat => before p.1 p.2))
      (bound : Nat → Nat) (hbound : Computable bound) :
      Rel (fun a => scan test before a (bound a)) := by
    let step (p : Nat) : Nat :=
      let a := p.unpair.1
      let i := p.unpair.2.unpair.1
      let best := p.unpair.2.unpair.2
      if test a i = 1 ∧ (best = 0 ∨ before i best.pred) then i.succ else best
    have ha : Computable (fun p : Nat => p.unpair.1) := Computable.fst.comp Computable.unpair
    have hd : Computable (fun p : Nat => p.unpair.2.unpair) :=
      Computable.unpair.comp (Computable.snd.comp Computable.unpair)
    have hi : Computable (fun p : Nat => p.unpair.2.unpair.1) := Computable.fst.comp hd
    have hb : Computable (fun p : Nat => p.unpair.2.unpair.2) := Computable.snd.comp hd
    have ht : Rel (fun p => test p.unpair.1 p.unpair.2.unpair.1) := by
      have h := relComp htest (relPair (liftOrdinary ha) (liftOrdinary hi))
      exact h.of_eq (fun n => by simp only [Nat.unpair_pair])
    let choose (v : Nat) (p : Nat × Nat) : Nat :=
      if v = 1 ∧ (p.2 = 0 ∨ before p.1 p.2.pred) then p.1.succ else p.2
    have hchoose : Computable₂ choose := by
      have hc := hcmp.decide.comp
        ((Computable.fst.comp Computable.snd).pair
          (Primrec.pred.to_comp.comp (Computable.snd.comp Computable.snd)))
      have hv := Primrec.eq.decide.comp Primrec.fst (Primrec.const (1 : Nat))
      have hb₀ := Primrec.eq.decide.comp (Primrec.snd.comp Primrec.snd) (Primrec.const (0 : Nat))
      have htest' := Primrec.and.to_comp.comp hv.to_comp
        (Primrec.or.to_comp.comp hb₀.to_comp hc)
      refine (Computable.cond htest'
        (Computable.succ.comp (Computable.fst.comp Computable.snd))
        (Computable.snd.comp Computable.snd)).of_eq ?_
      intro p
      simp [choose, Bool.cond_eq_ite]
    have hfinal : Computable₂ (fun v pos => choose v pos.unpair) :=
      hchoose.comp Computable.fst (Computable.unpair.comp Computable.snd)
    have hstep : Rel step := by
      refine (rel₂ hfinal ht (relPair (liftOrdinary hi) (liftOrdinary hb))).of_eq ?_
      intro n
      simp [step, choose]
    have hprec := Nat.RecursiveIn.prec (liftOrdinary (Computable.const 0)) hstep
    have hloop : Rel (fun p => scan test before p.unpair.1 p.unpair.2) := by
      refine hprec.of_eq ?_
      intro p
      change (p.unpair.2.rec (Part.some 0) (fun y IH =>
        IH.bind fun i => Part.some (step (Nat.pair p.unpair.1 (Nat.pair y i))))) = _
      induction p.unpair.2 with
      | zero => rfl
      | succ n ih =>
        simp only [Nat.rec_succ, ih, Part.bind_some, step, Nat.unpair_pair]
        rfl
    refine (relComp hloop (relPair (liftOrdinary Computable.id) (liftOrdinary hbound))).of_eq ?_
    intro n
    simp [id]

  let gate (reject value : Nat) : Nat := if reject = 0 then value else 0
  have gateOne (reject value : Nat) : gate reject value = 1 ↔ reject = 0 ∧ value = 1 := by
    by_cases h : reject = 0 <;> simp [gate, h]
  have hgate : Computable₂ gate :=
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
      Primrec.snd (Primrec.const 0)).to_comp

  -- Nat.pair enumerates the stage square by the first (s + 1)^2 codes.
  have square (s : Nat) (q : Nat × Nat) :
      Nat.pair q.1 q.2 < (s + 1) ^ 2 ↔ q.1 ≤ s ∧ q.2 ≤ s := by
    constructor
    · intro h
      have hm : max q.1 q.2 ≤ s := by
        by_contra hn
        have hpow := Nat.pow_le_pow_left (n := s + 1) (m := max q.1 q.2) (by omega) 2
        have hl := Nat.max_sq_add_min_le_pair q.1 q.2
        omega
      exact max_le_iff.mp hm
    · intro h
      exact (Nat.pair_lt_max_add_one_sq _ _).trans_le
        (Nat.pow_le_pow_left (Nat.add_le_add_right (max_le_iff.mpr h) 1) 2)
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
    exact (Primrec.nat_mul.to_comp.comp h h).of_eq (fun a => by simp only [upperBound, pow_two]; rfl)
  let upperTest (a i : Nat) := gate (answer (query (Nat.pair (req a) i)))
    (if fits (Finset.equivBitIndices.symm (rowAt (req a) i.unpair.1 i.unpair.2),
      stage a, masks a) then 1 else 0)
  have hupperTest : Rel (fun p => upperTest p.unpair.1 p.unpair.2) := by
    have ha : Computable (fun p : Nat => p.unpair.1) := Computable.fst.comp Computable.unpair
    have hq : Computable (fun p : Nat => p.unpair.2.unpair) :=
      Computable.unpair.comp (Computable.snd.comp Computable.unpair)
    have hc := hrow.comp ((hreq.comp ha).pair hq)
    have hf := hfits.to_comp.decide.comp (hc.pair ((hstage.comp ha).pair (hmasks.comp ha)))
    have hflag := Computable.cond hf (Computable.const (1 : Nat)) (Computable.const 0)
    refine (rel₂ hgate (relComp hanswer (liftOrdinary (hquery.comp hinput)))
      (liftOrdinary hflag)).of_eq ?_
    intro p
    simp [upperTest, Bool.cond_eq_ite]
  let upperInput (e s z : Nat) := Nat.pair e (Nat.pair s z)
  have upperSpec (e s z i : Nat) :
      (i < upperBound (upperInput e s z) ∧ upperTest (upperInput e s z) i = 1) ↔
        upperCandidate e s (Finset.equivBitIndices z) i.unpair := by
    have hi := square s i.unpair
    rw [Nat.pair_unpair] at hi
    have hs := hstable e i.unpair.1 i.unpair.2
    rw [Nat.pair_unpair] at hs
    simp only [upperCandidate, upperBound, upperTest, upperInput, req, stage, masks,
      Nat.unpair_pair, gateOne, answerZero, ite_eq_left_iff, Nat.zero_ne_one,
      imp_false, not_not, fits, Equiv.apply_symm_apply, hi, hs]
    tauto

  let lowerBound (a : Nat) := (stage a).succ
  let lowerFree (a m : Nat) : Prop :=
    m ∉ Finset.equivBitIndices (masks a).unpair.1 ∧
    m ∉ Finset.equivBitIndices (masks a).unpair.2
  let lowerTest (a m : Nat) := gate
    (answer (Nat.pair (req a) m) + (if lowerFree a m then 0 else 1)) (admissible m)
  have hlowerTest : Rel (fun p => lowerTest p.unpair.1 p.unpair.2) := by
    have hm : Computable (fun p : Nat => p.unpair.2) := Computable.snd.comp Computable.unpair
    have hc := Computable.unpair.comp (hmasks.comp (Computable.fst.comp Computable.unpair))
    have hfree : Computable (fun p : Nat => decide (lowerFree p.unpair.1 p.unpair.2)) := by
      have h₁ := Computable.not.comp (testBit.to_comp.comp (Computable.fst.comp hc) hm)
      have h₂ := Computable.not.comp (testBit.to_comp.comp (Computable.snd.comp hc) hm)
      refine (Primrec.and.to_comp.comp h₁ h₂).of_eq ?_
      intro p
      simp [lowerFree, memBits]
    have hreject := rel₂ Primrec.nat_add.to_comp (relComp hanswer (liftOrdinary hinput))
      (liftOrdinary (Computable.cond hfree (Computable.const (0 : Nat)) (Computable.const 1)))
    exact (rel₂ hgate hreject (relComp hM (liftOrdinary hm))).of_eq (fun p => by
      simp [lowerTest, Bool.cond_eq_ite])
  let lowerInput (e s c a : Nat) := upperInput e s (Nat.pair c a)
  have lowerSpec (e s c a m : Nat) :
      (m < lowerBound (lowerInput e s c a) ∧ lowerTest (lowerInput e s c a) m = 1) ↔
        lowerCandidate e s (Finset.equivBitIndices c) (Finset.equivBitIndices a) m := by
    simp only [lowerCandidate, lowerBound, lowerTest, lowerInput, upperInput, req, stage,
      lowerFree, masks, Nat.unpair_pair, Nat.lt_succ_iff, gateOne, Nat.add_eq_zero_iff,
      answerZero, admissibleOne, ite_eq_left_iff, Nat.one_ne_zero, imp_false, not_not]
    change (m ≤ s ∧ (¬ (φ e m).Dom ∧
      (m ∉ Finset.equivBitIndices c ∧ m ∉ Finset.equivBitIndices a)) ∧ m ∈ M) ↔ _
    tauto

  let upperCode (a : Nat) := scan upperTest upperBefore a (upperBound a)
  let lowerCode (a : Nat) := scan lowerTest (· < ·) a (lowerBound a)
  have hu : Rel upperCode := scanRelative upperTest upperBefore hupperTest hupperBefore
    upperBound hupperBound
  have hl : Rel lowerCode := scanRelative lowerTest (· < ·) hlowerTest Primrec.nat_lt.to_comp
    lowerBound (Computable.succ.comp hstage)
  let upperSearch (e s : Nat) (Z : Finset Nat) : Option (Nat × Nat) :=
    match upperCode (upperInput e s (Finset.equivBitIndices.symm Z)) with
    | 0 => none
    | j + 1 => some j.unpair
  let lowerSearch (e s : Nat) (content active : Finset Nat) : Option Nat :=
    match lowerCode (lowerInput e s (Finset.equivBitIndices.symm content)
        (Finset.equivBitIndices.symm active)) with
    | 0 => none
    | j + 1 => some j
  refine ⟨upperSearch, lowerSearch, hu.of_eq ?_, hl.of_eq ?_, ?_, ?_⟩
  · intro p
    rcases Nat.unpair p with ⟨e, args⟩
    rcases Nat.unpair args with ⟨s, z⟩
    simp only [upperSearch, Equiv.symm_apply_apply, upperInput]
    rw [show Nat.pair e (Nat.pair s z) = p by simp_all]
    cases upperCode p with
    | zero => rfl
    | succ j => cases h : j.unpair with | mk x t => simpa using congrArg Nat.succ (Nat.pair_unpair j)
  · intro p
    rcases Nat.unpair p with ⟨e, args⟩
    rcases Nat.unpair args with ⟨s, sets⟩
    rcases Nat.unpair sets with ⟨c, a⟩
    simp only [lowerSearch, Equiv.symm_apply_apply, lowerInput, upperInput]
    rw [show Nat.pair e (Nat.pair s (Nat.pair c a)) = p by simp_all]
    cases lowerCode p <;> rfl
  · intro e s Z
    let z := Finset.equivBitIndices.symm Z
    have spec (i : Nat) :=
      (upperSpec e s z i).trans (by rw [Equiv.apply_symm_apply])
    letI : IsStrictTotalOrder (Nat × Nat) pairBefore := horder
    have h := scanCorrect upperTest upperBefore
      (fun i => irrefl (r := pairBefore) i.unpair)
      (fun i j k => IsTrans.trans i.unpair j.unpair k.unpair)
      (upperInput e s z) (upperBound (upperInput e s z))
    change (match upperCode (upperInput e s z) with
      | 0 => _
      | j + 1 => _) at h
    unfold upperSearch
    cases upperCode (upperInput e s z) with
    | zero =>
      intro q hq
      let i := Nat.pair q.1 q.2
      have hi := (spec i).mpr (by simpa [i] using hq)
      exact h i hi.1 hi.2
    | succ j =>
      refine ⟨(spec j).mp h.1, ?_⟩
      intro q hq
      let i := Nat.pair q.1 q.2
      have hi := (spec i).mpr (by simpa [i] using hq)
      simpa [upperBefore, i] using h.2 i hi.1 hi.2
  · intro e s content active
    let c := Finset.equivBitIndices.symm content
    let a := Finset.equivBitIndices.symm active
    have spec (m : Nat) :=
      (lowerSpec e s c a m).trans (by rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply])
    have h := scanCorrect lowerTest (· < ·) (fun i => Nat.lt_irrefl i)
      (fun _ _ _ => Nat.lt_trans) (lowerInput e s c a) (lowerBound (lowerInput e s c a))
    change (match lowerCode (lowerInput e s c a) with
      | 0 => _
      | j + 1 => _) at h
    unfold lowerSearch
    cases lowerCode (lowerInput e s c a) with
    | zero =>
      intro m hm
      have hm' := (spec m).mpr hm
      exact h m hm'.1 hm'.2
    | succ j =>
      refine ⟨(spec j).mp h.1, ?_⟩
      intro m hm
      have hm' := (spec m).mpr hm
      exact Nat.le_of_not_gt (h.2 m hm'.1 hm'.2)

#print axioms PriorityBoundedOracleSearches
