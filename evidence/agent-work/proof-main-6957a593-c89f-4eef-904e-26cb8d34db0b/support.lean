namespace PriorityBoundedSearch

private def OracleTotal (oracle : Set (Nat →. Nat)) (f : Nat → Nat) :=
  Nat.RecursiveIn oracle (fun n => Part.some (f n))

variable {oracle : Set (Nat →. Nat)}

private theorem liftOrdinary {f : Nat → Nat} (hf : Computable f) : OracleTotal oracle f :=
  RecursiveIn.iff_nat.mp hf.computableIn

private theorem relComp {f g : Nat → Nat} (hf : OracleTotal oracle f) (hg : OracleTotal oracle g) :
    OracleTotal oracle (fun n => f (g n)) :=
  (Nat.RecursiveIn.comp hf hg).of_eq (fun _ => Part.bind_some _ _)

private theorem relPair {f g : Nat → Nat} (hf : OracleTotal oracle f) (hg : OracleTotal oracle g) :
    OracleTotal oracle (fun n => Nat.pair (f n) (g n)) :=
  (Nat.RecursiveIn.pair hf hg).of_eq (fun n => by
    change Part.map Nat.pair (Part.some (f n)) <*> Part.some (g n) = _
    rw [Part.map_some, ← Part.pure_eq_some (Nat.pair (f n)), pure_seq]
    exact Part.map_some _ _)

private theorem rel₂ {f g : Nat → Nat} {op : Nat → Nat → Nat} (hop : Computable₂ op)
    (hf : OracleTotal oracle f) (hg : OracleTotal oracle g) : OracleTotal oracle (fun n => op (f n) (g n)) := by
  have h : Computable (fun n : Nat => op n.unpair.1 n.unpair.2) :=
    hop.comp (Computable.fst.comp Computable.unpair) (Computable.snd.comp Computable.unpair)
  exact relComp (liftOrdinary h) (relPair hf hg) |>.of_eq (fun n => by
    simp only [Nat.unpair_pair])

-- Cintioli, arXiv:2609.00419v1, §4, pp. 8–9, upper and lower strategies.
-- https://arxiv.org/pdf/2609.00419v1#page=8
-- The article-specific Alphabeta Math portal and defect report returned 404.
-- Step 2.2 of the shared-library proof inspires the finite accumulator.
-- https://alphabetamath.cc/item/prop-basic-arithmetic-and-bounded-quantification-are-primitive-recursive
-- Here the step can query K, so use singleton-oracle recursion. The
-- accumulator records the best candidate and its invariant proves minimality.
private noncomputable def advance (before : Nat → Nat → Prop) (value i best : Nat) : Nat := by
  classical
  exact if value = 1 ∧ (best = 0 ∨ before i best.pred) then i.succ else best

private noncomputable def scan (test : Nat → Nat → Nat) (before : Nat → Nat → Prop) (a n : Nat) : Nat :=
  Nat.rec 0 (fun i best => advance before (test a i) i best) n

private theorem scanCorrect (test : Nat → Nat → Nat) (before : Nat → Nat → Prop)
    (hirr : ∀ i, ¬ before i i)
    (htrans : ∀ i j k, before i j → before j k → before i k) (a n : Nat) :
    match scan test before a n with
    | 0 => ∀ k < n, test a k ≠ 1
    | j + 1 => (j < n ∧ test a j = 1) ∧
        ∀ k < n, test a k = 1 → ¬ before k j := by
  classical
  induction n with
  | zero => simp [scan]
  | succ n ih =>
    change (match advance before (test a n) n (scan test before a n) with
      | 0 => ∀ k < n.succ, test a k ≠ 1
      | j + 1 => (j < n.succ ∧ test a j = 1) ∧
          ∀ k < n.succ, test a k = 1 → ¬ before k j)
    generalize scan test before a n = best at ih ⊢
    cases best with
    | zero =>
      unfold advance
      by_cases hn : test a n = 1
      · have htake : test a n = 1 ∧ (0 = 0 ∨ before n (Nat.pred 0)) :=
          ⟨hn, Or.inl rfl⟩
        rw [ite_eq_left htake]
        refine ⟨⟨Nat.lt_succ_self n, hn⟩, ?_⟩
        intro k hk hv
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
        · exact (ih k hlt hv).elim
        · exact hirr k
      · have hskip : ¬ (test a n = 1 ∧ (0 = 0 ∨ before n (Nat.pred 0))) :=
          fun h => hn h.1
        rw [ite_eq_right hskip]
        intro k hk hv
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
        · exact ih k hlt hv
        · exact hn hv
    | succ j =>
      simp only [advance, Nat.succ_ne_zero, false_or, Nat.pred_succ]
      by_cases hn : test a n = 1 ∧ before n j
      · rw [ite_eq_left hn]
        refine ⟨⟨Nat.lt_succ_self n, hn.1⟩, ?_⟩
        intro k hk hv hkn
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
        · exact ih.2 k hlt hv (htrans _ _ _ hkn hn.2)
        · exact hirr k hkn
      · rw [ite_eq_right hn]
        refine ⟨⟨Nat.lt_succ_of_lt ih.1.1, ih.1.2⟩, ?_⟩
        intro k hk hv
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hlt | rfl
        · exact ih.2 k hlt hv
        · exact fun h => hn ⟨hv, h⟩

private theorem scanRelative (test : Nat → Nat → Nat) (before : Nat → Nat → Prop)
    (htest : OracleTotal oracle (fun p => test p.unpair.1 p.unpair.2))
    (hcmp : ComputablePred (fun p : Nat × Nat => before p.1 p.2))
    (bound : Nat → Nat) (hbound : Computable bound) :
    OracleTotal oracle (fun a => scan test before a (bound a)) := by
  classical
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
  have ht : OracleTotal oracle (fun p => test p.unpair.1 p.unpair.2.unpair.1) := by
    have h := relComp htest (relPair (liftOrdinary ha) (liftOrdinary hi))
    exact h.of_eq (fun n => by simp only [Nat.unpair_pair])
  let choose (v : Nat) (p : Nat × Nat) : Nat := advance before v p.1 p.2
  have hchoose : Computable₂ choose := by
    have hpos : Computable (fun p : Nat × (Nat × Nat) => p.2) := Computable.snd
    have hindex := Computable.fst.comp hpos
    have hbest := Computable.snd.comp hpos
    have hc := hcmp.decide.comp (hindex.pair (Primrec.pred.to_comp.comp hbest))
    have hv : Computable (fun p : Nat × (Nat × Nat) => decide (p.1 = 1)) :=
      (Primrec.eq.decide.comp Primrec.fst (Primrec.const (1 : Nat))).to_comp
    have hb₀ := Primrec.eq.decide.to_comp.comp hbest (Computable.const (0 : Nat))
    have htest' := Primrec.and.to_comp.comp hv (Primrec.or.to_comp.comp hb₀ hc)
    refine (Computable.cond htest' (Computable.succ.comp hindex) hbest).of_eq ?_
    intro p
    simp [choose, advance, Bool.cond_eq_ite]
  have hfinal : Computable₂ (fun v (pos : Nat) => choose v pos.unpair) :=
    hchoose.comp Computable.fst (Computable.unpair.comp Computable.snd)
  have hstep : OracleTotal oracle step := by
    refine (rel₂ hfinal ht (relPair (liftOrdinary hi) (liftOrdinary hb))).of_eq ?_
    intro n
    simp [step, choose, advance]
  have hprec := Nat.RecursiveIn.prec (liftOrdinary (Computable.const 0)) hstep
  have hloop : OracleTotal oracle (fun p => scan test before p.unpair.1 p.unpair.2) := by
    refine hprec.of_eq ?_
    intro p
    cases hp : p.unpair with
    | mk a n =>
      simp only [hp]
      change Nat.rec (Part.some 0) (fun y IH =>
        IH.bind fun i => Part.some (step (Nat.pair a (Nat.pair y i)))) n =
          Part.some (scan test before a n)
      clear hp p
      induction n with
      | zero => rfl
      | succ n ih =>
        change (Nat.rec (motive := fun _ => Part Nat) (Part.some 0) (fun y IH => IH.bind fun i =>
          Part.some (step (Nat.pair a (Nat.pair y i)))) n).bind
            (fun i => Part.some (step (Nat.pair a (Nat.pair n i)))) = _
        rw [ih, Part.bind_some]
        simp [step, scan, advance]
  refine (relComp hloop (relPair (liftOrdinary Computable.id) (liftOrdinary hbound))).of_eq ?_
  intro n
  simp [id]

private def pairResult (code : Nat) : Option (Nat × Nat) :=
  match code with
  | 0 => none
  | j + 1 => some j.unpair

private def natResult (code : Nat) : Option Nat :=
  match code with
  | 0 => none
  | j + 1 => some j

private theorem pairRoundTrip (code : Nat) :
    (match pairResult code with
    | none => 0
    | some (x, t) => (Nat.pair x t).succ) = code := by
  cases code with
  | zero => rfl
  | succ j =>
    cases hj : j.unpair with
    | mk x t =>
      have heq : Nat.pair x t = j := by simpa only [hj] using Nat.pair_unpair j
      simp only [pairResult, hj, heq]

private theorem natRoundTrip (code : Nat) :
    (match natResult code with
    | none => 0
    | some m => m.succ) = code := by
  cases code <;> rfl

private theorem pairResult_correct (test : Nat → Nat → Nat)
    (before : (Nat × Nat) → (Nat × Nat) → Prop)
    (order : IsStrictTotalOrder (Nat × Nat) before)
    (a n : Nat) (eligible : (Nat × Nat) → Prop)
    (spec : ∀ i, (i < n ∧ test a i = 1) ↔ eligible i.unpair) :
    match pairResult (scan test (fun i j => before i.unpair j.unpair) a n) with
    | none => ∀ q, ¬ eligible q
    | some q => eligible q ∧ ∀ p, eligible p → ¬ before p q := by
  let : IsStrictTotalOrder (Nat × Nat) before := order
  have h := scanCorrect test (fun i j => before i.unpair j.unpair)
    (fun i => irrefl (r := before) i.unpair)
    (fun i j k => IsTrans.trans i.unpair j.unpair k.unpair) a n
  generalize scan test (fun i j => before i.unpair j.unpair) a n = code at h ⊢
  cases code with
  | zero =>
    intro q hq
    obtain ⟨hi, ht⟩ := (spec (Nat.pair q.1 q.2)).mpr (by simpa only [Nat.unpair_pair] using hq)
    exact h _ hi ht
  | succ j =>
    refine ⟨(spec j).mp h.1, ?_⟩
    intro q hq
    let i := Nat.pair q.1 q.2
    have hi := (spec i).mpr (by simpa only [i, Nat.unpair_pair] using hq)
    simpa only [i, Nat.unpair_pair] using h.2 i hi.1 hi.2

private theorem natResult_correct (test : Nat → Nat → Nat) (a n : Nat)
    (eligible : Nat → Prop) (spec : ∀ i, (i < n ∧ test a i = 1) ↔ eligible i) :
    match natResult (scan test Nat.lt a n) with
    | none => ∀ m, ¬ eligible m
    | some m => eligible m ∧ ∀ k, eligible k → m ≤ k := by
  have h := scanCorrect test Nat.lt Nat.lt_irrefl (fun _ _ _ h₁ h₂ => Nat.lt_trans h₁ h₂) a n
  generalize scan test Nat.lt a n = code at h ⊢
  cases code with
  | zero =>
    intro m hm
    have hm' := (spec m).mpr hm
    exact h m hm'.1 hm'.2
  | succ j =>
    refine ⟨(spec j).mp h.1, ?_⟩
    intro m hm
    have hm' := (spec m).mpr hm
    exact Nat.le_of_not_gt (h.2 m hm'.1 hm'.2)

-- Alphabeta Math, Basic arithmetic operations and bounded quantification
-- are primitive recursive, Steps 1.1, 2.1 and 3.1.
-- https://alphabetamath.cc/item/prop-basic-arithmetic-and-bounded-quantification-are-primitive-recursive
-- Arithmetic and a bounded universal test suffice for the ordinary part of
-- the upper test, even though the supplied row codes are only computable.

private theorem powTwo : Primrec (fun i : Nat => 2 ^ i) := by
  have hstep : Primrec₂ (fun (_ : Unit) (p : Nat × Nat) => p.2 * 2) :=
    Primrec.nat_mul.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 2)
  refine ((Primrec.nat_rec (Primrec.const 1) hstep).comp
    (Primrec.const ()) Primrec.id).of_eq ?_
  intro i
  change Nat.rec 1 (fun _ acc => acc * 2) i = 2 ^ i
  induction i with
  | zero => rfl
  | succ i ih => exact (congrArg (· * 2) ih).trans (Nat.pow_succ 2 i).symm

private theorem testBit : Primrec₂ Nat.testBit := by
  have hdiv : Primrec (fun p : Nat × Nat => p.1 / 2 ^ p.2) :=
    Primrec.nat_div.comp Primrec.fst (powTwo.comp Primrec.snd)
  exact (Primrec.eq.decide.comp
    (Primrec.nat_mod.comp hdiv (Primrec.const 2)) (Primrec.const 1)).of_eq
      (fun p => Nat.testBit_eq_decide_div_mod_eq.symm)

private theorem memBits (c m : Nat) : m ∈ Finset.equivBitIndices c ↔ c.testBit m = true := by
  simp only [Finset.equivBitIndices_apply, List.mem_toFinset, Nat.mem_bitIndices]

private theorem bitBound (c m : Nat) (hm : m ∈ Finset.equivBitIndices c) : m < c := by
  have h : 2 ^ m ≤ c := Nat.two_pow_le_of_mem_bitIndices (by
    simpa [Finset.equivBitIndices_apply] using hm)
  exact Nat.lt_of_lt_of_le Nat.lt_two_pow_self h

private def fits (p : Nat × Nat × Nat) : Prop :=
  ∀ m ∈ Finset.equivBitIndices p.1, m ≤ p.2.1 ∧ m ∉ Finset.equivBitIndices p.2.2

private theorem hfits : PrimrecPred fits := by
  classical
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
    obtain ⟨hle, hout⟩ :=
      (h m (bitBound p.1 m ((memBits _ _).mpr hm))).resolve_left (by simp [hm])
    exact ⟨hle, by simp [hout]⟩
  · intro h m _
    cases b : p.1.testBit m with
    | false => exact Or.inl rfl
    | true =>
      obtain ⟨hle, hout⟩ := h m b
      exact Or.inr ⟨hle, Bool.eq_false_iff.mpr hout⟩

private def gate (reject value : Nat) : Nat := if reject = 0 then value else 0

private theorem gateOne (reject value : Nat) : gate reject value = 1 ↔ reject = 0 ∧ value = 1 := by
  by_cases h : reject = 0 <;> simp [gate, h]

private theorem hgate : Computable₂ gate :=
  (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    Primrec.snd (Primrec.const 0)).to_comp

-- Cintioli, §4, pp. 8–9, upper and lower strategies. The two scans use
-- the row and marker tests from those strategies. Nat.pair enumerates the
-- stage square by the first (s + 1)^2 codes, and the supplied order governs
-- which eligible pair is returned.

private theorem square (s : Nat) (q : Nat × Nat) :
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

-- Keep symbolic packed bounds from being evaluated during theorem elaboration.
attribute [irreducible] scan

end PriorityBoundedSearch
