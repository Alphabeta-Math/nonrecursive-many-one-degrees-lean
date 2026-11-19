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

end PriorityBoundedSearch
