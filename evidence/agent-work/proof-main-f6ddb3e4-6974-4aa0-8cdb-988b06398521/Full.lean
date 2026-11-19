import Mathlib

import Proofs.PriorityBoundedOracleSearches

set_option maxHeartbeats 2000000

namespace PriorityCodedTrace

-- Cintioli, arXiv:2609.00419v1, §4, pp. 8–9 and Remark 6, p. 13.
-- https://arxiv.org/pdf/2609.00419v1#page=8
-- Both article-specific routes returned HTTP 404.
-- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419
-- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects
-- Pages 8–9 use all natural numbers as potential markers. The coordinator
-- also needs the restriction to M for the c.e. branch. In either instance
-- the supplier certifies the selected candidates and their minimality.
-- The supplier's arithmetic and closure helpers are private. The corresponding
-- local proofs below use the same bit coding and the native oracle constructors.
-- Alphabeta Math, prop-basic-arithmetic-and-bounded-quantification-are-primitive-recursive,
-- Step 2.2, uses bounded iteration with a finite accumulator.
-- https://alphabetamath.cc/item/prop-basic-arithmetic-and-bounded-quantification-are-primitive-recursive
-- Here the finite arithmetic uses the same principle. For visits and stages
-- the step invokes the compiled oracle searches, so we use RecursiveIn.prec.

private theorem powTwo : Primrec (fun i : Nat => 2 ^ i) := by
  have hstep : Primrec₂ (fun (_ : Unit) (p : Nat × Nat) => p.2 * 2) :=
    Primrec.nat_mul.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 2)
  refine ((Primrec.nat_rec (Primrec.const 1) hstep).comp
    (Primrec.const ()) Primrec.id).of_eq ?_
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
    exact (congrArg (· * 2) ih).trans (Nat.pow_succ 2 i).symm

private theorem bitTest : Primrec₂ Nat.testBit := by
  have hdiv : Primrec (fun p : Nat × Nat => p.1 / 2 ^ p.2) :=
    Primrec.nat_div.comp Primrec.fst (powTwo.comp Primrec.snd)
  exact (Primrec.eq.decide.comp
    (Primrec.nat_mod.comp hdiv (Primrec.const 2)) (Primrec.const 1)).of_eq
      (fun p => Nat.testBit_eq_decide_div_mod_eq.symm)

private theorem bitBuild : Primrec₂ Nat.bit := by
  exact (Primrec.cond Primrec.fst (Primrec.nat_double_succ.comp Primrec.snd)
    (Primrec.nat_double.comp Primrec.snd)).of_eq
      (fun p => by rcases p with ⟨b, n⟩; cases b <;> simp [Nat.bit_val])

private def orRec (a b bound : Nat) (i : Nat) : Nat :=
  Nat.rec 0 (fun k acc =>
    Nat.bit (a.testBit (bound - (k + 1)) || b.testBit (bound - (k + 1))) acc) i

private theorem orRec_bit (a b bound i m : Nat) (hi : i ≤ bound) :
    (orRec a b bound i).testBit m =
      if m < i then a.testBit (bound - i + m) || b.testBit (bound - i + m) else false := by
  induction i generalizing m with
  | zero => simp [orRec, Nat.zero_testBit]
  | succ i ih =>
    cases m with
    | zero => simp [orRec]
    | succ m =>
      have heq : bound - i + m = bound - (i + 1) + (m + 1) := by omega
      simp only [orRec, Nat.testBit_bit_succ]
      change (orRec a b bound i).testBit m = _
      rw [ih _ (by omega), heq]
      simp

private theorem primOr : Primrec₂ Nat.lor := by
  let index (p : (Nat × Nat) × (Nat × Nat)) :=
    (p.1.1 + p.1.2) - (p.2.1 + 1)
  have hindex : Primrec index :=
    Primrec.nat_sub.comp (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst)) (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
  have ha := bitTest.comp (Primrec.fst.comp (Primrec.fst : Primrec (Prod.fst :
    (Nat × Nat) × (Nat × Nat) → Nat × Nat))) hindex
  have hb := bitTest.comp (Primrec.snd.comp (Primrec.fst : Primrec (Prod.fst :
    (Nat × Nat) × (Nat × Nat) → Nat × Nat))) hindex
  have hbit : Primrec₂ (fun (p : Nat × Nat) (q : Nat × Nat) =>
      Nat.bit (p.1.testBit (index (p, q)) || p.2.testBit (index (p, q))) q.2) :=
    bitBuild.comp ((Primrec.cond ha (Primrec.const true) hb).of_eq (fun p => by cases p.1.1.testBit (index p) <;> rfl)) (Primrec.snd.comp Primrec.snd)
  refine (Primrec.nat_rec' (Primrec.nat_add : Primrec₂ Nat.add) (Primrec.const 0) hbit).of_eq ?_
  intro ⟨a, b⟩
  change orRec a b (a + b) (a + b) = a ||| b
  apply Nat.eq_of_testBit_eq
  intro m
  rw [orRec_bit _ _ _ _ _ le_rfl, Nat.testBit_lor, Nat.sub_self, Nat.zero_add]
  split
  · rfl
  · rw [Nat.testBit_eq_false_of_lt (n := a) (by
          exact Nat.lt_of_le_of_lt (by omega) Nat.lt_two_pow_self),
        Nat.testBit_eq_false_of_lt (n := b) (by
          exact Nat.lt_of_le_of_lt (by omega) Nat.lt_two_pow_self)]
    rfl

abbrev Bits := Finset.equivBitIndices

private theorem memBits (c m : Nat) : m ∈ Bits c ↔ c.testBit m = true := by
  simp only [Finset.equivBitIndices_apply, List.mem_toFinset, Nat.mem_bitIndices]

private theorem bitsOr (a b : Nat) : Bits (a ||| b) = Bits a ∪ Bits b := by
  ext m
  simp

private theorem bitsZero : Bits 0 = ∅ := by
  ext m
  simp

abbrev UpperSearch := Nat → Nat → Finset Nat → Option (Nat × Nat)
abbrev LowerSearch := Nat → Nat → Finset Nat → Finset Nat → Option Nat
abbrev Rows := Nat → Nat → Nat → Finset Nat

def upperCode (U : UpperSearch) (n : Nat) : Nat :=
  let (e, args) := n.unpair
  let (s, z) := args.unpair
  match U e s (Bits z) with
  | none => 0
  | some (x, t) => (Nat.pair x t).succ

def lowerCode (L : LowerSearch) (n : Nat) : Nat :=
  let (e, args) := n.unpair
  let (s, sets) := args.unpair
  let (content, active) := sets.unpair
  match L e s (Bits content) (Bits active) with
  | none => 0
  | some m => m.succ

def UpperCandidate (row : Rows) (e s : Nat) (Z : Finset Nat) (q : Nat × Nat) : Prop :=
  q.1 ≤ s ∧ q.2 ≤ s ∧
  (∀ m ∈ row e q.1 q.2, m ≤ s ∧ m ∉ Z) ∧
  ∀ r, q.2 ≤ r → row e q.1 r = row e q.1 q.2

def LowerCandidate (φ : Nat → Nat → Part Nat) (M : Set Nat)
    (e s : Nat) (content active : Finset Nat) (m : Nat) : Prop :=
  m ≤ s ∧ m ∈ M ∧ ¬ (φ e m).Dom ∧ m ∉ content ∧ m ∉ active

def UpperCorrect (row : Rows) (before : (Nat × Nat) → (Nat × Nat) → Prop)
    (U : UpperSearch) : Prop :=
  ∀ e s Z, match U e s Z with
    | none => ∀ q, ¬ UpperCandidate row e s Z q
    | some q => UpperCandidate row e s Z q ∧ ∀ p, UpperCandidate row e s Z p → ¬ before p q

def LowerCorrect (φ : Nat → Nat → Part Nat) (M : Set Nat) (L : LowerSearch) : Prop :=
  ∀ e s content active, match L e s content active with
    | none => ∀ m, ¬ LowerCandidate φ M e s content active m
    | some m => LowerCandidate φ M e s content active m ∧
        ∀ n, LowerCandidate φ M e s content active n → m ≤ n

abbrev State := Finset Nat × (Nat → Option Nat) × (Nat → Bool)

def initial : State := (∅, fun _ => none, fun _ => false)

def markerSet (marker : Nat → Option Nat) (p : Nat) : Finset Nat :=
  (Finset.range p).biUnion fun j =>
    if 2 * j + 1 < p then
      match marker j with
      | none => ∅
      | some m => {m}
    else ∅

theorem memMarkerSet (marker : Nat → Option Nat) (p m : Nat) :
    m ∈ markerSet marker p ↔ ∃ j, 2 * j + 1 < p ∧ marker j = some m := by
  simp only [markerSet, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨j, _, h⟩
    split at h
    · cases he : marker j <;> simp_all
      exact ⟨j, by assumption, by assumption⟩
    · simp at h
  · rintro ⟨j, hj, hm⟩
    refine ⟨j, by omega, ?_⟩
    simp [hj, hm]

def upperAction (U : UpperSearch) (s e : Nat) (a : State) : Option (Nat × Nat) :=
  if a.2.2 e then none else U e s (markerSet a.2.1 (2 * e))

def visit (row : Rows) (U : UpperSearch) (L : LowerSearch) (s k : Nat) (a : State) : State :=
  let e := k / 2
  if k % 2 = 0 then
    match upperAction U s e a with
    | none => a
    | some (x, t) =>
      let F := row e x t
      let remaining (j : Nat) :=
        match a.2.1 j with
        | none => none
        | some m => if k < 2 * j + 1 ∧ m ∈ F then none else some m
      (a.1 ∪ F, remaining, Function.update a.2.2 e true)
  else
    match a.2.1 e with
    | some _ => a
    | none => (a.1, Function.update a.2.1 e (L e s a.1 (markerSet a.2.1 s)), a.2.2)

def visits (row : Rows) (U : UpperSearch) (L : LowerSearch) (s : Nat) (a : State) (k : Nat) :
    State := Nat.rec a (fun p prev => visit row U L s p prev) k

def start (row : Rows) (U : UpperSearch) (L : LowerSearch) (s : Nat) : State :=
  Nat.rec initial (fun r prev => visits row U L r prev r) s

def state (row : Rows) (U : UpperSearch) (L : LowerSearch) (s k : Nat) : State :=
  visits row U L s (start row U L s) (min k s)

def chosenPair (row : Rows) (U : UpperSearch) (L : LowerSearch) (s e : Nat) :
    Option (Nat × Nat) :=
  if 2 * e < s then upperAction U s e (state row U L s (2 * e)) else none

def restraints (row : Rows) (U : UpperSearch) (L : LowerSearch) (s e : Nat) : Finset Nat :=
  markerSet (state row U L s (2 * e)).2.1 (2 * e)


-- The table stores 0 for an empty slot and m+1 for a live marker m.
-- Unstored indices decode to empty slots. The two Nat fields are the bit
-- masks for content and completed upper requirements.
private abbrev Table := List Nat
private abbrev Raw := Nat × Table × Nat
private abbrev Input := Nat × Nat × Raw

private def lookup (a : Table) (j : Nat) : Nat := a.getD j 0

private def markerAt (a : Table) (j : Nat) : Option Nat :=
  match lookup a j with
  | 0 => none
  | m + 1 => some m

private def decodeState (a : Raw) : State :=
  (Bits a.1, markerAt a.2.1, a.2.2.testBit)

private def singleMask (a : Table) (p j : Nat) : Nat :=
  if 2 * j + 1 < p ∧ lookup a j ≠ 0 then 2 ^ (lookup a j).pred else 0

private def mask (a : Table) (p : Nat) : Nat :=
  (List.range p).foldr (fun j acc => singleMask a p j ||| acc) 0

private theorem singleMask_bits (a : Table) (p j : Nat) :
    Bits (singleMask a p j) =
      if 2 * j + 1 < p then
        match markerAt a j with
        | none => ∅
        | some m => {m}
      else ∅ := by
  unfold singleMask markerAt
  by_cases h : 2 * j + 1 < p
  · cases he : lookup a j <;> simp [h]
  · simp [h]

private theorem mask_bits (a : Table) (p : Nat) : Bits (mask a p) = markerSet (markerAt a) p := by
  have fold (l : List Nat) (m : Nat) :
      m ∈ Bits (l.foldr (fun j acc => singleMask a p j ||| acc) 0) ↔
        ∃ j ∈ l, m ∈ Bits (singleMask a p j) := by
    induction l with
    | nil => simp
    | cons j l ih =>
      rw [List.foldr_cons, bitsOr, Finset.mem_union, ih]
      simp only [List.mem_cons, exists_eq_or_imp]
  ext m
  simpa only [mask, markerSet, Finset.mem_biUnion, Finset.mem_range, List.mem_range,
    singleMask_bits] using fold (List.range p) m

private def tabulate (n : Nat) (f : Nat → Nat) : Table := (List.range n).map f

private theorem lookupTabulate (n j : Nat) (f : Nat → Nat) :
    lookup (tabulate n f) j = if j < n then f j else 0 := by
  simp only [lookup, tabulate, List.getD_eq_getElem?_getD, List.getElem?_map]
  split
  · simp [List.getElem?_range ‹_›]
  · rw [List.getElem?_eq_none_iff.mpr (by simpa using (Nat.le_of_not_lt ‹¬ j < n›))]
    rfl

private theorem lookupOut (a : Table) (j : Nat) (h : a.length ≤ j) : lookup a j = 0 := by
  simp [lookup, List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr h]

private def cancel (k c : Nat) (a : Table) : Table :=
  tabulate a.length fun j =>
    if k < 2 * j + 1 ∧ c.testBit (lookup a j).pred = true then 0 else lookup a j

private def allocate (e value : Nat) (a : Table) : Table :=
  tabulate (max a.length (e + 1)) fun j => if j = e then value else lookup a j

private theorem lookupCancel (k c : Nat) (a : Table) (j : Nat) :
    lookup (cancel k c a) j =
      if k < 2 * j + 1 ∧ c.testBit (lookup a j).pred = true then 0 else lookup a j := by
  rw [cancel, lookupTabulate]
  split
  · rfl
  · rw [lookupOut a j (by omega)]
    split <;> rfl

private theorem lookupAllocate (e value : Nat) (a : Table) (j : Nat) :
    lookup (allocate e value a) j = if j = e then value else lookup a j := by
  rw [allocate, lookupTabulate]
  split
  · rfl
  · rename_i h
    have hn := Nat.le_of_not_lt h
    have hlen : a.length ≤ j := le_trans (le_max_left ..) hn
    have hne : j ≠ e := by have := le_trans (le_max_right a.length (e + 1)) hn; omega
    simp [hne, lookupOut a j hlen]

private def upperArg (p : Input) : Nat :=
  Nat.pair (p.2.1 / 2) (Nat.pair p.1 (mask p.2.2.2.1 (2 * (p.2.1 / 2))))

private def lowerArg (p : Input) : Nat :=
  Nat.pair (p.2.1 / 2)
    (Nat.pair p.1 (Nat.pair p.2.2.1 (mask p.2.2.2.1 p.1)))

private def rowArg (p : Input × Nat) : Nat × Nat × Nat :=
  (p.1.2.1 / 2, p.2.pred.unpair.1, p.2.pred.unpair.2)

private def combine (b : Input × Nat × Nat × Nat) : Raw :=
  let (p, u, l, c) := b
  let (_, k, a) := p
  let e := k / 2
  if k % 2 = 0 then
    if a.2.2.testBit e = true ∨ u = 0 then a
    else (a.1 ||| c, cancel k c a.2.1, a.2.2 ||| (2 ^ e))
  else
    if lookup a.2.1 e = 0 then (a.1, allocate e l a.2.1, a.2.2) else a

private def rawVisit (row : Rows) (U : UpperSearch) (L : LowerSearch)
    (s k : Nat) (a : Raw) : Raw :=
  let p : Input := (s, k, a)
  let u := upperCode U (upperArg p)
  let l := lowerCode L (lowerArg p)
  let q := rowArg (p, u)
  combine (p, u, l, Bits.symm (row q.1 q.2.1 q.2.2))

private theorem markerCancel (a : Table) (k c j : Nat) :
    markerAt (cancel k c a) j =
      match markerAt a j with
      | none => none
      | some m => if k < 2 * j + 1 ∧ m ∈ Bits c then none else some m := by
  unfold markerAt
  rw [lookupCancel]
  cases h : lookup a j with
  | zero => simp
  | succ m =>
    simp only [Nat.pred_succ, memBits]
    by_cases hm : k < 2 * j + 1 ∧ c.testBit m = true
    · simp only [ite_eq_left hm]
    · simp only [ite_eq_right hm]

private theorem markerAllocate (a : Table) (e j : Nat) (o : Option Nat) :
    markerAt (allocate e (o.elim 0 Nat.succ) a) j = Function.update (markerAt a) e o j := by
  by_cases h : j = e
  · subst j
    simp only [markerAt, lookupAllocate, Function.update_self]
    cases o <;> rfl
  · simp [markerAt, lookupAllocate, h, Function.update_of_ne]

private theorem rawVisit_decode (row : Rows) (U : UpperSearch) (L : LowerSearch)
    (s k : Nat) (a : Raw) :
    decodeState (rawVisit row U L s k a) = visit row U L s k (decodeState a) := by
  simp only [rawVisit, upperArg, lowerArg, upperCode, lowerCode, Nat.unpair_pair, mask_bits,
    combine, visit, upperAction, decodeState]
  let e := k / 2
  change (decodeState (if k % 2 = 0 then _ else _)) = _
  by_cases h : k % 2 = 0
  · simp only [ite_eq_left h]
    by_cases hd : a.2.2.testBit (k / 2) = true
    · simp [hd, decodeState]
    · cases hu : U (k / 2) s (markerSet (markerAt a.2.1) (2 * (k / 2))) with
      | none => simp [hd, decodeState]
      | some q =>
        rcases q with ⟨x,t⟩
        simp only [hd, Bool.false_eq_true, false_or, Nat.succ_ne_zero, ite_false, rowArg,
          Nat.pred_succ, Nat.unpair_pair, decodeState, bitsOr, Equiv.apply_symm_apply,
          Prod.mk.injEq, true_and]
        constructor
        · funext j
          rw [markerCancel, Equiv.apply_symm_apply]
        · funext j
          by_cases hj : j = k / 2
          · subst j
            simp
          · simp [Ne.symm hj, Function.update_of_ne hj]
  · simp only [ite_eq_right h]
    cases hl : lookup a.2.1 e with
    | zero =>
      have hm : markerAt a.2.1 (k / 2) = none := by simp [markerAt, ← show e = k / 2 from rfl, hl]
      simp only [hm, ite_true, decodeState,
        Prod.mk.injEq, true_and, and_true]
      cases hL : L e s (Bits a.1) (markerSet (markerAt a.2.1) s) with
      | none =>
        exact funext (fun j => markerAllocate a.2.1 e j none)
      | some m =>
        exact funext (fun j => markerAllocate a.2.1 e j (some m))
    | succ m =>
      have hm : markerAt a.2.1 (k / 2) = some m := by
        simp [markerAt, ← show e = k / 2 from rfl, hl]
      simp [hm, decodeState]


private theorem primLookup : Primrec₂ lookup := Primrec.list_getD 0

private theorem primLowerIndex : Primrec (fun j : Nat => 2 * j + 1) := Primrec.nat_double_succ

private theorem primMask : Primrec₂ mask := by
  -- The parameter of the fold is (table, priority cutoff).
  let cut : Table × Nat → Nat := Prod.snd
  let j : (Table × Nat) × (Nat × Nat) → Nat := fun q => q.2.1
  let tbl : (Table × Nat) × (Nat × Nat) → Table := fun q => q.1.1
  have hj : Primrec j := Primrec.fst.comp Primrec.snd
  have ht : Primrec tbl := Primrec.fst.comp Primrec.fst
  have hv := primLookup.comp ht hj
  have hp : Primrec (fun q : (Table × Nat) × (Nat × Nat) => cut q.1) :=
    Primrec.snd.comp Primrec.fst
  have hl := Primrec.nat_lt.comp (primLowerIndex.comp hj) hp
  have hn := (Primrec.eq.comp hv (Primrec.const 0)).not
  have hm : Primrec (fun q => singleMask (tbl q) (cut q.1) (j q)) :=
    Primrec.ite (hl.and hn) (powTwo.comp (Primrec.pred.comp hv)) (Primrec.const 0)
  exact Primrec.list_foldr (Primrec.list_range.comp (Primrec.snd : Primrec cut))
    (Primrec.const 0) (primOr.comp hm (Primrec.snd.comp Primrec.snd)).to₂

private theorem primCancel : Primrec (fun p : Nat × Nat × Table => cancel p.1 p.2.1 p.2.2) := by
  let P := Nat × Nat × Table
  have ht : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have hj : Primrec (fun p : P × Nat => p.2) := Primrec.snd
  have hv := primLookup.comp (ht.comp Primrec.fst) hj
  have hb := bitTest.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst :
    Primrec (Prod.fst : P × Nat → P)))) (Primrec.pred.comp hv)
  have hk : Primrec (fun p : P × Nat => p.1.1) := Primrec.fst.comp Primrec.fst
  unfold cancel tabulate
  exact Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp ht))
    (Primrec.ite ((Primrec.nat_lt.comp hk (primLowerIndex.comp hj)).and
      (Primrec.eq.comp hb (Primrec.const true))) (Primrec.const 0) hv)

private theorem primAllocate :
    Primrec (fun p : Nat × Nat × Table => allocate p.1 p.2.1 p.2.2) := by
  let P := Nat × Nat × Table
  have ht : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have he : Primrec (fun p : P => p.1) := Primrec.fst
  have hv : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  unfold allocate tabulate
  exact Primrec.list_map (Primrec.list_range.comp
    (Primrec.nat_max.comp (Primrec.list_length.comp ht) (Primrec.succ.comp he)))
    (Primrec.ite (Primrec.eq.comp Primrec.snd (he.comp Primrec.fst))
      (hv.comp Primrec.fst) (primLookup.comp (ht.comp Primrec.fst) Primrec.snd))

private theorem primStage : Primrec (fun p : Input => p.1) := Primrec.fst
private theorem primVisitIndex : Primrec (fun p : Input => p.2.1) := Primrec.fst.comp Primrec.snd
private theorem primRaw : Primrec (fun p : Input => p.2.2) := Primrec.snd.comp Primrec.snd
private theorem primIndex : Primrec (fun p : Input => p.2.1 / 2) :=
  Primrec.nat_div.comp primVisitIndex (Primrec.const 2)

private theorem primUpperArg : Primrec upperArg :=
  Primrec₂.natPair.comp primIndex (Primrec₂.natPair.comp primStage
    (primMask.comp (Primrec.fst.comp (Primrec.snd.comp primRaw))
      (Primrec.nat_double.comp primIndex)))

private theorem primLowerArg : Primrec lowerArg :=
  Primrec₂.natPair.comp primIndex (Primrec₂.natPair.comp primStage
    (Primrec₂.natPair.comp (Primrec.fst.comp primRaw)
      (primMask.comp (Primrec.fst.comp (Primrec.snd.comp primRaw)) primStage)))

private theorem primRowArg : Primrec rowArg :=
  (primIndex.comp Primrec.fst).pair (Primrec.unpair.comp (Primrec.pred.comp Primrec.snd))

private theorem primCombine : Primrec combine := by
  let B := Input × Nat × Nat × Nat
  have hi : Primrec (Prod.fst : B → Input) := Primrec.fst
  have he := primIndex.comp hi
  have hk := primVisitIndex.comp hi
  have ha := primRaw.comp hi
  have hc : Primrec (fun b : B => b.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hu : Primrec (fun b : B => b.2.1) := Primrec.fst.comp Primrec.snd
  have hl : Primrec (fun b : B => b.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ht := Primrec.fst.comp (Primrec.snd.comp ha)
  have hd := Primrec.snd.comp (Primrec.snd.comp ha)
  have hn := Primrec.fst.comp ha
  have upper := (primOr.comp hn hc).pair
    ((primCancel.comp (hk.pair (hc.pair ht))).pair (primOr.comp hd (powTwo.comp he)))
  have lower := hn.pair ((primAllocate.comp (he.pair (hl.pair ht))).pair hd)
  unfold combine
  exact Primrec.ite (Primrec.eq.comp (Primrec.nat_mod.comp hk (Primrec.const 2))
    (Primrec.const 0)) (Primrec.ite ((Primrec.eq.comp (bitTest.comp hd he)
      (Primrec.const true)).or (Primrec.eq.comp hu (Primrec.const 0))) ha upper)
    (Primrec.ite (Primrec.eq.comp (primLookup.comp ht he) (Primrec.const 0)) lower ha)

private abbrev Total (O : Set (Nat →. Nat)) (f : Nat → Nat) :=
  Nat.RecursiveIn O (fun n => Part.some (f n))

private theorem lift {O : Set (Nat →. Nat)} {f : Nat → Nat} (hf : Computable f) :
    Total O f :=
  RecursiveIn.iff_nat.mp hf.computableIn

private theorem comp {O : Set (Nat →. Nat)} {f g : Nat → Nat}
    (hf : Total O f) (hg : Total O g) : Total O (fun n => f (g n)) :=
  (Nat.RecursiveIn.comp hf hg).of_eq (fun _ => Part.bind_some _ _)

private theorem pair {O : Set (Nat →. Nat)} {f g : Nat → Nat}
    (hf : Total O f) (hg : Total O g) : Total O (fun n => Nat.pair (f n) (g n)) :=
  (Nat.RecursiveIn.pair hf hg).of_eq (fun n => by
    change Part.map Nat.pair (Part.some (f n)) <*> Part.some (g n) = _
    rw [Part.map_some, ← Part.pure_eq_some (Nat.pair (f n)), pure_seq]
    exact Part.map_some _ _)

private theorem prec {O : Set (Nat →. Nat)} {base step : Nat → Nat}
    (hb : Total O base) (hs : Total O step) :
    Total O (fun p =>
      let (a,n) := p.unpair
      Nat.rec (base a) (fun k acc => step (Nat.pair a (Nat.pair k acc))) n) := by
  refine (Nat.RecursiveIn.prec hb hs).of_eq ?_
  intro p
  dsimp only
  cases hp : p.unpair with
  | mk a n =>
   clear hp p
   induction n with
   | zero => rfl
   | succ n ih =>
     change Part.bind _ _ = _
     rw [ih, Part.bind_some]

private def decoded {α : Type} [Encodable α] (d : α) (n : Nat) : α :=
  (Encodable.decode n).getD d

private theorem primDecoded {α : Type} [Primcodable α] (d : α) : Primrec (decoded d) :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const d)

private theorem decoded_encode {α : Type} [Encodable α] (d x : α) :
    decoded d (Encodable.encode x) = x := by simp [decoded, Encodable.encodek]

private def rawInitial : Raw := (0, [], 0)
private def inputDefault : Input := (0, 0, rawInitial)

private def codedVisit (row : Rows) (U : UpperSearch) (L : LowerSearch) (n : Nat) : Nat :=
  let p := decoded inputDefault n
  Encodable.encode (rawVisit row U L p.1 p.2.1 p.2.2)

private theorem codedVisit_total
    (row : Rows) (U : UpperSearch) (L : LowerSearch) (O : Set (Nat →. Nat))
    (hrow : Computable (fun p : Nat × Nat × Nat => Bits.symm (row p.1 p.2.1 p.2.2)))
    (hu : Total O (upperCode U)) (hl : Total O (lowerCode L)) :
    Total O (codedVisit row U L) := by
  classical
  let a := decoded inputDefault
  let u n := upperCode U (upperArg (a n))
  let l n := lowerCode L (lowerArg (a n))
  let b : Nat × Nat → Input × Nat := fun p => (a p.1, p.2)
  have ha := primDecoded inputDefault
  have hb : Primrec b := (ha.comp Primrec.fst).pair Primrec.snd
  have hu' : Total O u := comp hu (lift (primUpperArg.comp ha).to_comp)
  have hl' : Total O l := comp hl (lift (primLowerArg.comp ha).to_comp)
  have hc : Total O (fun n =>
      Bits.symm (row (rowArg (a n, u n)).1 (rowArg (a n, u n)).2.1
        (rowArg (a n, u n)).2.2)) :=
    (comp (lift (hrow.comp ((primRowArg.comp hb).to_comp.comp Computable.unpair)))
      (pair (lift Computable.id) hu')).of_eq (fun _ => by simp only [Nat.unpair_pair, b, id_eq])
  have htail : Primrec (fun n : Nat => n.unpair.2.unpair) :=
    Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)
  have hpost : Computable (fun n : Nat => Encodable.encode
      (combine (a n.unpair.1, n.unpair.2.unpair.1,
        n.unpair.2.unpair.2.unpair.1, n.unpair.2.unpair.2.unpair.2))) :=
    (Primrec.encode.comp (primCombine.comp
      ((ha.comp (Primrec.fst.comp Primrec.unpair)).pair
        ((Primrec.fst.comp htail).pair (Primrec.unpair.comp (Primrec.snd.comp htail)))))).to_comp
  -- All three functions supplied to this composition are total. Its selector
  -- only commits the branch specified by the parity, done flag and live marker.
  exact (comp (lift hpost) (pair (lift Computable.id) (pair hu' (pair hl' hc)))).of_eq
    (fun n => by simp only [Nat.unpair_pair, codedVisit, rawVisit, a, u, l, id_eq])


private def innerStep (row : Rows) (U : UpperSearch) (L : LowerSearch) (n : Nat) : Nat :=
  codedVisit row U L (Encodable.encode
    (n.unpair.1.unpair.1, n.unpair.2.unpair.1, decoded rawInitial n.unpair.2.unpair.2))

private def inner (row : Rows) (U : UpperSearch) (L : LowerSearch) (n : Nat) : Nat :=
  let (a, k) := n.unpair
  Nat.rec a.unpair.2 (fun j acc => innerStep row U L (Nat.pair a (Nat.pair j acc))) k

private theorem inner_total (row : Rows) (U : UpperSearch) (L : LowerSearch)
    (O : Set (Nat →. Nat)) (hv : Total O (codedVisit row U L)) :
    Total O (inner row U L) := by
  have hleft : Primrec (fun n : Nat => n.unpair.1.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
  have hright : Primrec (fun n : Nat => n.unpair.2.unpair) :=
    Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)
  have harg : Primrec (fun n : Nat =>
      Encodable.encode (n.unpair.1.unpair.1, n.unpair.2.unpair.1,
        decoded rawInitial n.unpair.2.unpair.2)) :=
    Primrec.encode.comp (hleft.pair ((Primrec.fst.comp hright).pair
      ((primDecoded rawInitial).comp (Primrec.snd.comp hright))))
  have ht : Total O (innerStep row U L) := by
    unfold innerStep
    exact comp (f := codedVisit row U L) hv (lift harg.to_comp)
  unfold inner
  exact prec (base := fun a => a.unpair.2) (step := innerStep row U L)
    (lift (Primrec.snd.comp Primrec.unpair).to_comp) ht

private theorem inner_decode (row : Rows) (U : UpperSearch) (L : LowerSearch)
    (s k v : Nat) :
    decodeState (decoded rawInitial (inner row U L (Nat.pair (Nat.pair s v) k))) =
      visits row U L s (decodeState (decoded rawInitial v)) k := by
  induction k with
  | zero => simp [inner, visits, Nat.unpair_pair]
  | succ k ih =>
    simp only [inner, Nat.unpair_pair] at ih ⊢
    change decodeState (decoded rawInitial (innerStep row U L
      (Nat.pair (Nat.pair s v) (Nat.pair k _)))) = visit row U L s k _
    have hs j acc : innerStep row U L (Nat.pair (Nat.pair s v) (Nat.pair j acc)) =
        Encodable.encode (rawVisit row U L s j (decoded rawInitial acc)) := by
      simp only [innerStep, Nat.unpair_pair, codedVisit, decoded_encode]
    rw [hs, decoded_encode, rawVisit_decode, ih]; rfl

private def outerStep (row : Rows) (U : UpperSearch) (L : LowerSearch) (n : Nat) : Nat :=
  inner row U L (Nat.pair (Nat.pair n.unpair.2.unpair.1 n.unpair.2.unpair.2)
    n.unpair.2.unpair.1)

private def outer (row : Rows) (U : UpperSearch) (L : LowerSearch) (s : Nat) : Nat :=
  Nat.rec (Encodable.encode rawInitial)
    (fun r prev => outerStep row U L (Nat.pair 0 (Nat.pair r prev))) s

private theorem outer_total (row : Rows) (U : UpperSearch) (L : LowerSearch)
    (O : Set (Nat →. Nat)) (hi : Total O (inner row U L)) :
    Total O (outer row U L) := by
  have htail := Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)
  have harg : Primrec (fun n : Nat =>
      Nat.pair (Nat.pair n.unpair.2.unpair.1 n.unpair.2.unpair.2) n.unpair.2.unpair.1) :=
    Primrec₂.natPair.comp (Primrec₂.natPair.comp (Primrec.fst.comp htail)
      (Primrec.snd.comp htail)) (Primrec.fst.comp htail)
  have hs : Total O (outerStep row U L) := by
    unfold outerStep
    exact comp (f := inner row U L) hi (lift harg.to_comp)
  exact (comp (prec (lift (Computable.const (Encodable.encode rawInitial))) hs)
    (lift (Primrec₂.natPair.comp (Primrec.const 0) Primrec.id).to_comp)).of_eq
      (fun n => by simp only [Nat.unpair_pair, outer, id_eq])

private theorem outer_decode (row : Rows) (U : UpperSearch) (L : LowerSearch) (s : Nat) :
    decodeState (decoded rawInitial (outer row U L s)) = start row U L s := by
  induction s with
  | zero =>
    change decodeState (decoded rawInitial (Encodable.encode rawInitial)) = initial
    rw [decoded_encode]
    have hmarker : markerAt [] = fun _ => none := by
      funext j
      simp [markerAt, lookup]
    have hdone : Nat.testBit 0 = fun _ => false := funext Nat.zero_testBit
    simp only [decodeState, rawInitial, initial, bitsZero, hmarker, hdone]
  | succ s ih =>
    change decodeState (decoded rawInitial
      (outerStep row U L (Nat.pair 0 (Nat.pair s (outer row U L s))))) =
        visits row U L s (start row U L s) s
    simp only [outerStep, Nat.unpair_pair, inner_decode, ih]

/-- The input is the pair of the stage number and the number of visits requested. -/
def traceCode (row : Rows) (U : UpperSearch) (L : LowerSearch) (n : Nat) : Nat :=
  inner row U L
    (Nat.pair (Nat.pair n.unpair.1 (outer row U L n.unpair.1)) (min n.unpair.2 n.unpair.1))

private theorem traceCode_total (row : Rows) (U : UpperSearch) (L : LowerSearch)
    (O : Set (Nat →. Nat)) (hi : Total O (inner row U L))
    (ho : Total O (outer row U L)) : Total O (traceCode row U L) := by
  have hs : Primrec (fun n : Nat => n.unpair.1) := Primrec.fst.comp Primrec.unpair
  have hk : Primrec (fun n : Nat => n.unpair.2) := Primrec.snd.comp Primrec.unpair
  unfold traceCode
  exact comp (f := inner row U L) hi (pair (pair (lift hs.to_comp)
    (comp (f := outer row U L) ho (lift hs.to_comp))) (lift (Primrec.nat_min.comp hk hs).to_comp))

def decodeVisitCode (n : Nat) : State :=
  decodeState (decoded rawInitial n)

/-- Decoding a visit code gives the nested recursion used by the article. -/
theorem traceCode_decode (row : Rows) (U : UpperSearch) (L : LowerSearch) (s k : Nat) :
    decodeVisitCode (traceCode row U L (Nat.pair s k)) = state row U L s k := by
  simp only [decodeVisitCode, traceCode, Nat.unpair_pair, inner_decode, outer_decode, state]

private theorem restraint_code_eq (row : Rows) (U : UpperSearch) (L : LowerSearch)
    (s e : Nat) :
    mask (decoded rawInitial (traceCode row U L (Nat.pair s (2 * e)))).2.1 (2 * e) =
      Bits.symm (restraints row U L s e) := by
  apply Bits.injective
  rw [mask_bits, Equiv.apply_symm_apply]
  have he := congrArg (fun a : State => a.2.1) (traceCode_decode row U L s (2 * e))
  simp only [decodeVisitCode, decodeState] at he
  unfold restraints
  rw [he]

theorem traceComputations (row : Rows) (U : UpperSearch) (L : LowerSearch) (O : Set (Nat →. Nat))
    (hrow : Computable (fun p : Nat × Nat × Nat => Bits.symm (row p.1 p.2.1 p.2.2)))
    (hu : Nat.RecursiveIn O (fun n => Part.some (upperCode U n)))
    (hl : Nat.RecursiveIn O (fun n => Part.some (lowerCode L n))) :
    Nat.RecursiveIn O (fun n => Part.some (traceCode row U L n)) ∧
    Nat.RecursiveIn O (fun s => Part.some (Bits.symm (state row U L s s).1)) ∧
    Nat.RecursiveIn O (fun n => Part.some
      (Bits.symm (restraints row U L n.unpair.1 n.unpair.2))) := by
  have hv := codedVisit_total row U L O hrow hu hl
  have hi := inner_total row U L O hv
  have ht := traceCode_total row U L O hi (outer_total row U L O hi)
  refine ⟨ht, ?_, ?_⟩
  · have ha : Primrec (fun n : Nat => (decoded rawInitial n).1) :=
      Primrec.fst.comp (primDecoded rawInitial)
    refine (comp (lift ha.to_comp) (comp ht (lift
      (Primrec₂.natPair.comp Primrec.id Primrec.id).to_comp))).of_eq ?_
    intro s
    have he := congrArg Prod.fst (traceCode_decode row U L s s)
    simp only [decodeVisitCode, decodeState] at he
    change Part.some (decoded rawInitial (traceCode row U L (Nat.pair s s))).1 = _
    rw [← he, Equiv.symm_apply_apply]
  · have harg : Primrec (fun n : Nat => Nat.pair n.unpair.1 (2 * n.unpair.2)) :=
      Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
        (Primrec.nat_double.comp (Primrec.snd.comp Primrec.unpair))
    have htable : Primrec (fun n => (decoded rawInitial n).2.1) :=
      Primrec.fst.comp (Primrec.snd.comp (primDecoded rawInitial))
    have hp : Primrec (fun n : Nat => 2 * n.unpair.2) :=
      Primrec.nat_double.comp (Primrec.snd.comp Primrec.unpair)
    have hpost : Primrec (fun n : Nat => mask (decoded rawInitial n.unpair.1).2.1 n.unpair.2) :=
      primMask.comp (htable.comp (Primrec.fst.comp Primrec.unpair))
        (Primrec.snd.comp Primrec.unpair)
    refine (comp (lift hpost.to_comp) (pair (comp ht (lift harg.to_comp))
      (lift hp.to_comp))).of_eq ?_
    intro n
    simp only [Nat.unpair_pair]
    exact congrArg Part.some (restraint_code_eq row U L n.unpair.1 n.unpair.2)


section Laws

variable {φ : Nat → Nat → Part Nat} {row : Rows} {M : Set Nat}
  {U : UpperSearch} {L : LowerSearch}
  {before : (Nat × Nat) → (Nat × Nat) → Prop}

private def remaining (k : Nat) (F : Finset Nat) (marker : Nat → Option Nat) (j : Nat) :
    Option Nat :=
  match marker j with
  | none => none
  | some m => if k < 2 * j + 1 ∧ m ∈ F then none else some m

private theorem upperVisit (s i : Nat) (a : State) :
    visit row U L s (2 * i) a =
      match upperAction U s i a with
      | none => a
      | some (x,t) =>
        (a.1 ∪ row i x t, remaining (2 * i) (row i x t) a.2.1, Function.update a.2.2 i true) := by
  have hm : (2 * i) % 2 = 0 := by omega
  have hd : (2 * i) / 2 = i := by omega
  simp only [visit, hm, hd, ite_true]
  rfl

private theorem lowerVisit (s i : Nat) (a : State) :
    visit row U L s (2 * i + 1) a =
      match a.2.1 i with
      | none => (a.1, Function.update a.2.1 i (L i s a.1 (markerSet a.2.1 s)), a.2.2)
      | some _ => a := by
  have hm : ¬ (2 * i + 1) % 2 = 0 := by omega
  have hd : (2 * i + 1) / 2 = i := by omega
  simp only [visit, hm, hd, ite_false]
  cases a.2.1 i <;> rfl

private theorem updateSame (marker : Nat → Option Nat) (i : Nat) :
    Function.update marker i (marker i) = marker := by
  funext j
  by_cases h : j = i
  · subst j; simp
  · exact Function.update_of_ne h _ _

private inductive Step (row : Rows) (U : UpperSearch) (L : LowerSearch)
    (s k : Nat) (a : State) : State → Prop
  | unchanged : Step row U L s k a a
  | upper (i : Nat) (q : Nat × Nat) (hk : k = 2 * i)
      (hq : upperAction U s i a = some q) :
      Step row U L s k a
        (a.1 ∪ row i q.1 q.2, remaining k (row i q.1 q.2) a.2.1, Function.update a.2.2 i true)
  | lower (i m : Nat) (hk : k = 2 * i + 1) (hi : a.2.1 i = none)
      (hm : L i s a.1 (markerSet a.2.1 s) = some m) :
      Step row U L s k a (a.1, Function.update a.2.1 i (some m), a.2.2)

private theorem step (s k : Nat) (a : State) :
    Step row U L s k a (visit row U L s k a) := by
  let i := k / 2
  by_cases h : k % 2 = 0
  · have hk : k = 2 * i := by dsimp [i]; omega
    rw [hk, upperVisit]
    cases hq : upperAction U s i a with
    | none => exact .unchanged
    | some q =>
      rcases q with ⟨x,t⟩
      exact .upper _ _ rfl hq
  · have hk : k = 2 * i + 1 := by dsimp [i]; omega
    rw [hk, lowerVisit]
    cases hi : a.2.1 i with
    | some m => exact .unchanged
    | none =>
      cases hm : L i s a.1 (markerSet a.2.1 s) with
      | some m => exact .lower _ _ rfl hi hm
      | none =>
        change Step row U L s (2 * i + 1) a (a.1, Function.update a.2.1 i none, a.2.2)
        rw [← hi, updateSame]
        cases a; exact .unchanged

private theorem upperSome (hU : UpperCorrect row before U) {s i : Nat} {a : State}
    {q : Nat × Nat} (hq : upperAction U s i a = some q) :
    a.2.2 i = false ∧ UpperCandidate row i s (markerSet a.2.1 (2 * i)) q := by
  have hb : a.2.2 i ≠ true := by
    intro h
    simp [upperAction, h] at hq
  have hf : a.2.2 i = false := Bool.eq_false_iff.mpr hb
  have hu : U i s (markerSet a.2.1 (2 * i)) = some q := by
    simpa [upperAction, hf] using hq
  have hc := hU i s (markerSet a.2.1 (2 * i))
  rw [hu] at hc
  exact ⟨hf, hc.1⟩

private theorem lowerSome (hL : LowerCorrect φ M L) {s i : Nat} {a : State}
    {m : Nat} (hm : L i s a.1 (markerSet a.2.1 s) = some m) :
    LowerCandidate φ M i s a.1 (markerSet a.2.1 s) m := by
  have hc := hL i s a.1 (markerSet a.2.1 s)
  rw [hm] at hc
  exact hc.1

private theorem remainingSome {k : Nat} {F : Finset Nat}
    {marker : Nat → Option Nat} {j m : Nat} (hm : remaining k F marker j = some m) :
    marker j = some m ∧ ¬ (k < 2 * j + 1 ∧ m ∈ F) := by
  unfold remaining at hm
  cases he : marker j with
  | none => simp [he] at hm
  | some n =>
    by_cases h : k < 2 * j + 1 ∧ n ∈ F
    · simp only [he, ite_eq_left h, reduceCtorEq] at hm
    · simp only [he, ite_eq_right h, Option.some.injEq] at hm
      subst m
      exact ⟨rfl, h⟩

private theorem remainingNone {k : Nat} {F : Finset Nat}
    {marker : Nat → Option Nat} {j m : Nat} (hm : marker j = some m)
    (hn : remaining k F marker j = none) : k < 2 * j + 1 ∧ m ∈ F := by
  by_cases h : k < 2 * j + 1 ∧ m ∈ F
  · exact h
  · simp only [remaining, hm, ite_eq_right h, reduceCtorEq] at hn

private structure Valid (φ : Nat → Nat → Part Nat) (M : Set Nat) (s : Nat) (a : State) : Prop where
  contentBound : ∀ m ∈ a.1, m ≤ s
  markerBound : ∀ i m, a.2.1 i = some m → m ≤ s
  visited : ∀ i m, a.2.1 i = some m → 2 * i + 1 < s
  active : ∀ i m, a.2.1 i = some m → m ∈ M ∧ ¬ (φ i m).Dom ∧ m ∉ a.1
  unique : ∀ i j m, a.2.1 i = some m → a.2.1 j = some m → i = j

private theorem validInitial : Valid φ M s initial := by
  constructor <;> simp [initial]

private theorem validSucc {s : Nat} {a : State} (h : Valid φ M s a) :
    Valid φ M (s + 1) a :=
  ⟨fun m hm => (h.contentBound m hm).step, fun i m hm => (h.markerBound i m hm).step,
    fun i m hm => Nat.lt_succ_of_lt (h.visited i m hm), h.active, h.unique⟩

private theorem stepValid (hU : UpperCorrect row before U) (hL : LowerCorrect φ M L)
    {s k : Nat} {a b : State} (hk : k < s) (ha : Valid φ M s a)
    (tr : Step row U L s k a b) : Valid φ M s b := by
  cases tr with
  | unchanged => exact ha
  | upper i q hi hq =>
    have hc := (upperSome hU hq).2
    constructor
    · intro m hm
      rcases Finset.mem_union.mp hm with hm | hm
      · exact ha.contentBound _ hm
      · exact (hc.2.2.1 _ hm).1
    · exact fun j m hm => ha.markerBound _ _ (remainingSome hm).1
    · exact fun j m hm => ha.visited _ _ (remainingSome hm).1
    · intro j m hm
      obtain ⟨old, kept⟩ := remainingSome hm
      obtain ⟨hM, hD, hC⟩ := ha.active _ _ old
      refine ⟨hM, hD, fun h => ?_⟩
      rcases Finset.mem_union.mp h with h | h
      · exact hC h
      · by_cases hp : k < 2 * j + 1
        · exact kept ⟨hp, h⟩
        · have hp' : 2 * j + 1 < 2 * i := by omega
          exact (hc.2.2.1 _ h).2 ((memMarkerSet _ _ _).mpr ⟨j, hp', old⟩)
    · exact fun j l m hj hl => ha.unique _ _ _ (remainingSome hj).1 (remainingSome hl).1
  | lower i n hi _ hn =>
    have hc := lowerSome hL hn
    have fresh (j : Nat) : a.2.1 j ≠ some n := fun hj =>
      hc.2.2.2.2 ((memMarkerSet _ _ _).mpr ⟨j, ha.visited _ _ hj, hj⟩)
    have update (j m : Nat) (h : Function.update a.2.1 i (some n) j = some m) :
        (j = i ∧ m = n) ∨ (j ≠ i ∧ a.2.1 j = some m) := by
      by_cases hj : j = i
      · subst j
        exact .inl ⟨rfl, (Option.some.inj (by simpa using h)).symm⟩
      · exact .inr ⟨hj, by simpa only [Function.update_of_ne hj] using h⟩
    constructor
    · exact ha.contentBound
    · intro j m hm
      rcases update _ _ hm with ⟨rfl, rfl⟩ | ⟨_, old⟩
      · exact hc.1
      · exact ha.markerBound _ _ old
    · intro j m hm
      rcases update _ _ hm with ⟨rfl, rfl⟩ | ⟨_, old⟩
      · omega
      · exact ha.visited _ _ old
    · intro j m hm
      rcases update _ _ hm with ⟨rfl, rfl⟩ | ⟨_, old⟩
      · exact ⟨hc.2.1, hc.2.2.1, hc.2.2.2.1⟩
      · exact ha.active _ _ old
    · intro j l m hj hl
      rcases update _ _ hj with ⟨hj', hmj⟩ | ⟨_, oldj⟩
      · rcases update _ _ hl with ⟨hl', _⟩ | ⟨_, oldl⟩
        · exact hj'.trans hl'.symm
        · exact (fresh _ (hmj ▸ oldl)).elim
      · rcases update _ _ hl with ⟨_, hml⟩ | ⟨_, oldl⟩
        · exact (fresh _ (hml ▸ oldj)).elim
        · exact ha.unique _ _ _ oldj oldl

private theorem visitsValid (hU : UpperCorrect row before U) (hL : LowerCorrect φ M L)
    {s : Nat} {a : State} (ha : Valid φ M s a) (k : Nat) (hk : k ≤ s) :
    Valid φ M s (visits row U L s a k) := by
  induction k with
  | zero => exact ha
  | succ k ih =>
    exact stepValid hU hL (by omega) (ih (by omega)) (step s k _)

private theorem startValid (hU : UpperCorrect row before U) (hL : LowerCorrect φ M L)
    (s : Nat) : Valid φ M s (start row U L s) := by
  induction s with
  | zero => exact validInitial
  | succ s ih => exact validSucc (visitsValid hU hL ih s le_rfl)

private theorem stateValid (hU : UpperCorrect row before U) (hL : LowerCorrect φ M L)
    (s k : Nat) : Valid φ M s (state row U L s k) :=
  visitsValid hU hL (startValid hU hL s) (min k s) (min_le_right ..)

theorem state_zero (s : Nat) : state row U L s 0 = start row U L s := by
  simp [state, visits]

theorem state_carry (s : Nat) : state row U L (s + 1) 0 = state row U L s s := by
  rw [state_zero]
  simp only [state, min_self]
  rfl

theorem state_next (s k : Nat) (hk : k < s) :
    state row U L s (k + 1) = visit row U L s k (state row U L s k) := by
  simp only [state, Nat.min_eq_left (show k + 1 ≤ s by omega),
    Nat.min_eq_left (show k ≤ s by omega)]
  rfl

private theorem stepContent {s k : Nat} {a b : State} (h : Step row U L s k a b) :
    a.1 ⊆ b.1 := by
  cases h with
  | upper => exact Finset.subset_union_left
  | _ => exact Finset.Subset.rfl

theorem content_mono (s j k : Nat) (hjk : j ≤ k) (hk : k ≤ s) :
    (state row U L s j).1 ⊆ (state row U L s k).1 := by
  induction k, hjk using Nat.le_induction with
  | base => exact Finset.Subset.rfl
  | succ k _ ih =>
    rw [state_next s k (by omega)]
    exact (ih (by omega)).trans (stepContent (step s k _))

end Laws


section Certificate

variable {φ : Nat → Nat → Part Nat} {row : Rows} {M : Set Nat}
  {U : UpperSearch} {L : LowerSearch}
  {before : (Nat × Nat) → (Nat × Nat) → Prop}

abbrev content (row : Rows) (U : UpperSearch) (L : LowerSearch) (s k : Nat) :=
  (state row U L s k).1

abbrev marker (row : Rows) (U : UpperSearch) (L : LowerSearch) (s k e : Nat) :=
  (state row U L s k).2.1 e

def done (row : Rows) (U : UpperSearch) (L : LowerSearch) (s e : Nat) : Prop :=
  (state row U L s 0).2.2 e = true

private theorem chosen_at (s i : Nat) (hi : 2 * i < s) :
    chosenPair row U L s i = upperAction U s i (state row U L s (2 * i)) := by
  exact ite_eq_left hi

private theorem flag_same (s k e : Nat) (a : State) (hne : k ≠ 2 * e) :
    (visit row U L s k a).2.2 e = a.2.2 e := by
  have hstep := step (row := row) (U := U) (L := L) s k a
  generalize hresult : visit row U L s k a = result at hstep ⊢
  cases hstep with
  | unchanged => rfl
  | lower => rfl
  | upper i _ hi _ =>
    exact Function.update_of_ne (show e ≠ i by intro h; subst i; exact hne hi) _ _

private theorem flag_at (s e : Nat) (a : State) :
    (visit row U L s (2 * e) a).2.2 e = true ↔
      a.2.2 e = true ∨ (upperAction U s e a).isSome = true := by
  rw [upperVisit]
  cases h : upperAction U s e a with
  | none => simp
  | some q => rcases q with ⟨x,t⟩; simp

private theorem flag_state (s k e : Nat) (hk : k ≤ s) :
    (state row U L s k).2.2 e = true ↔
      done row U L s e ∨ (2 * e < k ∧ (chosenPair row U L s e).isSome = true) := by
  induction k with
  | zero => simp [done]
  | succ k ih =>
    have hs : k < s := by omega
    rw [state_next s k hs]
    by_cases h : k = 2 * e
    · subst k
      rw [flag_at, ← chosen_at s e hs, ih (by omega)]
      simp
    · rw [flag_same s k e _ h, ih (by omega)]
      have he : 2 * e < k + 1 ↔ 2 * e < k := by omega
      rw [he]

/-- Trace laws for the priority verification, stated without importing the parent. -/
structure Laws (φ : Nat → Nat → Part Nat) (row : Rows) (M : Set Nat)
    (U : UpperSearch) (L : LowerSearch) : Prop where
  contentInitial : content row U L 0 0 = ∅
  markerInitial : ∀ e, marker row U L 0 0 e = none
  doneInitial : ∀ e, ¬ done row U L 0 e
  contentCarry : ∀ s, content row U L (s + 1) 0 = content row U L s s
  markerCarry : ∀ s e, marker row U L (s + 1) 0 e = marker row U L s s e
  contentPersists : ∀ s j k, j ≤ k → k ≤ s → content row U L s j ⊆ content row U L s k
  doneNext : ∀ s e, done row U L (s + 1) e ↔ done row U L s e ∨ (chosenPair row U L s e).isSome
  action : ∀ s e q, chosenPair row U L s e = some q →
    2 * e < s ∧ ¬ done row U L s e ∧ UpperCandidate row e s (restraints row U L s e) q ∧
    row e q.1 q.2 ⊆ content row U L s s
  upperProgress : ∀ s e q, 2 * e < s → ¬ done row U L s e →
    UpperCandidate row e s (restraints row U L s e) q → (chosenPair row U L s e).isSome
  lowerProgress : ∀ s e m, 2 * e + 1 < s → marker row U L s (2 * e + 1) e = none →
    m ≤ s → m ∈ M → ¬ (φ e m).Dom → m ∉ content row U L s (2 * e + 1) →
    (∀ j, marker row U L s (2 * e + 1) j ≠ some m) → (marker row U L s (2 * e + 2) e).isSome
  enterContent : ∀ s k m, k < s → m ∈ content row U L s (k + 1) → m ∉ content row U L s k →
    ∃ i q, k = 2 * i ∧ chosenPair row U L s i = some q ∧ m ∈ row i q.1 q.2
  enterMarker : ∀ s k e m, k < s → marker row U L s (k + 1) e = some m →
    marker row U L s k e ≠ some m → k = 2 * e + 1 ∧ m ≤ s
  active : ∀ s k e m, marker row U L s k e = some m →
    m ∈ M ∧ ¬ (φ e m).Dom ∧ m ∉ content row U L s k
  cancellation : ∀ s k e m, k < s → marker row U L s k e = some m →
    marker row U L s (k + 1) e = none →
    ∃ i q, k = 2 * i ∧ 2 * i < 2 * e + 1 ∧ chosenPair row U L s i = some q ∧ m ∈ row i q.1 q.2
  noReplacement : ∀ s k e m, k < s → marker row U L s k e = some m →
    marker row U L s (k + 1) e = none ∨ marker row U L s (k + 1) e = some m
  contentBound : ∀ s k m, m ∈ content row U L s k → m ≤ s
  markerBound : ∀ s k e m, marker row U L s k e = some m → m ≤ s
  visited : ∀ s k e m, marker row U L s k e = some m → 2 * e + 1 < s
  unique : ∀ s k e j m, marker row U L s k e = some m → marker row U L s k j = some m → j = e

private theorem exact_action (s e : Nat) {q : Nat × Nat} (hk : 2 * e < s)
    (hq : chosenPair row U L s e = some q) :
    row e q.1 q.2 ⊆ content row U L s (2 * e + 1) := by
  unfold content
  rw [state_next s (2 * e) hk, upperVisit, ← chosen_at s e hk, hq]
  rcases q with ⟨x,t⟩
  exact Finset.subset_union_right

theorem traceLaws (hU : UpperCorrect row before U) (hL : LowerCorrect φ M L) :
    Laws φ row M U L := by
  refine {
    contentInitial := rfl
    markerInitial := fun _ => rfl
    doneInitial := fun _ => Bool.false_ne_true
    contentCarry := fun s => congrArg Prod.fst (state_carry s)
    markerCarry := fun s e => congrArg (fun a : State => a.2.1 e) (state_carry s)
    contentPersists := content_mono
    doneNext := ?_
    action := ?_
    upperProgress := ?_
    lowerProgress := ?_
    enterContent := ?_
    enterMarker := ?_
    active := fun s k e m => (stateValid hU hL s k).active e m
    cancellation := ?_
    noReplacement := ?_
    contentBound := fun s k => (stateValid hU hL s k).contentBound
    markerBound := fun s k => (stateValid hU hL s k).markerBound
    visited := fun s k => (stateValid hU hL s k).visited
    unique := fun s k e j m he hj => (stateValid hU hL s k).unique j e m hj he
  }
  · intro s e
    conv_lhs => unfold done; rw [state_carry]
    rw [flag_state s s e le_rfl]
    constructor
    · exact fun h => h.imp id And.right
    · intro h
      rcases h with hd | h
      · exact .inl hd
      · refine .inr ⟨?_, h⟩
        by_contra hn
        simp [chosenPair, hn] at h
  · intro s e q hq
    have hk : 2 * e < s := by
      by_contra hn
      simp [chosenPair, hn] at hq
    have ha := upperSome hU ((chosen_at s e hk).symm.trans hq)
    refine ⟨hk, ?_, ha.2, (exact_action s e hk hq).trans (content_mono _ _ _ (by omega) le_rfl)⟩
    intro hd
    have ht := (flag_state s (2 * e) e hk.le).mpr (.inl hd)
    simp [ha.1] at ht
  · intro s e q hk hn hc
    have hd : ¬ (state row U L s (2 * e)).2.2 e = true := by
      intro h
      exact hn (((flag_state s (2 * e) e hk.le).mp h).resolve_right (by omega))
    rw [chosen_at s e hk]
    unfold upperAction
    rw [ite_eq_right hd]
    change (U e s (restraints row U L s e)).isSome = true
    have hh := hU e s (restraints row U L s e)
    cases hres : U e s (restraints row U L s e) with
    | none =>
      rw [hres] at hh
      exact (hh q hc).elim
    | some _ => rfl
  · intro s e m hk hn hb hM hD hC hf
    let a := state row U L s (2 * e + 1)
    have fresh : m ∉ markerSet a.2.1 s := by
      rintro hm
      obtain ⟨j, _, hj⟩ := (memMarkerSet _ _ _).mp hm
      exact hf j hj
    have hh := hL e s a.1 (markerSet a.2.1 s)
    change ((state row U L s (2 * e + 1 + 1)).2.1 e).isSome = true
    rw [state_next s _ hk, lowerVisit]
    change ((match a.2.1 e with
      | none => (a.1, Function.update a.2.1 e (L e s a.1 (markerSet a.2.1 s)), a.2.2)
      | some _ => a).2.1 e).isSome = true
    rw [show a.2.1 e = none from hn]
    simp only [Function.update_self]
    cases hres : L e s a.1 (markerSet a.2.1 s) with
    | none =>
      rw [hres] at hh
      exact (hh m ⟨hb, hM, hD, hC, fresh⟩).elim
    | some _ => rfl
  · intro s k m hk hm hn
    let a := state row U L s k
    have hstep := step (row := row) (U := U) (L := L) s k a
    unfold content at hm
    rw [state_next s k hk] at hm
    change m ∈ (visit row U L s k a).1 at hm
    change m ∉ a.1 at hn
    generalize hresult : visit row U L s k a = result at hstep hm
    cases hstep with
    | unchanged => exact (hn hm).elim
    | lower => exact (hn hm).elim
    | upper i q hi hq =>
      exact ⟨i, q, hi, (chosen_at s i (by omega)).trans (by simpa only [← hi] using hq),
        (Finset.mem_union.mp hm).resolve_left hn⟩
  · intro s k e m hk hm hn
    let a := state row U L s k
    have hstep := step (row := row) (U := U) (L := L) s k a
    unfold marker at hm
    rw [state_next s k hk] at hm
    change (visit row U L s k a).2.1 e = some m at hm
    change a.2.1 e ≠ some m at hn
    generalize hresult : visit row U L s k a = result at hstep hm
    cases hstep with
    | unchanged => exact (hn hm).elim
    | upper => exact (hn (remainingSome hm).1).elim
    | lower i n hi _ hsearch =>
      have he : e = i := by
        by_contra h
        exact hn (by simpa only [Function.update_of_ne h] using hm)
      subst e
      have hn' : n = m := by simpa only [Function.update_self, Option.some.injEq] using hm
      exact ⟨hi, hn' ▸ (lowerSome hL hsearch).1⟩
  · intro s k e m hk hm hn
    let a := state row U L s k
    have hstep := step (row := row) (U := U) (L := L) s k a
    unfold marker at hn
    rw [state_next s k hk] at hn
    change a.2.1 e = some m at hm
    change (visit row U L s k a).2.1 e = none at hn
    generalize hresult : visit row U L s k a = result at hstep hn
    cases hstep with
    | unchanged =>
      have hfalse : some m = (none : Option Nat) := hm.symm.trans hn
      cases hfalse
    | lower i _ _ hi _ =>
      have he : e ≠ i := fun he => by subst e; simp [hm] at hi
      have hfalse : some m = (none : Option Nat) :=
        hm.symm.trans (by simpa only [Function.update_of_ne he] using hn)
      cases hfalse
    | upper i q hi hq =>
      have hx := remainingNone hm hn
      exact ⟨i, q, hi, by omega, (chosen_at s i (by omega)).trans
        (by simpa only [← hi] using hq), hx.2⟩
  · intro s k e m hk hm
    let a := state row U L s k
    unfold marker
    rw [state_next s k hk]
    change a.2.1 e = some m at hm
    change (visit row U L s k a).2.1 e = none ∨ (visit row U L s k a).2.1 e = some m
    have hstep := step (row := row) (U := U) (L := L) s k a
    generalize hresult : visit row U L s k a = result at hstep ⊢
    cases hstep with
    | unchanged => exact .inr hm
    | lower i _ _ hi _ =>
      have he : e ≠ i := fun he => by subst e; simp [hm] at hi
      exact .inr (by simpa only [Function.update_of_ne he] using hm)
    | upper i q hi hq =>
      by_cases h : k < 2 * e + 1 ∧ m ∈ row i q.1 q.2
      · exact .inl (by simp only [remaining, hm, ite_eq_left h])
      · exact .inr (by simp only [remaining, hm, ite_eq_right h])


-- The lower mask in the decoded visit includes every active marker, since a
-- marker can be assigned only at a visit to its own lower requirement.
theorem allActive (T : Laws φ row M U L) (s k m : Nat) :
    m ∈ markerSet (state row U L s k).2.1 s ↔
      ∃ e, marker row U L s k e = some m := by
  rw [memMarkerSet]
  exact ⟨fun ⟨e, _, he⟩ => ⟨e, he⟩,
    fun ⟨e, he⟩ => ⟨e, T.visited s k e m he, he⟩⟩

theorem state_clamp (s k : Nat) :
    state row U L s k = state row U L s (min k s) := by
  unfold state
  rw [Nat.min_eq_left (min_le_right k s)]

theorem visited_before (T : Laws φ row M U L) (s k e m : Nat)
    (hm : marker row U L s k e = some m) :
    2 * e + 1 < s - 1 ∨ 2 * e + 1 < min k s := by
  have aux : ∀ k, k ≤ s → marker row U L s k e = some m →
      2 * e + 1 < s - 1 ∨ 2 * e + 1 < k := by
    intro k hk hm
    induction k with
    | zero =>
      cases s with
      | zero => rw [T.markerInitial e] at hm; contradiction
      | succ s =>
        rw [T.markerCarry s e] at hm
        exact .inl (by simpa using T.visited s s e m hm)
    | succ k ih =>
      by_cases hprev : marker row U L s k e = some m
      · exact (ih (by omega) hprev).imp id (fun h => by omega)
      · have hnew := (T.enterMarker s k e m (by omega) hm hprev).1
        exact .inr (by omega)
  have hclamp := congrArg (fun a : State => a.2.1 e)
    (state_clamp (row := row) (U := U) (L := L) s k)
  exact aux (min k s) (min_le_right ..) (hclamp.symm.trans hm)

end Certificate

end PriorityCodedTrace

theorem PriorityCodedVisitTrace : (∀ (φ : Nat → Nat → Part Nat)
    (row : PriorityCodedTrace.Rows)
    (pairBefore : (Nat × Nat) → (Nat × Nat) → Prop)
    (query : Nat → Nat) (M : Set Nat),
  let K : Set Nat := {n | (φ n.unpair.1 n.unpair.2).Dom}
  let oracle : Set (Nat →. Nat) :=
    {(by classical exact fun n => Part.some (if n ∈ K then 1 else 0))}
  Computable (fun p : Nat × Nat × Nat => Finset.equivBitIndices.symm (row p.1 p.2.1 p.2.2)) →
  IsStrictTotalOrder (Nat × Nat) pairBefore →
  ComputablePred (fun p : (Nat × Nat) × (Nat × Nat) => pairBefore p.1 p.2) →
  Computable query →
  (∀ e x t, query (Nat.pair e (Nat.pair x t)) ∉ K ↔
    ∀ r, t ≤ r → row e x r = row e x t) →
  Nat.RecursiveIn oracle (by classical exact fun m => Part.some (if m ∈ M then 1 else 0)) →
  ∃ (U : PriorityCodedTrace.UpperSearch) (L : PriorityCodedTrace.LowerSearch),
    Nat.RecursiveIn oracle (fun n => Part.some (PriorityCodedTrace.upperCode U n)) ∧
    Nat.RecursiveIn oracle (fun n => Part.some (PriorityCodedTrace.lowerCode L n)) ∧
    PriorityCodedTrace.UpperCorrect row pairBefore U ∧
    PriorityCodedTrace.LowerCorrect φ M L ∧
    Nat.RecursiveIn oracle (fun n => Part.some (PriorityCodedTrace.traceCode row U L n)) ∧
    Nat.RecursiveIn oracle (fun s => Part.some
      (Finset.equivBitIndices.symm (PriorityCodedTrace.content row U L s s))) ∧
    Nat.RecursiveIn oracle (fun n => Part.some
      (Finset.equivBitIndices.symm (PriorityCodedTrace.restraints row U L n.unpair.1 n.unpair.2))) ∧
    PriorityCodedTrace.Laws φ row M U L) :=
(by
  intro φ row pairBefore query M K oracle hrow horder hbefore hquery hstable hM
  -- The supplier takes the same paired-domain oracle and finite masks.
  -- Both recursions and their decoded visits use these very search witnesses.
  obtain ⟨U, L, hu, hl, hU, hL⟩ :=
    PriorityBoundedOracleSearches φ row pairBefore query M hrow horder hbefore hquery hstable hM
  change Nat.RecursiveIn oracle (fun n => Part.some (PriorityCodedTrace.upperCode U n)) at hu
  change Nat.RecursiveIn oracle (fun n => Part.some (PriorityCodedTrace.lowerCode L n)) at hl
  change PriorityCodedTrace.UpperCorrect row pairBefore U at hU
  change PriorityCodedTrace.LowerCorrect φ M L at hL
  obtain ⟨htrace, hcontent, hrestraints⟩ :=
    PriorityCodedTrace.traceComputations row U L oracle hrow hu hl
  exact ⟨U, L, hu, hl, hU, hL, htrace, hcontent, hrestraints, PriorityCodedTrace.traceLaws hU hL⟩)

#print axioms PriorityCodedVisitTrace
