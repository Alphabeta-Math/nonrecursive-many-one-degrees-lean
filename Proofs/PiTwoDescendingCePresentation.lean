import Mathlib

import Proofs.ArithmeticalHierarchyLevels
import Proofs.ComputablyEnumerableSet

set_option maxHeartbeats 2000000

theorem PiTwoDescendingCePresentation : (∀ P : _root_.Set _root_.Nat,
  {xs : _root_.Fin 1 → _root_.Nat | xs 0 ∈ P} ∈
      (_root_.ArithmeticalHierarchyLevels 2 1 (_root_.Nat.le_succ 1)).2.1 →
  ∃ Q : _root_.Nat → _root_.Nat → _root_.Nat → Prop,
    _root_.ComputablePred (fun t : _root_.Nat × _root_.Nat × _root_.Nat =>
      Q t.1 t.2.1 t.2.2) ∧
    (∀ y : _root_.Nat, y ∈ P ↔ ∀ j : _root_.Nat, ∃ s : _root_.Nat, Q y j s) ∧
    (let H (k : _root_.Nat) : _root_.Set _root_.Nat :=
      {y | ∀ j : _root_.Nat, j < k → ∃ s : _root_.Nat, Q y j s}
     let encode (n : _root_.Nat) := _root_.List.replicate n false
     let decode (w : _root_.List _root_.Bool) :=
       if w = encode (_root_.List.length w) then _root_.Option.some (_root_.List.length w)
       else _root_.Option.none
     _root_.ComputablyEnumerableSet encode decode
       (_root_.List.replicate_left_injective false)
       (fun n => by simp [decode, encode])
       (fun w hw => _root_.ite_eq_right (fun h => hw ⟨_root_.List.length w, h.symm⟩))
       {z : _root_.Nat | (_root_.Nat.unpair z).2 ∈ H (_root_.Nat.unpair z).1} ∧
     H 0 = _root_.Set.univ ∧ _root_.Antitone H ∧ P = _root_.Set.iInter H)) :=
(by
  classical
  intro P hP
  -- Cintioli, arXiv:2609.00419v1, §2, p. 3, proof of Lemma 1.
  -- The source starts with a computable matrix. The reviewed hierarchy
  -- definition supplies the primitive-recursive matrix of the complement,
  -- so expand its tuple quantifiers and negate the matrix.
  -- https://arxiv.org/pdf/2609.00419v1#page=3
  change ∃ R : (Fin 1 → Nat) → (Fin 2 → Nat) → Prop,
    PrimrecRel R ∧ ∀ xs : Fin 1 → Nat,
      (¬ xs 0 ∈ P) ↔ ∃ j : Nat, ∀ s : Nat, R xs (Fin.cons j (Fin.cons s Fin.elim0)) at hP
  obtain ⟨R, hR, hRP⟩ := hP
  let tuple (j s : Nat) : Fin 2 → Nat := Fin.cons j (Fin.cons s Fin.elim0)
  let Q (y j s : Nat) := ¬ R (fun _ => y) (tuple j s)
  -- The free tuple is constant in its coordinate. The bound tuple has
  -- coordinates j and s, tested by equality of the index with 0.
  have hUnary : Primrec fun t : Nat × Nat × Nat => (fun _ : Fin 1 => t.1) := by
    apply Primrec.fin_curry.mpr
    exact Primrec.fst.comp Primrec.fst
  have hBinary : Primrec fun t : Nat × Nat × Nat => tuple t.2.1 t.2.2 := by
    apply Primrec.fin_curry.mpr
    have hFirst : Primrec fun t : (Nat × Nat × Nat) × Fin 2 => t.1.2.1 :=
      Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have hSecond : Primrec fun t : (Nat × Nat × Nat) × Fin 2 => t.1.2.2 :=
      Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
    have hCoord : Primrec fun t : (Nat × Nat × Nat) × Fin 2 =>
        if t.2 = 0 then t.1.2.1 else t.1.2.2 :=
      Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) hFirst hSecond
    exact hCoord.of_eq fun ⟨t, i⟩ => by fin_cases i <;> simp [tuple]
  have hQ : ComputablePred (fun t : Nat × Nat × Nat => Q t.1 t.2.1 t.2.2) :=
    (hR.comp hUnary hBinary).computablePred.not
  have hPiff (y : Nat) : y ∈ P ↔ ∀ j : Nat, ∃ s : Nat, Q y j s := by
    simpa only [Q, tuple, not_not, not_exists, not_forall] using
      not_congr (hRP (fun _ => y))
  refine ⟨Q, hQ, hPiff, ?_⟩
  dsimp only
  let H (k : Nat) : Set Nat := {y | ∀ j < k, ∃ s, Q y j s}
  let G : Set Nat := {z | z.unpair.2 ∈ H z.unpair.1}
  let B (z b : Nat) : Prop := ∀ j < z.unpair.1, ∃ s < b, Q z.unpair.2 j s
  -- The source leaves uniformity implicit. A common strict bound suffices
  -- for finitely many witnesses. At k = 0 the bound can be 0.
  have bounded (y k : Nat) (h : y ∈ H k) :
      ∃ b : Nat, ∀ j < k, ∃ s < b, Q y j s := by
    induction k with
    | zero => exact ⟨0, fun j hj => (Nat.not_lt_zero j hj).elim⟩
    | succ k ih =>
      obtain ⟨b, hb⟩ := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
      obtain ⟨s, hs⟩ := h k (Nat.lt_succ_self k)
      refine ⟨max b (s + 1), fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · obtain ⟨t, ht, hQt⟩ := hb j hj
        exact ⟨t, lt_of_lt_of_le ht (le_max_left _ _), hQt⟩
      · exact ⟨s, lt_of_lt_of_le (Nat.lt_succ_self s) (le_max_right _ _), hs⟩
  -- Tau Ceti's bounded-search lemma uses a jointly computable input test.
  -- Adapt its Boolean recursion over 0 through n-1 using the pinned mathlib
  -- primitives, so the proof needs no Tau Ceti import.
  -- The bounded and unbounded search adaptations below are from
  -- TauCeti/Computability/RE.lean, rev. 91942aa9ff8cea04d0d9905b80f75c07ce2379c4.
  -- Copyright (c) 2026 The Tau Ceti contributors. Apache-2.0.
  have existsLt {α : Type} [Primcodable α] {p : α → Nat → Prop}
      (hp : ComputablePred fun x : α × Nat => p x.1 x.2) :
      ComputablePred fun x : α × Nat => ∃ n < x.2, p x.1 n := by
    have hscan : Computable fun x : α × Nat =>
        Nat.rec (motive := fun _ => Bool) false (fun n b => b || decide (p x.1 n)) x.2 :=
      Computable.nat_rec Computable.snd (Computable.const false)
        (Primrec.or.to_comp.comp (Computable.snd.comp Computable.snd)
          (hp.decide.comp (Computable.pair (Computable.fst.comp Computable.fst)
            (Computable.fst.comp Computable.snd)))).to₂
    refine Computable.computablePred (hscan.of_eq fun ⟨a, n⟩ => ?_)
    induction n with
    | zero => simp
    | succ n ih =>
      have hsplit : (∃ m < n + 1, p a m) ↔ (∃ m < n, p a m) ∨ p a n := by
        simp only [Nat.lt_succ_iff_lt_or_eq, or_and_right, exists_or, exists_eq_left]
      change (Nat.rec false (fun m b => b || decide (p a m)) n ||
        decide (p a n)) = decide (∃ m < n + 1, p a m)
      rw [ih]
      simp only [hsplit, Bool.decide_or]
  have hReorder : Computable (fun t : (Nat × Nat) × Nat => (t.1.1, t.1.2, t.2)) :=
    (Computable.fst.comp Computable.fst).pair
      ((Computable.snd.comp Computable.fst).pair Computable.snd)
  have hInner : ComputablePred fun t : (Nat × Nat) × Nat =>
      ∃ s < t.2, Q t.1.1 t.1.2 s :=
    existsLt (p := fun (yj : Nat × Nat) s => Q yj.1 yj.2 s)
      (hQ.decide.comp hReorder).computablePred
  have hUnpair : Computable Nat.unpair := Primrec.unpair.to_comp
  have hInnerInput : Computable (fun t : (Nat × Nat) × Nat =>
      ((t.1.1.unpair.2, t.2), t.1.2)) :=
    ((Computable.snd.comp (hUnpair.comp (Computable.fst.comp Computable.fst))).pair
      Computable.snd).pair (Computable.snd.comp Computable.fst)
  have hFailure : ComputablePred fun t : (Nat × Nat) × Nat =>
      ¬ ∃ s < t.1.2, Q t.1.1.unpair.2 t.2 s :=
    ((hInner.decide.comp hInnerInput).computablePred :
      ComputablePred fun t : (Nat × Nat) × Nat => ∃ s < t.1.2, Q t.1.1.unpair.2 t.2 s).not
  have hOuter := existsLt (p := fun (zb : Nat × Nat) j =>
    ¬ ∃ s < zb.2, Q zb.1.unpair.2 j s) hFailure
  have hOuterInput : Computable (fun t : Nat × Nat => (t, t.1.unpair.1)) :=
    Computable.id.pair (Computable.fst.comp (hUnpair.comp Computable.fst))
  have hB : ComputablePred (fun t : Nat × Nat => B t.1 t.2) := by
    have h := (hOuter.not.decide.comp hOuterInput).computablePred
    exact h.of_eq fun t => by simp [B]
  -- Adapt Tau Ceti's existential semidecision proof. The stage test is
  -- total, so all earlier searches satisfy the rfind domain condition.
  have hSearch : Partrec fun z => Nat.rfind fun b => Part.some (decide (B z b)) :=
    Partrec.rfind hB.decide.partrec
  have hRE : REPred (fun z => z ∈ G) := hSearch.dom_re.of_eq fun z => by
    have hDom : (Nat.rfind fun b => Part.some (decide (B z b))).Dom ↔ ∃ b, B z b := by
      simpa using Nat.rfind_dom (p := fun b => Part.some (decide (B z b)))
    rw [hDom]
    constructor
    · rintro ⟨b, hb⟩ j hj
      obtain ⟨s, _, hs⟩ := hb j hj
      exact ⟨s, hs⟩
    · exact bounded z.unpair.2 z.unpair.1
  -- Alphabeta Math, thm-recognizable-iff-enumerable, Steps 1.2, 2.1, 3.1.
  -- Use the compiled Nat bridge for the recognizability-to-range direction.
  -- Its fallback enumerator covers the nonempty case and uses Nat.unpair
  -- for candidate/fuel and the reviewed false-bit encoding for Nat outputs.
  -- https://alphabetamath.cc/item/thm-recognizable-iff-enumerable
  -- The article-specific Research Portal and defect-report routes return
  -- HTTP 404. The article's claim is proved as stated on p. 3.
  refine ⟨(ComputablyEnumerableSet.nat_rePred_iff false G).mp hRE, ?_, ?_, ?_⟩
  · ext y
    simp
  · intro k l hkl y hy j hj
    exact hy j (lt_of_lt_of_le hj hkl)
  · -- The row k = j + 1 supplies the witness at each specified index j.
    ext y
    rw [Set.mem_iInter, hPiff]
    exact ⟨fun h k j _ => h j, fun h j => h (j + 1) j (Nat.lt_succ_self j)⟩)
