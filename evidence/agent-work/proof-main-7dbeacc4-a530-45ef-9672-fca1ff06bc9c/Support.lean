/- The reviewed definition is the range characterization from
   https://alphabetamath.cc/item/def-computably-enumerable-set (Definition).
   This support connects its constant-bit encodings of Nat with mathlib's REPred.
   List.length recovers the Nat from either encoding, so the equivalence takes
   no computational hypothesis on a supplied decoder. The article-specific
   Research Portal and defect-report routes returned HTTP 404. The numbered
   proof below refers to the verified shared-library recognizability theorem
   at https://alphabetamath.cc/item/thm-recognizable-iff-enumerable. -/
namespace ComputablyEnumerableSet

/-- Both constant-bit unary encodings of Nat are computable. -/
theorem computable_replicate (bit : Bool) :
    Computable (fun n : ℕ => List.replicate n bit) := by
  have hstep : Computable₂ (fun (_ : ℕ) (p : ℕ × List Bool) => bit :: p.2) :=
    (Computable.list_cons.comp (Computable.const bit)
      (Computable.snd.comp Computable.snd)).to₂
  refine (Computable.nat_rec Computable.id (Computable.const ([] : List Bool))
    hstep).of_eq ?_
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    exact congrArg (List.cons bit) ih

/-- Search the indices of a total computable enumeration to recognize its range. -/
theorem nat_rePred_range {e : ℕ → ℕ} (he : Computable e) :
    REPred (fun x => x ∈ Set.range e) := by
  -- In thm-recognizable-iff-enumerable, step 1.1, each equality test terminates.
  -- Here rfind searches the indices directly using equality on Nat.
  have htest : Computable (fun p : ℕ × ℕ => decide (e p.2 = p.1)) :=
    Primrec.eq.decide.to_comp.comp (he.comp Computable.snd) Computable.fst
  have hsearch : Partrec (fun x => Nat.rfind (fun n => Part.some (decide (e n = x)))) :=
    Partrec.rfind htest.partrec
  refine hsearch.dom_re.of_eq fun x => ?_
  exact (Nat.rfind_dom (p := fun n => Part.some (decide (e n = x)))).trans
    (by simp [Set.mem_range])

/-- Code representation of a semidecider for membership in a set of Nat. -/
theorem nat_rePred_iff_exists_code (A : Set ℕ) :
    REPred (fun x => x ∈ A) ↔
      ∃ c : Nat.Partrec.Code, ∀ x, (c.eval x).Dom ↔ x ∈ A := by
  constructor
  · intro h
    -- The REPred witness returns Unit. Map its output to 0 for the Nat code.
    have hzero : Partrec (fun x : ℕ =>
        (Part.assert (x ∈ A) (fun _ => Part.some (0 : ℕ)))) := by
      unfold REPred at h
      refine (h.map ((Computable.const (0 : ℕ) : Computable (fun _ : ℕ × Unit => 0)).to₂)).of_eq ?_
      intro x
      ext n
      simp [eq_comm]
    obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hzero)
    exact ⟨c, fun x => by
      rw [hc]
      simp [Part.dom_iff_mem]⟩
  · rintro ⟨c, hc⟩
    have h : Nat.Partrec c.eval := Nat.Partrec.Code.exists_code.mpr ⟨c, rfl⟩
    exact (Partrec.nat_iff.mpr h).dom_re.of_eq hc

/-- A nonempty c.e. set of Nat is the range of a total computable function. -/
theorem nat_exists_computable_range {A : Set ℕ}
    (hA : REPred (fun x => x ∈ A)) (hne : A.Nonempty) :
    ∃ e : ℕ → ℕ, Computable e ∧ Set.range e = A := by
  -- thm-recognizable-iff-enumerable, step 1.2 supplies a fallback member;
  -- we choose one from nonemptiness and use it as a computable constant.
  obtain ⟨a, ha⟩ := hne
  obtain ⟨c, hc⟩ := (nat_rePred_iff_exists_code A).mp hA
  -- Step 2.1 uses shortlex words. For Nat, unpair the input into a candidate
  -- and fuel. This specializes the bounded-code construction in Tau Ceti
  -- REPred.exists_computable_range at revision 91942aa9ff8cea04d0d9905b80f75c07ce2379c4
  -- to Nat using only the pinned mathlib modules.
  let bounded (n : ℕ) := Nat.Partrec.Code.evaln n.unpair.2 c n.unpair.1
  let e (n : ℕ) : ℕ := if (bounded n).isSome then n.unpair.1 else a
  have hinput : Computable (fun n => (Nat.unpair n).1) :=
    Computable.fst.comp Computable.unpair
  have hfuel : Computable (fun n => (Nat.unpair n).2) :=
    Computable.snd.comp Computable.unpair
  have hbounded : Computable bounded :=
    Nat.Partrec.Code.primrec_evaln.to_comp.comp
      ((hfuel.pair (Computable.const c)).pair hinput)
  have he : Computable e := by
    simpa only [e, Bool.cond_eq_ite] using
      (Primrec.option_isSome.to_comp.comp hbounded).cond hinput (Computable.const a)
  have hcovered (x : ℕ) : x ∈ A ↔ ∃ t, (Nat.Partrec.Code.evaln t c x).isSome := by
    rw [← hc x, Part.dom_iff_mem]
    constructor
    · rintro ⟨out, hout⟩
      obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp hout
      exact ⟨t, Option.isSome_iff_exists.mpr ⟨out, ht⟩⟩
    · rintro ⟨t, ht⟩
      obtain ⟨out, hout⟩ := Option.isSome_iff_exists.mp ht
      exact ⟨out, Nat.Partrec.Code.evaln_complete.mpr ⟨t, hout⟩⟩
  refine ⟨e, he, Set.ext fun x => ?_⟩
  constructor
  · rintro ⟨n, rfl⟩
    by_cases h : (bounded n).isSome
    · rw [show e n = n.unpair.1 from ite_eq_left h]
      exact (hcovered _).mpr ⟨n.unpair.2, h⟩
    · rw [show e n = a from ite_eq_right h]
      exact ha
  · intro hx
    obtain ⟨t, ht⟩ := (hcovered x).mp hx
    exact ⟨Nat.pair x t, by simp [e, bounded, ht]⟩

/-- Nat bridge for the raw reviewed definition, which follows this support. -/
theorem nat_rePred_iff (bit : Bool) (A : Set ℕ) :
    REPred (fun x => x ∈ A) ↔
      A = ∅ ∨ ∃ e : ℕ → ℕ,
        Computable (fun n : ℕ => List.replicate (e n) bit) ∧ Set.range e = A := by
  -- Step 3.1 combines the directions. Both directions treat the empty set
  -- separately, since a total map out of Nat always has some output.
  constructor
  · intro h
    by_cases he : A = ∅
    · exact Or.inl he
    · obtain ⟨e, hc, hr⟩ := nat_exists_computable_range h (Set.nonempty_iff_ne_empty.mpr he)
      exact Or.inr ⟨e, (computable_replicate bit).comp hc, hr⟩
  · rintro (rfl | ⟨e, he, rfl⟩)
    · exact (Partrec.none (α := ℕ) (σ := ℕ)).dom_re.of_eq fun x => by simp
    · apply nat_rePred_range
      exact (Computable.list_length.comp he).of_eq fun n => List.length_replicate

end ComputablyEnumerableSet
