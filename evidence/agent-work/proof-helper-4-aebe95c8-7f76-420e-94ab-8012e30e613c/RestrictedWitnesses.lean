import PriorityRequirementsDraft

namespace PriorityRequirements

/-- A c.e. colour supplies an ascending partial map defined on exactly that colour. -/
theorem ceAscendingMap {A : Set ℕ} (hA : REPred (fun x => x ∈ A)) (hinf : A.Infinite) :
    ∃ ψ : ℕ → Part ℕ, Partrec ψ ∧
      (∀ x, (ψ x).Dom ↔ x ∈ A) ∧
      (∀ x y, y ∈ ψ x → x < y ∧ (y ∈ A ↔ x ∈ A)) := by
  -- Alphabeta Math, thm-recognizable-iff-enumerable, Steps 1.2, 2.1, 3.1.
  -- The Nat range bridge supplies an enumerator, which we search over pairs.
  obtain ⟨a, ha, hrange⟩ := ComputablyEnumerableSet.nat_exists_computable_range hA hinf.nonempty
  let test (x n : ℕ) : Option ℕ :=
    if a n.unpair.1 = x ∧ x < a n.unpair.2 then some (a n.unpair.2) else none
  have first : Computable (fun p : ℕ × ℕ => a p.2.unpair.1) :=
    ha.comp (Computable.fst.comp (Computable.unpair.comp Computable.snd))
  have last : Computable (fun p : ℕ × ℕ => a p.2.unpair.2) :=
    ha.comp (Computable.snd.comp (Computable.unpair.comp Computable.snd))
  have eqTest := Primrec.eq.decide.to_comp.comp first Computable.fst
  have ltTest := Primrec.nat_lt.decide.to_comp.comp Computable.fst last
  have both : Computable (fun p : ℕ × ℕ => decide (a p.2.unpair.1 = p.1 ∧ p.1 < a p.2.unpair.2)) :=
    (Primrec.and.to_comp.comp eqTest ltTest).of_eq (by intro p; simp [Bool.decide_and])
  have htest : Computable₂ test := by
    change Computable (fun p : ℕ × ℕ => test p.1 p.2)
    simpa only [test, Bool.cond_decide] using
      both.cond (Computable.option_some.comp last) (Computable.const (none : Option ℕ))
  have valid {x n y} (hy : y ∈ test x n) : x < y ∧ y ∈ A ∧ x ∈ A := by
    unfold test at hy
    split at hy
    next h =>
      have he : a n.unpair.2 = y := by simpa using hy
      subst y
      exact ⟨h.2, hrange ▸ (show a n.unpair.2 ∈ Set.range a from ⟨_, rfl⟩),
        hrange ▸ (show x ∈ Set.range a from ⟨n.unpair.1, h.1⟩)⟩
    next => simp at hy
  refine ⟨fun x => Nat.rfindOpt (test x), Partrec.rfindOpt htest, fun x => ?_, ?_⟩
  · rw [Nat.rfindOpt_dom]
    constructor
    · rintro ⟨n, y, hy⟩
      exact (valid hy).2.2
    · intro hx
      obtain ⟨y, hy, hxy⟩ := hinf.exists_gt x
      rw [← hrange] at hx hy
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, rfl⟩ := hy
      exact ⟨Nat.pair i j, a j, by simp [test, hxy]⟩
  · intro x y h
    obtain ⟨n, hn⟩ := Nat.rfindOpt_spec h
    obtain ⟨hxy, hy, hx⟩ := valid hn
    exact ⟨hxy, iff_of_true hy hx⟩

theorem ceComplementHasUnboundedOmissions
    (A : Set ℕ) (f : ℕ → Part ℕ)
    (hA : REPred (fun x => x ∈ A))
    (hnonrec : ¬ ComputablePred (fun x => x ∈ A))
    (hnoncyl : ¬ (OneOneReducible (fun x => x ∈ A)
        (fun z => ∃ x n : ℕ, x ∈ A ∧ z = Nat.pair x n) ∧
      OneOneReducible (fun z => ∃ x n : ℕ, x ∈ A ∧ z = Nat.pair x n)
        (fun x => x ∈ A)))
    (hf : Partrec f)
    (hasc : ∀ x y, y ∈ f x → x < y ∧ (y ∈ A ↔ x ∈ A)) :
    ∀ b : ℕ, ∃ m, b < m ∧ m ∈ Aᶜ ∧ ¬ (f m).Dom := by
  classical
  have hAinf : A.Infinite := by
    intro hfin
    let xs := hfin.toFinset.toList
    have listMem : PrimrecRel (fun (ys : List ℕ) (x : ℕ) => x ∈ ys) :=
      (PrimrecRel.exists_mem_list (R := @Eq ℕ) Primrec.eq).of_eq (by intro ys x; simp)
    have comp : ComputablePred (fun x : ℕ => x ∈ xs) :=
      (listMem.decide.to_comp.comp (Computable.const xs) Computable.id).computablePred
    exact hnonrec (comp.of_eq (fun x => Finset.mem_toList.trans hfin.mem_toFinset))
  obtain ⟨ψ, hψ, hdomψ, hascψ⟩ := ceAscendingMap hA hAinf
  obtain ⟨g, hg, hdomg, hout⟩ := CofiniteDomainLemma.partrec_union hf hψ
  have hascg (x y : ℕ) (hy : y ∈ g x) := (hout x y hy).elim (hasc x y) (hascψ x y)
  have hinf := CofiniteDomainLemma A g hnonrec hnoncyl hg hascg
  intro b
  obtain ⟨m, hm, hmb⟩ := hinf.exists_gt b
  change ¬ (g m).Dom at hm
  exact ⟨m, hmb, fun h => hm ((hdomg m).2 (.inr ((hdomψ m).2 h))),
    fun h => hm ((hdomg m).2 (.inl h))⟩

/-- Witness formulas for a trace whose lower markers lie in the non-c.e. colour. -/
theorem ceRestrictedRequirements
    {φ : ℕ → ℕ → Part ℕ} {row : ℕ → ℕ → ℕ → Finset ℕ}
    (A : Set ℕ) (T : VerificationTrace φ row (Aᶜ)) (V : ℕ → ℕ → Set ℕ)
    (hφ : Partrec₂ φ)
    (hV : REPred (fun p : ℕ × ℕ × ℕ => p.2.2 ∈ V p.1 p.2.1))
    (hmono : ∀ e x, Monotone (row e x))
    (hunion : ∀ e x y, y ∈ V e x ↔ ∃ s, y ∈ row e x s)
    (hA : REPred (fun x => x ∈ A))
    (hnonrec : ¬ ComputablePred (fun x => x ∈ A))
    (hnoncyl : ¬ (OneOneReducible (fun x => x ∈ A)
        (fun z => ∃ x n : ℕ, x ∈ A ∧ z = Nat.pair x n) ∧
      OneOneReducible (fun z => ∃ x n : ℕ, x ∈ A ∧ z = Nat.pair x n)
        (fun x => x ∈ A))) :
    (∀ e, (∀ x y, y ∈ V e x → (y ∈ A ↔ x ∈ A)) →
      ∃ x, (V e x).Finite ∧ V e x ⊆ T.output) ∧
    (∀ e, (∀ x y, y ∈ φ e x → x < y ∧ (y ∈ A ↔ x ∈ A)) →
      ∃ m, m ∈ Aᶜ ∧ m ∉ T.output ∧ ¬ (φ e m).Dom) := by
  constructor
  · intro e hhom
    have hnotRE : ¬ REPred (fun x => x ∈ Aᶜ) :=
      fun h => hnonrec (ComputablePred.computable_iff_re_compl_re'.mpr ⟨hA, h⟩)
    refine T.upper_met V hmono hunion e (fun Z hZ hZM => ?_)
    exact FiniteMarkerAvoidance.of_nonCE_marker_colors A (V e) hnoncyl
      ((ComputablyEnumerableSet.nat_rePred_iff true _).mp (rowGraphRE hV e))
      hhom Z hZ (fun z hz =>
        ⟨fun h => ((hZM hz) h).elim, fun _ hce =>
          hnotRE ((ComputablyEnumerableSet.nat_rePred_iff true _).mpr hce)⟩)
  · intro e hasc
    exact T.lower_met e (ceComplementHasUnboundedOmissions A (φ e) hA hnonrec hnoncyl
      (hφ.comp (Computable.const e) Computable.id) hasc)

/-- The c.e. colour is the domain of a single section, so its complement is
decidable by one query to the paired halting oracle. -/
theorem ceComplementOracle
    (φ : ℕ → ℕ → Part ℕ) (A : Set ℕ)
    (hsurj : ∀ f : ℕ → Part ℕ, Partrec f → ∃ e, φ e = f)
    (hA : REPred (fun x => x ∈ A)) :
    Nat.RecursiveIn
      {(by classical exact fun n => Part.some (if n ∈ haltingOracle φ then 1 else 0))}
      (by classical exact fun m => Part.some (if m ∈ Aᶜ then 1 else 0)) := by
  classical
  obtain ⟨c, hdom⟩ := (ComputablyEnumerableSet.nat_rePred_iff_exists_code A).mp hA
  have hc : Partrec c.eval :=
    Partrec.nat_iff.mpr (Nat.Partrec.Code.exists_code.mpr ⟨c, rfl⟩)
  obtain ⟨i, hi⟩ := hsurj c.eval hc
  let answer (n : ℕ) := if n ∈ haltingOracle φ then 1 else 0
  let O : Set (ℕ →. ℕ) := {fun n => Part.some (answer n)}
  have hanswer : Nat.RecursiveIn O (fun n => Part.some (answer n)) :=
    Nat.RecursiveIn.oracle _ (Set.mem_singleton _)
  have hpair : Nat.RecursiveIn O (fun n => Part.some (Nat.pair i n)) :=
    RecursiveIn.iff_nat.mp
      (Primrec₂.natPair.to_comp.comp (Computable.const i) Computable.id).computableIn
  have hflip : Nat.RecursiveIn O (fun n => Part.some (1 - n)) :=
    RecursiveIn.iff_nat.mp
      (Primrec.nat_sub.to_comp.comp (Computable.const 1) Computable.id).computableIn
  refine (hflip.comp (hanswer.comp hpair)).of_eq ?_
  intro n
  have hn : Nat.pair i n ∈ haltingOracle φ ↔ n ∈ A :=
    (pair_mem_haltingOracle φ i n).trans (by rw [hi]; exact hdom n)
  by_cases hnA : n ∈ A <;> simp [answer, hn, hnA]

end PriorityRequirements

#print axioms PriorityRequirements
#print axioms PriorityRequirements.ceComplementHasUnboundedOmissions
#print axioms PriorityRequirements.ceRestrictedRequirements
#print axioms PriorityRequirements.ceComplementOracle
