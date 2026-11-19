import Proofs.PriorityRequirements
import Proofs.HaltingSigmaOneCompleteness

namespace MaslovaRestricted

open HaltingSigmaOneCompleteness

abbrev Cylinder (A : Set ℕ) : Set ℕ :=
  {z | ∃ x n : ℕ, x ∈ A ∧ z = Nat.pair x n}

abbrev NonCylinder (A : Set ℕ) : Prop :=
  ¬ (OneOneReducible (fun x => x ∈ A) (fun x => x ∈ Cylinder A) ∧
    OneOneReducible (fun x => x ∈ Cylinder A) (fun x => x ∈ A))

abbrev Ascending (A : Set ℕ) (f : ℕ → Part ℕ) : Prop :=
  ∀ x y, y ∈ f x → x < y ∧ (y ∈ A ↔ x ∈ A)

theorem canonicalTripleRE :
    REPred (fun p : ℕ × ℕ × ℕ => p.2.2 ∈ row p.1 p.2.1) := by
  have hpair : Computable (fun p : ℕ × ℕ × ℕ => Nat.pair p.2.1 p.2.2) :=
    Primrec₂.natPair.to_comp.comp (Computable.fst.comp Computable.snd)
      (Computable.snd.comp Computable.snd)
  exact (canonicalNumbering_acceptable.2.2.1.comp Computable.fst hpair).dom_re

theorem packedExhaustion (W : ℕ → Set ℕ)
    (hW :
      let encode (n : ℕ) := List.replicate n true
      let decode (w : List Bool) := if encode w.length = w then some w.length else none
      ComputablyEnumerableSet encode decode
        (Function.LeftInverse.injective
          (show Function.LeftInverse List.length encode from fun _ => List.length_replicate))
        (fun n => by simp [decode, encode])
        (fun w hw => ite_eq_right (fun h => hw ⟨w.length, h⟩))
        {z : ℕ | ∃ x y : ℕ, y ∈ W x ∧ z = Nat.pair x y}) :
    ∃ e, ∀ x, W x = {y | ∃ s, y ∈ rowAt e x s} := by
  let G : Set ℕ := {z | ∃ x y : ℕ, y ∈ W x ∧ z = Nat.pair x y}
  obtain ⟨e, he⟩ := exists_index_stages ((ComputablyEnumerableSet.nat_rePred_iff true G).mpr hW)
  refine ⟨e, fun x => Set.ext fun y => Iff.trans ?_ (he x y)⟩
  change y ∈ W x ↔ ∃ a b : ℕ, b ∈ W a ∧ Nat.pair x y = Nat.pair a b
  constructor
  · exact fun h => ⟨x, y, h, rfl⟩
  · rintro ⟨a, b, hb, hab⟩
    obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp hab
    exact hb

theorem avoidComplement (A : Set ℕ) (hA : REPred (fun x => x ∈ A))
    (hnonrec : ¬ ComputablePred (fun x => x ∈ A)) (hnoncyl : NonCylinder A)
    (e : ℕ) (hhom : ∀ x y, y ∈ row e x → (y ∈ A ↔ x ∈ A)) :
    ∀ Z : Set ℕ, Z.Finite → Z ⊆ Aᶜ →
      ∃ x, (row e x).Finite ∧ row e x ∩ Z = ∅ := by
  have hnco : ¬ REPred (fun x => x ∈ Aᶜ) := by
    intro h
    exact hnonrec (ComputablePred.computable_iff_re_compl_re'.mpr ⟨hA, h⟩)
  intro Z hZ hsub
  exact FiniteMarkerAvoidance.of_nonCE_marker_colors A (row e) hnoncyl
    ((ComputablyEnumerableSet.nat_rePred_iff true _).mp
      (PriorityRequirements.rowGraphRE canonicalTripleRE e)) hhom Z hZ
    (fun z hz => ⟨fun ha => (hsub hz ha).elim,
      fun _ hce => hnco ((ComputablyEnumerableSet.nat_rePred_iff true _).mpr hce)⟩)

theorem ceAdvance {A : Set ℕ} (hA : REPred (fun x => x ∈ A)) (hinf : A.Infinite) :
    ∃ ψ : ℕ → Part ℕ, Partrec ψ ∧ (∀ x, (ψ x).Dom ↔ x ∈ A) ∧ Ascending A ψ := by
  classical
  obtain ⟨enumA, henum, hrange⟩ :=
    ComputablyEnumerableSet.nat_exists_computable_range hA hinf.nonempty
  let step (x n : ℕ) : Option ℕ := if x < enumA n then some (enumA n) else none
  have hstep : Computable₂ step := by
    change Computable (fun p : ℕ × ℕ => step p.1 p.2)
    have hout := henum.comp (Computable.snd : Computable (Prod.snd : ℕ × ℕ → ℕ))
    simpa only [step, Bool.cond_eq_ite, decide_eq_true_eq] using
      (Primrec.nat_lt.decide.to_comp.comp Computable.fst hout).cond
        (Primrec.option_some.to_comp.comp hout) (Computable.const (none : Option ℕ))
  let advance (x : ℕ) := Nat.rfindOpt (step x)
  have hadvance : Partrec advance := Partrec.rfindOpt hstep
  have hsuccess (x : ℕ) : (advance x).Dom := by
    obtain ⟨y, hy, hxy⟩ := hinf.exists_gt x
    obtain ⟨n, rfl⟩ : y ∈ Set.range enumA := hrange.symm ▸ hy
    exact Nat.rfindOpt_dom.mpr ⟨n, enumA n, by simp [step, hxy]⟩
  let gate (x : ℕ) := Part.assert (x ∈ A) (fun _ => Part.some ())
  let ψ (x : ℕ) := (gate x).bind (fun _ => advance x)
  have hgate : Partrec gate := hA
  have hψ : Partrec ψ := hgate.bind (hadvance.comp (Computable.fst : Computable (Prod.fst : ℕ × Unit → ℕ)))
  have hdom (x : ℕ) : (ψ x).Dom ↔ x ∈ A := by
    by_cases hx : x ∈ A <;> simp [ψ, gate, Part.assert_pos, Part.assert_neg, hx, hsuccess]
  refine ⟨ψ, hψ, hdom, ?_⟩
  intro x y hy
  obtain ⟨_, _, hout⟩ := Part.mem_bind_iff.mp hy
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec hout
  have hx := (hdom x).mp (Part.dom_iff_mem.mpr ⟨y, hy⟩)
  by_cases hxy : x < enumA n
  · have heq : enumA n = y := by simpa [step, hxy] using hn
    have hyA : enumA n ∈ A := hrange ▸ Set.mem_range_self n
    exact ⟨heq ▸ hxy, iff_of_true (heq ▸ hyA) hx⟩
  · simp [step, hxy] at hn

theorem omittedAbove (A : Set ℕ) (hA : REPred (fun x => x ∈ A))
    (hnonrec : ¬ ComputablePred (fun x => x ∈ A)) (hnoncyl : NonCylinder A)
    (f : ℕ → Part ℕ) (hf : Partrec f) (hasc : Ascending A f) :
    ∀ b, ∃ m, b < m ∧ m ∈ Aᶜ ∧ ¬ (f m).Dom := by
  classical
  have hinf : A.Infinite := by
    intro hfin
    have hlist : PrimrecRel (fun (xs : List ℕ) (x : ℕ) => x ∈ xs) :=
      (PrimrecRel.exists_mem_list (R := @Eq ℕ) Primrec.eq).of_eq (by intro xs x; simp)
    have hmem := hlist.decide.to_comp.comp (Computable.const hfin.toFinset.toList) Computable.id
    exact hnonrec (hmem.computablePred.of_eq (fun x => Finset.mem_toList.trans hfin.mem_toFinset))
  obtain ⟨ψ, hψ, hψdom, hψasc⟩ := ceAdvance hA hinf
  obtain ⟨χ, hχ, hχdom, hχout⟩ := CofiniteDomainLemma.partrec_union hf hψ
  have hdom (x : ℕ) : (χ x).Dom ↔ (f x).Dom ∨ x ∈ A := (hχdom x).trans (or_congr_right (hψdom x))
  have hχasc : Ascending A χ := fun x y hy => (hχout x y hy).elim (hasc x y) (hψasc x y)
  intro b
  obtain ⟨m, hm, hb⟩ := (CofiniteDomainLemma A χ hnonrec hnoncyl hχ hχasc).exists_gt b
  have hout : ¬ ((f m).Dom ∨ m ∈ A) := fun h => hm ((hdom m).mpr h)
  exact ⟨m, hb, fun ha => hout (Or.inr ha), fun hd => hout (Or.inl hd)⟩

theorem restrictRequirements (A : Set ℕ) (hA : REPred (fun x => x ∈ A))
    (hnonrec : ¬ ComputablePred (fun x => x ∈ A)) (hnoncyl : NonCylinder A)
    (T : PriorityRequirements.VerificationTrace canonicalNumbering rowAt Aᶜ) :
    (∀ e, (∀ x y, y ∈ row e x → (y ∈ A ↔ x ∈ A)) →
      ∃ x, (row e x).Finite ∧ row e x ⊆ T.output) ∧
    (∀ e, Ascending A (canonicalNumbering e) →
      ∃ m, m ∈ Aᶜ ∧ m ∉ T.output ∧ ¬ (canonicalNumbering e m).Dom) := by
  exact ⟨fun e hhom => T.upper_met row monotone_rowAt mem_row_iff_exists_stage e
    (avoidComplement A hA hnonrec hnoncyl e hhom),
    fun e hasc => T.lower_met e
      (omittedAbove A hA hnonrec hnoncyl (canonicalNumbering e)
        (canonicalNumbering_acceptable.1 e) hasc)⟩

theorem complementOracle (A : Set ℕ) (hA : REPred (fun x => x ∈ A)) :
    Nat.RecursiveIn
      {(by classical exact fun n => Part.some (if n ∈ PriorityRequirements.haltingOracle canonicalNumbering then 1 else 0))}
      (fun m => Part.some (@ite ℕ (m ∈ Aᶜ) (Classical.propDecidable _) 1 0)) := by
  classical
  obtain ⟨c, hc⟩ := (ComputablyEnumerableSet.nat_rePred_iff_exists_code A).mp hA
  let e := Encodable.encode c
  let K := PriorityRequirements.haltingOracle canonicalNumbering
  let answer (n : ℕ) : ℕ := if n ∈ K then 1 else 0
  let O : Set (ℕ →. ℕ) := {fun n => Part.some (answer n)}
  let Rel (f : ℕ → ℕ) := Nat.RecursiveIn O (fun n => Part.some (f n))
  have liftOrdinary {f : ℕ → ℕ} (hf : Computable f) : Rel f :=
    RecursiveIn.iff_nat.mp hf.computableIn
  have relComp {f g : ℕ → ℕ} (hf : Rel f) (hg : Rel g) :
      Rel (fun n => f (g n)) :=
    (Nat.RecursiveIn.comp hf hg).of_eq (fun _ => Part.bind_some _ _)
  have hanswer : Rel answer := Nat.RecursiveIn.oracle _ (Set.mem_singleton _)
  have hquery : Rel (Nat.pair e) :=
    liftOrdinary (Primrec₂.natPair.to_comp.comp (Computable.const e) Computable.id)
  have hswap : Rel (fun k : ℕ => 1 - k) :=
    liftOrdinary (Primrec.nat_sub.to_comp.comp (Computable.const 1) Computable.id)
  refine (relComp hswap (relComp hanswer hquery)).of_eq fun m => ?_
  have hiff : Nat.pair e m ∈ K ↔ m ∈ A := by
    rw [show Nat.pair e m ∈ K ↔ (canonicalNumbering e m).Dom from
      PriorityRequirements.pair_mem_haltingOracle canonicalNumbering e m]
    simpa [canonicalNumbering, e] using hc m
  by_cases hm : m ∈ A <;> simp [answer, hiff, hm]

theorem existsRestrictedRequirements (A : Set ℕ)
    (hA :
      let encode (n : ℕ) := List.replicate n false
      let decode (w : List Bool) := if w = encode w.length then some w.length else none
      ComputablyEnumerableSet encode decode (List.replicate_left_injective false)
        (fun n => by simp [decode, encode])
        (fun w hw => ite_eq_right (fun h => hw ⟨w.length, h.symm⟩)) A)
    (hnonrec : ¬ ComputablePred (fun x => x ∈ A)) (hnoncyl : NonCylinder A) :
    ∃ N : Set ℕ,
      ({xs : Fin 1 → ℕ | xs 0 ∈ Nᶜ} : Set (Fin 1 → ℕ)) ∈
        (ArithmeticalHierarchyLevels 2 1 (Nat.le_succ 1)).2.1 ∧
      (∀ e, (∀ x y, y ∈ row e x → (y ∈ A ↔ x ∈ A)) →
        ∃ x, (row e x).Finite ∧ row e x ⊆ N) ∧
      (∀ e, Ascending A (canonicalNumbering e) →
        ∃ m, m ∈ Aᶜ ∧ m ∉ N ∧ ¬ (canonicalNumbering e m).Dom) := by
  have hRE := (ComputablyEnumerableSet.nat_rePred_iff false A).mpr hA
  let before (q r : ℕ × ℕ) : Prop := Nat.pair q.1 q.2 < Nat.pair r.1 r.2
  have horder : IsStrictTotalOrder (ℕ × ℕ) before :=
    Nat.pairEquiv.injective.isStrictTotalOrder_onFun (· < ·)
  have hpair : Primrec (fun q : ℕ × ℕ => Nat.pair q.1 q.2) :=
    Primrec₂.natPair.comp Primrec.fst Primrec.snd
  have hbefore : ComputablePred (fun p : (ℕ × ℕ) × (ℕ × ℕ) => before p.1 p.2) :=
    (Primrec.nat_lt.comp (hpair.comp Primrec.fst) (hpair.comp Primrec.snd)).computablePred
  obtain ⟨T, _, hSigma⟩ := PriorityRequirements.existsEffectiveTrace canonicalNumbering rowAt Aᶜ before
    canonicalNumbering_acceptable.2.2.1 canonicalNumbering_acceptable.2.1 computable_rowAt_code
    horder hbefore (complementOracle A hRE)
  exact ⟨T.output, by
    change ({xs : Fin 1 → ℕ | xs 0 ∈ T.output}ᶜᶜ : Set (Fin 1 → ℕ)) ∈
      (ArithmeticalHierarchyLevels 2 1 (Nat.le_succ 1)).1
    simpa using hSigma, restrictRequirements A hRE hnonrec hnoncyl T⟩

end MaslovaRestricted

#print axioms MaslovaRestricted.packedExhaustion
#print axioms MaslovaRestricted.existsRestrictedRequirements
