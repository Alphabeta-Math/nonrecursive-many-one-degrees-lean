import Mathlib

import Proofs.ManyOneReducibilityOnNat
import Proofs.ComputablyEnumerableSet

set_option maxHeartbeats 2000000

/- The article-specific Alphabeta Math portal and defect report for
   arXiv:2609.00419 returned HTTP 404. Reference [1] is arXiv:2603.02600.
   Its Corollaries 5.4 and 5.5 give the finite-one and typicality conclusions.
   arXiv:2602.19960v3 §3 proves one-one incomparability. Finite-one
   reducibility permits more witnesses, so the structural proof follows
   §5 of reference [1]. The fixed-function measure argument follows
   arXiv:2602.19960v3, Proposition 4.1. -/
namespace RigidDegreeAntichainProof

open Set MeasureTheory Filter
open scoped ENNReal

private def Rigid (A : Set ℕ) : Prop :=
  ∀ f : ℕ → ℕ, Computable f → (∀ n, n ∈ A ↔ f n ∈ A) →
    ∃ N : ℕ, ∀ n, N ≤ n → f n = n

private def FiniteOne (A B : Set ℕ) : Prop :=
  ∃ f : ℕ → ℕ, Computable f ∧ (∀ n, n ∈ A ↔ f n ∈ B) ∧
    ∀ y, Set.Finite {n | f n = y}

private def Antichain (A : Set ℕ) : Prop :=
  ∃ B : ℕ → Set ℕ,
    (∀ i, ManyOneReducibilityOnNat (B i) A ∧ ManyOneReducibilityOnNat A (B i)) ∧
    Pairwise (fun i j => ¬ FiniteOne (B i) (B j) ∧ ¬ FiniteOne (B j) (B i))

private def project (i n : ℕ) : ℕ :=
  if n.unpair.1 = 0 then n.unpair.2 else Nat.pair i n.unpair.2

private theorem computableLeft : Computable (fun n : ℕ => n.unpair.1) :=
  Computable.fst.comp Primrec.unpair.to_comp

private theorem computableProject (i : ℕ) : Computable (project i) := by
  have hs : Computable (fun n : ℕ => n.unpair.2) :=
    Computable.snd.comp Primrec.unpair.to_comp
  have hz : Computable (fun n : ℕ => decide (n.unpair.1 = 0)) :=
    Primrec.eq.decide.to_comp.comp computableLeft (Computable.const 0)
  unfold project
  simpa only [Bool.cond_eq_ite, decide_eq_true_eq] using
    hz.cond hs (Primrec₂.natPair.to_comp.comp (Computable.const i) hs)

private theorem structural (A : Set ℕ) (hA : Rigid A) : Antichain A := by
  -- Cintioli, arXiv:2603.02600v2, Def. 5.1 and Lemma 5.2.
  -- Alphabeta Math, lem-many-one-reducibility-is-a-preorder, steps 1.2
  -- and 2.1: compose total computable maps and check membership at each
  -- input. Here projection and the base-column section are explicit.
  -- For Sᵢ = range (Nat.pair i), the code pair 0 x stands for (x,0).
  -- The code pair (k+1) t stands for (pair i t,k+1). This explicit coding
  -- replaces enumeration of the calibrated domain and search for its inverse.
  let B (i : ℕ) : Set ℕ := {n | project i n ∈ A}
  refine ⟨B, fun i => ⟨⟨project i, computableProject i, fun _ => Iff.rfl⟩,
    ⟨Nat.pair 0, Primrec₂.natPair.to_comp.comp (Computable.const 0) Computable.id,
      fun x => by change x ∈ A ↔ project i (Nat.pair 0 x) ∈ A; simp [project]⟩⟩, ?_⟩
  have incomparable (i j : ℕ) (hij : i ≠ j) : ¬ FiniteOne (B i) (B j) := by
    rintro ⟨f, hf, hfA, hfibre⟩
    let out (x k : ℕ) := project j (f (Nat.pair (k + 1) x.unpair.2))
    have hout : Computable (fun p : ℕ × ℕ => out p.1 p.2) :=
      (computableProject j).comp (hf.comp (Primrec₂.natPair.to_comp.comp
        (Computable.succ.comp Computable.snd)
        (Computable.snd.comp (Primrec.unpair.to_comp.comp Computable.fst))))
    -- In Theorem 5.3 the search asks for an output over Sⱼ and uses
    -- bi-immunity. Here an output projecting away from x suffices.
    -- For x ∈ Sᵢ its target fibre consists only of pair 0 x, so finite
    -- fibres of f guarantee this weaker search succeeds. The
    -- installed ComputablyEnumerableSet range lemmas serve the
    -- bi-immunity route. The singleton-fibre argument needs only
    -- the installed ManyOneReducibilityOnNat witness interface.
    have hex (x : ℕ) (hx : x.unpair.1 = i) : ∃ k, out x k ≠ x := by
      by_contra! hh
      have hcol (k : ℕ) : f (Nat.pair (k + 1) x.unpair.2) = Nat.pair 0 x := by
        let n := f (Nat.pair (k + 1) x.unpair.2)
        have heq : project j n = x := hh k
        by_cases hz : n.unpair.1 = 0
        · have hs : n.unpair.2 = x := by simpa [project, hz] using heq
          change n = Nat.pair 0 x
          rw [← Nat.pair_unpair n, hz, hs]
        · have hs : Nat.pair j n.unpair.2 = x := by simpa [project, hz] using heq
          have hj := congrArg (fun m : ℕ => m.unpair.1) hs
          simp [hx] at hj
          exact (hij hj.symm).elim
      have hinj : Function.Injective (fun k : ℕ => Nat.pair (k + 1) x.unpair.2) := by
        intro a b hab
        simpa using congrArg (fun m : ℕ => m.unpair.1) hab
      exact (Set.infinite_range_of_injective hinj)
        ((hfibre (Nat.pair 0 x)).subset (by rintro _ ⟨k, rfl⟩; exact hcol k))
    -- Use a guard in the witness test to make least search total off Sᵢ.
    let P (x k : ℕ) := x.unpair.1 ≠ i ∨ out x k ≠ x
    let _ : DecidableRel P := fun x k =>
      inferInstanceAs (Decidable (x.unpair.1 ≠ i ∨ out x k ≠ x))
    have hP : ComputablePred (fun p : ℕ × ℕ => P p.1 p.2) := by
      have hc : Computable (fun p : ℕ × ℕ => decide (p.1.unpair.1 = i)) :=
        Primrec.eq.decide.to_comp.comp (computableLeft.comp Computable.fst) (Computable.const i)
      have hd : Computable (fun p : ℕ × ℕ => decide (out p.1 p.2 = p.1)) :=
        Primrec.eq.decide.to_comp.comp hout Computable.fst
      apply Computable.computablePred
      refine (Primrec.or.to_comp.comp (Primrec.not.to_comp.comp hc)
        (Primrec.not.to_comp.comp hd)).of_eq ?_
      intro p
      simp [P]
    have htot (x : ℕ) : ∃ k, P x k := by
      by_cases hx : x.unpair.1 = i
      · obtain ⟨k, hk⟩ := hex x hx
        exact ⟨k, Or.inr hk⟩
      · exact ⟨0, Or.inl hx⟩
    let idx (x : ℕ) := Nat.find (htot x)
    have hidx : Computable idx := Computable.find hP htot
    let g (x : ℕ) := if x.unpair.1 = i then out x (idx x) else x
    have hg : Computable g := by
      have hc : Computable (fun x : ℕ => decide (x.unpair.1 = i)) :=
        Primrec.eq.decide.to_comp.comp computableLeft (Computable.const i)
      simpa only [g, Bool.cond_eq_ite, decide_eq_true_eq, id_eq] using
        hc.cond (hout.comp (Computable.id.pair hidx)) Computable.id
    have hgA (x : ℕ) : x ∈ A ↔ g x ∈ A := by
      by_cases hx : x.unpair.1 = i
      · have heq : project i (Nat.pair (idx x + 1) x.unpair.2) = x := by
          simp [project, ← hx]
        have hh := hfA (Nat.pair (idx x + 1) x.unpair.2)
        change project i (Nat.pair (idx x + 1) x.unpair.2) ∈ A ↔ out x (idx x) ∈ A at hh
        simpa [heq, g, hx] using hh
      · simp [g, hx]
    obtain ⟨N, hN⟩ := hA g hg hgA
    let x := Nat.pair i N
    have hx : x.unpair.1 = i := by simp [x]
    have hne : out x (idx x) ≠ x := (Nat.find_spec (htot x)).resolve_left (not_not_intro hx)
    exact hne (by simpa [g, hx] using hN x (Nat.right_le_pair i N))
  exact fun i j hij => ⟨incomparable i j hij, incomparable j i hij.symm⟩

private def asSet (a : ℕ → Bool) : Set ℕ := {n | a n = true}

private noncomputable def coin : Measure Bool := Measure.uniformOfFinset Finset.univ

private local instance : IsProbabilityMeasure coin := by
  constructor
  simp [coin, Measure.uniformOfFinset_apply, ENNReal.div_self]

private noncomputable def fairCoin : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => coin)

private local instance : IsProbabilityMeasure fairCoin := by
  unfold fairCoin
  infer_instance

private def agrees (f : ℕ → ℕ) : Set (ℕ → Bool) :=
  {a | ∀ n, a n = a (f n)}

private theorem closedAgrees (f : ℕ → ℕ) : IsClosed (agrees f) := by
  change IsClosed {a : ℕ → Bool | ∀ n, a n = a (f n)}
  rw [Set.ofPred_forall]
  exact isClosed_iInter fun n => isClosed_eq (continuous_apply n) (continuous_apply (f n))

private theorem residual_agrees_compl {f : ℕ → ℕ}
    (hm : ∀ N, ∃ n, N ≤ n ∧ f n ≠ n) :
    (agrees f)ᶜ ∈ residual (ℕ → Bool) := by
  -- Alphabeta Math, lem-cantor-and-baire-sequence-coding, steps 1.1 and
  -- 2.1: use the finite prefix basis and change an unrestricted bit.
  -- Here its new value must differ from the bit at the image coordinate.
  -- lem-open-dense-and-closed-nowhere-dense-baire-forms-are-equivalent-in-zf,
  -- steps 1.1 and 2.1: check density on each nonempty open set and apply
  -- the open-complement criterion to the closed agreement set.
  apply residual_of_dense_open (closedAgrees f).isOpen_compl
  rw [dense_iff_inter_open]
  rintro U hU ⟨a, ha⟩
  obtain ⟨_, ⟨b, N, rfl⟩, hab, hsub⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ => Bool)).exists_subset_of_mem_open ha hU
  obtain ⟨n, hn, hfn⟩ := hm N
  let c : ℕ → Bool := Function.update a n (!(a (f n)))
  refine ⟨c, hsub (PiNat.mem_cylinder_iff.mpr ?_), ?_⟩
  · intro k hk
    simpa [c, Function.update_of_ne (show k ≠ n by omega)] using
      PiNat.mem_cylinder_iff.mp hab k hk
  · intro hc
    have heq := hc n
    simp only [c, Function.update_self, Function.update_of_ne hfn] at heq
    cases h : a (f n) <;> simp [h] at heq

private def flip (n : ℕ) (a : ℕ → Bool) (k : ℕ) : Bool :=
  if k = n then !(a k) else a k

private theorem map_flip (n : ℕ) : Measure.map (flip n) fairCoin = fairCoin := by
  have hcoin : Measure.map Bool.not coin = coin := by
    apply Measure.ext_of_singleton
    intro b
    rw [Measure.map_apply (measurable_of_finite _)
      (MeasurableSet.singleton b)]
    have hpre : Bool.not ⁻¹' {b} = {!(b)} := by
      ext a
      change (Bool.not a = b) ↔ a = Bool.not b
      cases a <;> cases b <;> decide
    rw [hpre]
    simp [coin]
  have hmeas (k : ℕ) : Measurable (fun b : Bool => if k = n then !b else b) :=
    measurable_of_finite _
  change Measure.map (fun a k => if k = n then !(a k) else a k) fairCoin = fairCoin
  unfold fairCoin
  rw [Measure.infinitePi_map_pi _ hmeas]
  congr 1
  funext k
  by_cases hk : k = n
  · simpa [hk] using hcoin
  · simp [hk]

private theorem measure_inter_agreement {C : Set (ℕ → Bool)} {n m : ℕ}
    (hC : MeasurableSet C) (hnm : n ≠ m)
    (hflip : ∀ a, flip n a ∈ C ↔ a ∈ C) :
    fairCoin (C ∩ {a | a n = a m}) = fairCoin C / 2 := by
  -- A fair-coin coordinate flip is measure preserving. It interchanges
  -- the agreeing and disagreeing halves of an event independent of n.
  let E : Set (ℕ → Bool) := {a | a n = a m}
  have hE : MeasurableSet E := measurableSet_eq_fun (measurable_pi_apply n) (measurable_pi_apply m)
  have hm : Measurable (flip n) := Measurable.of_eval fun k => by
    by_cases hk : k = n
    · simpa [flip, hk, Function.comp_def] using
        (measurable_of_finite Bool.not).comp (measurable_pi_apply n)
    · simpa [flip, hk] using (measurable_pi_apply k : Measurable (fun a : ℕ → Bool => a k))
  have hsplit : flip n ⁻¹' (C ∩ E) = C ∩ Eᶜ := by
    ext a
    change (flip n a ∈ C ∧ flip n a n = flip n a m) ↔ (a ∈ C ∧ ¬ a n = a m)
    rw [hflip]
    simp only [flip, ite_eq_right hnm.symm]
    cases a n <;> cases a m <;> simp
  have hequal : fairCoin (C ∩ E) = fairCoin (C ∩ Eᶜ) := by
    rw [← hsplit, ← Measure.map_apply hm (hC.inter hE), map_flip]
  have hdisj : Disjoint (C ∩ E) (C ∩ Eᶜ) := by
    exact disjoint_compl_right.mono Set.inter_subset_right Set.inter_subset_right
  have hunion : (C ∩ E) ∪ (C ∩ Eᶜ) = C := by
    ext a
    simp
  have hsum := measure_union (μ := fairCoin) hdisj (hC.inter hE.compl)
  rw [hunion, ← hequal] at hsum
  apply (ENNReal.eq_div_iff (by norm_num) (by simp)).2
  simpa [two_mul] using hsum.symm

private theorem measure_agrees_zero {f : ℕ → ℕ}
    (hm : ∀ N, ∃ n, N ≤ n ∧ f n ≠ n) : fairCoin (agrees f) = 0 := by
  -- Cintioli, arXiv:2602.19960v3, Proposition 4.1, p. 6.
  -- We retain finite supports and halve the cylinder mass by a coordinate
  -- flip. The almost-everywhere endpoint needs only existence of the
  -- finite tests, so no effective sequence or randomness test is needed.
  have hconstraints (t : ℕ) : ∃ (s : Finset ℕ) (C : Set (ℕ → Bool)),
      MeasurableSet C ∧ agrees f ⊆ C ∧ fairCoin C = (2⁻¹ : ℝ≥0∞) ^ t ∧
      ∀ a b : ℕ → Bool, (∀ k ∈ s, a k = b k) → (a ∈ C ↔ b ∈ C) := by
    induction t with
    | zero => exact ⟨∅, univ, MeasurableSet.univ, Set.subset_univ _, by simp, by simp⟩
    | succ t ih =>
      obtain ⟨s, C, hC, hsub, hmass, hdep⟩ := ih
      obtain ⟨n, hn, hfn⟩ := hm (s.sup Nat.succ)
      have hns : n ∉ s := fun hn' => by
        have hle : n.succ ≤ s.sup Nat.succ := Finset.le_sup (f := Nat.succ) hn'
        omega
      let E : Set (ℕ → Bool) := {a | a n = a (f n)}
      have hE : MeasurableSet E :=
        measurableSet_eq_fun (measurable_pi_apply n) (measurable_pi_apply (f n))
      have hflip (a : ℕ → Bool) : flip n a ∈ C ↔ a ∈ C := by
        apply hdep
        intro k hk
        have hkn : k ≠ n := fun he => hns (he ▸ hk)
        simp [flip, hkn]
      refine ⟨insert n (insert (f n) s), C ∩ E, hC.inter hE,
        fun a ha => ⟨hsub ha, ha n⟩, ?_, ?_⟩
      · rw [measure_inter_agreement hC hfn.symm hflip, hmass, pow_succ, div_eq_mul_inv]
      · intro a b hab
        have hs : ∀ k ∈ s, a k = b k := fun k hk => hab k (by simp [hk])
        have h₁ := hab n (by simp)
        have h₂ := hab (f n) (by simp)
        change (a ∈ C ∧ a n = a (f n)) ↔ (b ∈ C ∧ b n = b (f n))
        rw [hdep a b hs, h₁, h₂]
  have hle (t : ℕ) : fairCoin (agrees f) ≤ (2⁻¹ : ℝ≥0∞) ^ t := by
    obtain ⟨_, C, _, hC, hmass, _⟩ := hconstraints t
    exact (measure_mono hC).trans_eq hmass
  refine le_antisymm ?_ bot_le
  exact le_of_tendsto_of_tendsto tendsto_const_nhds
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num))
    (Eventually.of_forall hle)

private noncomputable def codeFunction (c : Nat.Partrec.Code) (n : ℕ) : ℕ :=
  open scoped Classical in
  if h : (c.eval n).Dom then (c.eval n).get h else 0

private theorem exists_codeFunction (f : ℕ → ℕ) (hf : Computable f) :
    ∃ c, codeFunction c = f := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hf.partrec)
  refine ⟨c, funext fun n => ?_⟩
  unfold codeFunction
  rw [hc]
  simp [PFun.coe_val]

private def obeys (f : ℕ → ℕ) (a : ℕ → Bool) : Prop :=
  a ∈ agrees f → ∃ N : ℕ, ∀ n, N ≤ n → f n = n

private theorem eventually_obeys {l : Filter (ℕ → Bool)}
    (f : ℕ → ℕ) (h : (∀ N, ∃ n, N ≤ n ∧ f n ≠ n) →
      (agrees f)ᶜ ∈ l) : ∀ᶠ a in l, obeys f a := by
  by_cases ht : ∃ N : ℕ, ∀ n, N ≤ n → f n = n
  · exact Eventually.of_forall fun _ _ => ht
  · have hm : ∀ N, ∃ n, N ≤ n ∧ f n ≠ n := by push Not at ht; exact ht
    have havoids : ∀ᶠ a in l, a ∉ agrees f := h hm
    exact havoids.mono fun _ ha hfix => (ha hfix).elim

private theorem eventually_rigid {l : Filter (ℕ → Bool)} [CountableInterFilter l]
    (h : ∀ f : ℕ → ℕ, (∀ N, ∃ n, N ≤ n ∧ f n ≠ n) → (agrees f)ᶜ ∈ l) :
    ∀ᶠ a in l, Rigid (asSet a) := by
  -- Every total computable map is represented by a partial-recursive code.
  -- The default on undefined arguments is used only to index the tests by
  -- this countable type. Each individual test applies to arbitrary maps.
  -- The countable intersection of open dense complements gives the
  -- residual conclusion, as in the same Alphabeta item, step 3.1.
  have hc : ∀ᶠ a in l, ∀ c : Nat.Partrec.Code, obeys (codeFunction c) a :=
    eventually_countable_forall.mpr (fun c => eventually_obeys _ (h _))
  refine hc.mono fun a ha f hf hself => ?_
  obtain ⟨c, hc⟩ := exists_codeFunction f hf
  rw [← hc]
  apply ha c
  rw [hc]
  exact fun n => Bool.eq_iff_iff.mpr (hself n)

private theorem ae_rigid : ∀ᵐ a ∂fairCoin, Rigid (asSet a) := by
  apply eventually_rigid
  intro f hf
  apply ae_iff.mpr
  have heq : {a | ¬ a ∉ agrees f} = agrees f := Set.ext (by simp)
  rw [heq]
  exact measure_agrees_zero hf

private theorem residual_rigid : ∀ᶠ a in residual (ℕ → Bool), Rigid (asSet a) :=
  eventually_rigid fun _ => residual_agrees_compl

private theorem mass_rigid : fairCoin {a | Rigid (asSet a)} = 1 := by
  have h : {a | Rigid (asSet a)} =ᵐ[fairCoin] (univ : Set (ℕ → Bool)) :=
    ae_rigid.mono fun _ ha => by simp [ha]
  rw [measure_congr h, measure_univ]

end RigidDegreeAntichainProof

theorem RigidDegreeAntichain : (let rigid := fun A : _root_.Set _root_.Nat =>
  ∀ f : _root_.Nat → _root_.Nat, _root_.Computable f →
    (∀ n : _root_.Nat, n ∈ A ↔ f n ∈ A) →
    ∃ N : _root_.Nat, ∀ n : _root_.Nat, N ≤ n → f n = n
let finiteOne := fun A B : _root_.Set _root_.Nat =>
  ∃ f : _root_.Nat → _root_.Nat, _root_.Computable f ∧
    (∀ n : _root_.Nat, n ∈ A ↔ f n ∈ B) ∧
    (∀ y : _root_.Nat, _root_.Set.Finite {n : _root_.Nat | f n = y})
let hasAntichain := fun A : _root_.Set _root_.Nat =>
  ∃ B : _root_.Nat → _root_.Set _root_.Nat,
    (∀ i : _root_.Nat,
      _root_.ManyOneReducibilityOnNat (B i) A ∧ _root_.ManyOneReducibilityOnNat A (B i)) ∧
    _root_.Pairwise (fun i j => ¬ finiteOne (B i) (B j) ∧ ¬ finiteOne (B j) (B i))
let asSet := fun a : _root_.Nat → _root_.Bool => {n : _root_.Nat | a n = _root_.Bool.true}
let fairCoin := _root_.MeasureTheory.Measure.infinitePi
  (fun _ : _root_.Nat =>
    _root_.MeasureTheory.Measure.uniformOfFinset (_root_.Finset.univ : _root_.Finset _root_.Bool))
(∀ A : _root_.Set _root_.Nat, rigid A → hasAntichain A) ∧
  fairCoin {a | rigid (asSet a)} = 1 ∧
  _root_.Filter.Eventually (fun a => rigid (asSet a)) (_root_.residual (_root_.Nat → _root_.Bool)) ∧
  _root_.Filter.Eventually (fun a => hasAntichain (asSet a)) (_root_.MeasureTheory.ae fairCoin) ∧
  _root_.Filter.Eventually (fun a => hasAntichain (asSet a)) (_root_.residual (_root_.Nat → _root_.Bool))) :=
(by
  open RigidDegreeAntichainProof in
  exact ⟨structural, mass_rigid, residual_rigid,
    ae_rigid.mono (fun a ha => structural (asSet a) ha),
    residual_rigid.mono (fun a ha => structural (asSet a) ha)⟩)

#print axioms RigidDegreeAntichain
