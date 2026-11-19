import Mathlib

import Proofs.InfiniteHomogeneousRows
import Proofs.ComputablyEnumerableSet

set_option maxHeartbeats 2000000

/-- Race two partial computable maps. The domain is their union, and every
    returned value is an output of one of the two maps at the same input. -/
theorem CofiniteDomainLemma.partrec_union
    {φ ψ : ℕ → Part ℕ} (hφ : Partrec φ) (hψ : Partrec ψ) :
    ∃ χ : ℕ → Part ℕ, Partrec χ ∧
      (∀ x, (χ x).Dom ↔ (φ x).Dom ∨ (ψ x).Dom) ∧
      (∀ x y, y ∈ χ x → y ∈ φ x ∨ y ∈ ψ x) := by
  -- For the c.e. branch, the coordinator asks for the bounded-code race.
  -- Nat.Partrec.merge' already implements it: at each fuel, try both codes
  -- with left priority at equal fuel, then use rfindOpt for the first success.
  -- Its soundness and completeness give both clauses even when the maps
  -- return different values on their common domain.
  obtain ⟨χ, hχ, hspec⟩ :=
    Nat.Partrec.merge' (Partrec.nat_iff.mp hφ) (Partrec.nat_iff.mp hψ)
  exact ⟨χ, Partrec.nat_iff.mpr hχ, fun x => (hspec x).2,
    fun x => (hspec x).1⟩

theorem CofiniteDomainLemma : (∀ (A : _root_.Set _root_.Nat) (φ : _root_.Nat → _root_.Part _root_.Nat),
  let cyl : _root_.Set _root_.Nat :=
    {z | ∃ x n : _root_.Nat, x ∈ A ∧ z = _root_.Nat.pair x n}
  ¬ _root_.ComputablePred (fun x : _root_.Nat => x ∈ A) →
  ¬ (_root_.OneOneReducible (fun x : _root_.Nat => x ∈ A) (fun z : _root_.Nat => z ∈ cyl) ∧
     _root_.OneOneReducible (fun z : _root_.Nat => z ∈ cyl) (fun x : _root_.Nat => x ∈ A)) →
  _root_.Partrec φ →
  (∀ x y : _root_.Nat, y ∈ φ x → x < y ∧ (y ∈ A ↔ x ∈ A)) →
  _root_.Set.Infinite ({x : _root_.Nat | _root_.Part.Dom (φ x)}ᶜ)) :=
(by
  intro A φ cyl hnonrec hnoncyl hφ hasc
  classical
  -- Cintioli, §3, Definition 3 and Lemma 4, pp. 6–7.
  -- https://arxiv.org/pdf/2609.00419v1#page=6
  -- The article-specific Alphabeta Math portal and defect report returned
  -- HTTP 404. The proof follows the v1 source and the compiled row supplier.
  by_contra hfinite
  let F : Set ℕ := {x : ℕ | (φ x).Dom}ᶜ
  have hF : F.Finite := not_not.mp hfinite

  -- Finite lists of constants give computable membership tests. Thus a
  -- finite colour, or its computable complement, would make A recursive.
  have hmemRelation : PrimrecRel (fun (xs : List ℕ) (x : ℕ) => x ∈ xs) :=
    (PrimrecRel.exists_mem_list (R := @Eq ℕ) Primrec.eq).of_eq (by
      intro xs x
      simp)
  have hlistMem (xs : List ℕ) : ComputablePred (fun x : ℕ => x ∈ xs) :=
    (hmemRelation.decide.to_comp.comp (Computable.const xs) Computable.id).computablePred
  have hfiniteComp (S : Set ℕ) (hS : S.Finite) : ComputablePred (fun x : ℕ => x ∈ S) :=
    (hlistMem hS.toFinset.toList).of_eq fun x =>
      Finset.mem_toList.trans hS.mem_toFinset
  have hA : A.Infinite := fun h => hnonrec (hfiniteComp A h)
  have hAc : Aᶜ.Infinite := fun h =>
    hnonrec ((hfiniteComp Aᶜ h).not.of_eq (fun x => by simp))

  have htarget (x : ℕ) : ∃ y : ℕ, x < y ∧ (y ∈ A ↔ x ∈ A) := by
    by_cases hx : x ∈ A
    · obtain ⟨y, hy, hxy⟩ := hA.exists_gt x
      exact ⟨y, hxy, iff_of_true hy hx⟩
    · obtain ⟨y, hy, hxy⟩ := hAc.exists_gt x
      exact ⟨y, hxy, iff_of_false hy hx⟩
  choose target htarget_spec using htarget
  let exceptions := hF.toFinset.toList
  have hexceptions (x : ℕ) : x ∈ exceptions ↔ ¬ (φ x).Dom :=
    Finset.mem_toList.trans hF.mem_toFinset

  -- Lemma 4 hardcodes the chosen values only on the finite exceptional set.
  -- The induction implements this table by equality tests and constants.
  have hlookup (xs : List ℕ) :
      Computable (fun x : ℕ => if x ∈ xs then target x else 0) := by
    induction xs with
    | nil => simpa using (Computable.const (0 : ℕ) : Computable (fun _ : ℕ => 0))
    | cons a xs ih =>
      have heq : ComputablePred (fun x : ℕ => x = a) :=
        (Primrec.eq.decide.to_comp.comp Computable.id (Computable.const a)).computablePred
      refine (ComputablePred.ite (Computable.const (target a)) ih heq).of_eq ?_
      intro x
      by_cases hx : x = a
      · subst x
        simp
      · simp [hx]
  let patch (x : ℕ) : Part ℕ :=
    if x ∈ exceptions then Part.some (target x) else φ x
  have hpatch : Partrec patch := by
    refine (Partrec.cond (hlistMem exceptions).decide
      (hlookup exceptions).partrec hφ).of_eq ?_
    intro x
    by_cases hx : x ∈ exceptions <;> simp [patch, hx]
  have hdom (x : ℕ) : (patch x).Dom := by
    by_cases hx : x ∈ exceptions
    · simp [patch, hx]
    · simpa only [patch, ite_eq_right hx] using not_not.mp (mt (hexceptions x).mpr hx)
  let g (x : ℕ) := (patch x).get (hdom x)
  have hgmem (x : ℕ) : g x ∈ patch x := Part.get_mem (hdom x)
  have hg : Computable g := hpatch.of_eq_tot hgmem
  have hg_spec (x : ℕ) : x < g x ∧ (g x ∈ A ↔ x ∈ A) := by
    by_cases hx : x ∈ exceptions
    · have h : g x = target x := by simpa [patch, hx] using hgmem x
      rw [h]
      exact htarget_spec x
    · exact hasc x (g x) (by simpa only [patch, ite_eq_right hx] using hgmem x)

  let orbit (x n : ℕ) : ℕ := Nat.rec x (fun _ y => g y) n
  let W (x : ℕ) := Set.range (orbit x)
  have horbit : Computable₂ orbit :=
    (Computable.nat_rec Computable.snd Computable.fst (hg.comp
      (Computable.snd.comp Computable.snd)).to₂).to₂
  have hinfinite (x : ℕ) : (W x).Infinite :=
    Set.infinite_range_of_injective (strictMono_nat_of_lt_succ (f := orbit x)
      (fun n => (hg_spec (orbit x n)).1)).injective
  have hcolour (x n : ℕ) : orbit x n ∈ A ↔ x ∈ A := by
    induction n with
    | zero => rfl
    | succ n ih => exact (hg_spec (orbit x n)).2.trans ih
  have hhom (x y : ℕ) (hy : y ∈ W x) : y ∈ A ↔ x ∈ A := by
    obtain ⟨n, rfl⟩ := hy
    exact hcolour x n

  -- https://alphabetamath.cc/item/thm-recognizable-iff-enumerable
  -- Step 1.1 searches a total enumerator. Here the values being enumerated
  -- are packed Nat pairs.
  -- The compiled ComputablyEnumerableSet range recognizer and true-bit
  -- bridge supply the c.e. graph premise with the supplier’s encoding.
  -- Both apply to Nat sets, so the optional Tau Ceti import is unnecessary.
  let graph : Set ℕ := {z | ∃ x y : ℕ, y ∈ W x ∧ z = Nat.pair x y}
  let pack (i : ℕ) := Nat.pair i.unpair.1 (orbit i.unpair.1 i.unpair.2)
  have hpack : Computable pack :=
    (Primrec₂.natPair.to_comp.comp Computable.fst horbit).comp Computable.unpair
  have hgraph : Set.range pack = graph := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.unpair.1, orbit i.unpair.1 i.unpair.2, ⟨i.unpair.2, rfl⟩, rfl⟩
    · rintro ⟨x, y, ⟨n, rfl⟩, rfl⟩
      exact ⟨Nat.pair x n, by simp [pack, Nat.unpair_pair]⟩
  have hRE : REPred (fun z => z ∈ graph) := by
    rw [← hgraph]
    exact ComputablyEnumerableSet.nat_rePred_range hpack

  -- Lemma 4 builds its fresh-output reduction directly. We apply the
  -- reviewed §3 observation to these orbit rows.
  -- https://alphabetamath.cc/item/thm-infinite-ce-sets-have-computable-injective-enumerations
  -- Steps 1.1, 2.1 and 3.1 motivate keeping prior outputs, freshness and
  -- termination. The supplier uses the row indexed by each input; it
  -- therefore needs uniform enumerability and infinitude for every row.
  have hbackward : OneOneReducible (fun z => z ∈ cyl) (fun x => x ∈ A) :=
    InfiniteHomogeneousRows A W
      ((ComputablyEnumerableSet.nat_rePred_iff true graph).mp hRE) hhom hinfinite
  have hforward : OneOneReducible (fun x => x ∈ A) (fun z => z ∈ cyl) := by
    refine ⟨fun x => Nat.pair x 0,
      Primrec₂.natPair.to_comp.comp Computable.id (Computable.const 0), ?_, ?_⟩
    · intro x y h
      exact congrArg Prod.fst (Nat.pairEquiv.injective h : (x, 0) = (y, 0))
    · intro x
      change x ∈ A ↔ ∃ y n : ℕ, y ∈ A ∧ Nat.pair x 0 = Nat.pair y n
      constructor
      · exact fun hx => ⟨x, 0, hx, rfl⟩
      · rintro ⟨y, n, hy, heq⟩
        have hxy : x = y :=
          congrArg Prod.fst (Nat.pairEquiv.injective heq : (x, 0) = (y, n))
        exact hxy ▸ hy
  exact hnoncyl ⟨hforward, hbackward⟩)
