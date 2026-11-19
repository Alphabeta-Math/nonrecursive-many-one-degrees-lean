import Mathlib
import Proofs.ComputablyEnumerableSet

set_option maxHeartbeats 2000000

theorem InfiniteCEInjectiveEnumeration : (∀ {α : Type*} (encode : α → _root_.List _root_.Bool)
    (decode : _root_.List _root_.Bool → _root_.Option α)
    (hInjective : _root_.Function.Injective encode)
    (hDecode : ∀ x : α, decode (encode x) = _root_.Option.some x)
    (hInvalid : ∀ w : _root_.List _root_.Bool,
      w ∉ _root_.Set.range encode → decode w = _root_.Option.none)
    (A : _root_.Set α),
    _root_.ComputablyEnumerableSet encode decode hInjective hDecode hInvalid A →
    _root_.Set.Infinite A →
    ∃ f : _root_.Nat → α,
      _root_.Computable (fun n : _root_.Nat => encode (f n)) ∧
      _root_.Function.Injective f ∧ _root_.Set.range f = A) :=
(by
  intro α encode decode hInjective hDecode hInvalid A hce hA
  -- Cintioli, arXiv:2609.00419v1, Lemma 1, p. 4, uses the Nat instance
  -- to enumerate R without repetitions. The article-specific Alphabeta Math
  -- Research Portal and its defect report both returned HTTP 404.
  -- Alphabeta Math, thm-infinite-ce-sets-have-computable-injective-enumerations,
  -- step 1.1: unfold the reviewed c.e. supplier and discard its empty case.
  -- Store the binary outputs of e, as suggested by the step's codeword scan.
  -- The reviewed supplier makes these outputs computable on List Bool, so no
  -- computability assumption on decode or Primcodable instance on α is needed.
  rcases hce with hEmpty | ⟨e, he, heRange⟩
  · subst A
    exact (hA Set.finite_empty).elim
  let code (n : ℕ) := encode (e n)
  have hcode : Computable code := he
  have hcodeRange : Set.range code = encode '' A := by
    simpa only [code, Function.comp_def, heRange] using (Set.range_comp encode e)
  have hcodeInfinite : (Set.range code).Infinite := by
    rw [hcodeRange]
    exact hA.image hInjective.injOn

  -- Steps 1.1 and 3.1: search from the start for the least input whose
  -- codeword is absent from the history. Prove termination at this point,
  -- since each finite history omits a value of the infinite codeword range.
  -- The least-fresh search and list recursion follow the construction behind
  -- Tau Ceti's Computable.exists_injective_range (91942aa9ff8cea04d0d9905b80f75c07ce2379c4),
  -- specialized to Nat input and binary outputs and proved with pinned mathlib.
  let fresh (seen : List (List Bool)) (n : ℕ) : Prop := code n ∉ seen
  let decidableFresh : DecidableRel fresh := fun seen n =>
    inferInstanceAs (Decidable (code n ∉ seen))
  have hfreshExists (seen : List (List Bool)) : ∃ n, fresh seen n := by
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hcodeInfinite.exists_notMem_finite seen.finite_toSet
    exact ⟨n, hn⟩
  have hmem : PrimrecRel (fun (seen : List (List Bool)) (w : List Bool) => w ∈ seen) :=
    (PrimrecRel.exists_mem_list (R := @Eq (List Bool)) Primrec.eq).of_eq
      (by intro seen w; simp)
  have htest : ComputablePred (fun p : List (List Bool) × ℕ => fresh p.1 p.2) :=
    (hmem.not.decide.to_comp.comp Computable.fst (hcode.comp Computable.snd)).computablePred
  let next (seen : List (List Bool)) : ℕ := @Nat.find (fresh seen) (decidableFresh seen) (hfreshExists seen)
  have hnext : Computable next := @Computable.find _ _ fresh decidableFresh htest hfreshExists
  let history (n : ℕ) : List (List Bool) :=
    Nat.rec [] (fun _ seen => code (next seen) :: seen) n
  have hstep : Computable₂
      (fun (_ : ℕ) (p : ℕ × List (List Bool)) => code (next p.2) :: p.2) :=
    (Computable.list_cons.comp (hcode.comp (hnext.comp (Computable.snd.comp Computable.snd)))
      (Computable.snd.comp Computable.snd)).to₂
  have hhistory : Computable history :=
    Computable.nat_rec Computable.id (Computable.const ([] : List (List Bool))) hstep
  let index (n : ℕ) := next (history n)
  let f (n : ℕ) := e (index n)
  have hf : Computable (fun n => encode (f n)) := hcode.comp (hnext.comp hhistory)

  -- Step 2.1: the history at stage n contains exactly the earlier outputs,
  -- and the selected output at stage n is fresh.
  have hh (n : ℕ) (w : List Bool) :
      w ∈ history n ↔ ∃ i < n, code (index i) = w := by
    induction n with
    | zero => simp [history]
    | succ n ih =>
      change w ∈ code (index n) :: history n ↔ _
      rw [List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨i, hi, rfl⟩)
        · exact ⟨n, Nat.lt_succ_self n, rfl⟩
        · exact ⟨i, Nat.lt_trans hi (Nat.lt_succ_self n), rfl⟩
      · rintro ⟨i, hi, heq⟩
        rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
        · exact Or.inr ⟨i, hlt, heq⟩
        · exact Or.inl heq.symm
  have hfresh (n : ℕ) : code (index n) ∉ history n :=
    @Nat.find_spec (fresh (history n)) (decidableFresh (history n)) (hfreshExists (history n))
  have hne (i j : ℕ) (hij : i < j) : f i ≠ f j := by
    intro heq
    exact hfresh j ((hh j _).mpr ⟨i, hij, congrArg encode heq⟩)
  have hinjective : Function.Injective f := by
    intro i j heq
    rcases lt_trichotomy i j with hij | hij | hji
    · exact (hne i j hij heq).elim
    · exact hij
    · exact (hne j i hji heq.symm).elim

  -- Step 2.1, coverage: any input below the least fresh index has already
  -- appeared. The history at the next stage also contains the current output.
  -- Thus the chosen indices grow strictly and eventually pass each input.
  have hbelow (n k : ℕ) (hk : k < index n) : code k ∈ history n :=
    not_not.mp (@Nat.find_min (fresh (history n)) (decidableFresh (history n))
      (hfreshExists (history n)) k hk)
  have hthrough (n k : ℕ) (hk : k ≤ index n) : code k ∈ history (n + 1) := by
    change code k ∈ code (index n) :: history n
    rcases lt_or_eq_of_le hk with hlt | heq
    · exact List.mem_cons_of_mem _ (hbelow n k hlt)
    · rw [heq]
      exact List.mem_cons_self
  have hindex (n : ℕ) : n ≤ index n := by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      have hlt : index n < index (n + 1) := by
        apply lt_of_not_ge
        intro hn
        exact hfresh (n + 1) (hthrough n (index (n + 1)) hn)
      exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ih hlt)

  -- Step 4.1: lift codeword coverage to A using injectivity of encode.
  refine ⟨f, hf, hinjective, ?_⟩
  rw [← heRange]
  apply Set.Subset.antisymm
  · rintro _ ⟨n, rfl⟩
    exact ⟨index n, rfl⟩
  · rintro _ ⟨k, rfl⟩
    have hk : k < index (k + 1) := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) (hindex (k + 1))
    obtain ⟨i, _, hi⟩ := (hh (k + 1) (code k)).mp (hbelow (k + 1) k hk)
    exact ⟨i, hInjective hi⟩
)

#print axioms InfiniteCEInjectiveEnumeration
