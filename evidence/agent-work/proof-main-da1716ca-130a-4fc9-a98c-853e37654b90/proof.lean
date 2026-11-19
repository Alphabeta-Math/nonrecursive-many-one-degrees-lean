by
  intro A W encode decode hce hhom hinfinite
  -- Cintioli, arXiv:2609.00419v1, §3, pp. 4–5, uses the computable
  -- enumeration of pairs without repetition. Here stage k treats Nat.unpair k.
  -- The article-specific Alphabeta Math portal and defect report returned HTTP 404.
  -- The reviewed c.e. supplier gives a domain code for the packed row graph.
  -- Bounded evaluation of that code suffices for the search.
  let graph : Set ℕ := {z | ∃ x y : ℕ, y ∈ W x ∧ z = Nat.pair x y}
  have hgraph : REPred (fun z => z ∈ graph) :=
    (ComputablyEnumerableSet.nat_rePred_iff true graph).mpr hce
  obtain ⟨code, hcode⟩ :=
    (ComputablyEnumerableSet.nat_rePred_iff_exists_code graph).mp hgraph
  have hstage (x y : ℕ) :
      y ∈ W x ↔ ∃ fuel, (code.evaln fuel (Nat.pair x y)).isSome := by
    have hpair : Nat.pair x y ∈ graph ↔ y ∈ W x := by
      constructor
      · rintro ⟨row, value, hmem, heq⟩
        have hxy : (x, y) = (row, value) := by
          simpa only [Nat.unpair_pair] using congrArg Nat.unpair heq
        cases hxy
        exact hmem
      · intro hmem
        exact ⟨x, y, hmem, rfl⟩
    rw [← hpair, ← hcode, Part.dom_iff_mem]
    constructor
    · rintro ⟨out, hout⟩
      obtain ⟨fuel, hfuel⟩ := Nat.Partrec.Code.evaln_complete.mp hout
      exact ⟨fuel, Option.isSome_iff_exists.mpr ⟨out, hfuel⟩⟩
    · rintro ⟨fuel, hfuel⟩
      obtain ⟨out, hout⟩ := Option.isSome_iff_exists.mp hfuel
      exact ⟨out, Nat.Partrec.Code.evaln_complete.mpr ⟨fuel, hout⟩⟩

  -- https://alphabetamath.cc/item/thm-infinite-ce-sets-have-computable-injective-enumerations
  -- steps 1.1 and 3.1 motivate keeping the earlier outputs and using infinitude
  -- for termination. Here the required row varies with the input, so search
  -- jointly for a candidate and enough fuel to certify its row membership.
  let bounded (p : (ℕ × List ℕ) × ℕ) :=
    code.evaln p.2.unpair.2 (Nat.pair p.1.1.unpair.1 p.2.unpair.1)
  let eligible (state : ℕ × List ℕ) (k : ℕ) : Prop :=
    (bounded (state, k)).isSome ∧ k.unpair.1 ∉ state.2
  let : DecidableRel eligible := fun state k => by
    unfold eligible
    infer_instance
  have hrow : Computable (fun p : (ℕ × List ℕ) × ℕ => p.1.1.unpair.1) :=
    Computable.fst.comp (Primrec.unpair.to_comp.comp (Computable.fst.comp Computable.fst))
  have hcandidate : Computable (fun p : (ℕ × List ℕ) × ℕ => p.2.unpair.1) :=
    Computable.fst.comp (Primrec.unpair.to_comp.comp Computable.snd)
  have hfuel : Computable (fun p : (ℕ × List ℕ) × ℕ => p.2.unpair.2) :=
    Computable.snd.comp (Primrec.unpair.to_comp.comp Computable.snd)
  have hbounded : Computable bounded :=
    Nat.Partrec.Code.primrec_evaln.to_comp.comp
      ((hfuel.pair (Computable.const code)).pair (Primrec₂.natPair.to_comp.comp hrow hcandidate))
  have hmem : PrimrecRel (fun (xs : List ℕ) (y : ℕ) => y ∈ xs) :=
    (PrimrecRel.exists_mem_list (R := @Eq ℕ) Primrec.eq).of_eq (by intro xs y; simp)
  have heligible : ComputablePred (fun p : (ℕ × List ℕ) × ℕ => eligible p.1 p.2) := by
    apply Computable.computablePred
    refine (Primrec.and.to_comp.comp (Primrec.option_isSome.to_comp.comp hbounded)
      (hmem.not.decide.to_comp.comp (Computable.snd.comp Computable.fst) hcandidate)).of_eq ?_
    intro p
    simp [eligible]
  have hexists (state : ℕ × List ℕ) : ∃ k, eligible state k := by
    obtain ⟨y, hy, hnew⟩ := (hinfinite state.1.unpair.1).exists_notMem_finset state.2.toFinset
    obtain ⟨fuel, hfound⟩ := (hstage _ _).mp hy
    have hnotUsed : y ∉ state.2 := by simpa using hnew
    exact ⟨Nat.pair y fuel, by simpa [eligible, bounded] using And.intro hfound hnotUsed⟩
  let choose (state : ℕ × List ℕ) := (Nat.find (hexists state)).unpair.1
  have hchoose : Computable choose :=
    (Computable.fst.comp Primrec.unpair.to_comp).comp (Computable.find heligible hexists)
  have hchosen (state : ℕ × List ℕ) :
      choose state ∈ W state.1.unpair.1 ∧ choose state ∉ state.2 := by
    have hs := Nat.find_spec (hexists state)
    exact ⟨(hstage _ _).mpr ⟨(Nat.find (hexists state)).unpair.2, hs.1⟩, hs.2⟩

  let history (n : ℕ) : List ℕ :=
    Nat.rec [] (fun k xs => choose (k, xs) :: xs) n
  have hstep : Computable₂ (fun (_ : ℕ) (p : ℕ × List ℕ) => choose p :: p.2) :=
    (Computable.list_cons.comp (hchoose.comp Computable.snd)
      (Computable.snd.comp Computable.snd)).to₂
  have hhistory : Computable history :=
    Computable.nat_rec Computable.id (Computable.const ([] : List ℕ)) hstep
  let f (n : ℕ) := choose (n, history n)
  have hf : Computable f := hchoose.comp (Computable.id.pair hhistory)
  -- Step 2.1 uses freshness for injectivity. Every earlier output belongs to
  -- the current history. Surjectivity onto a row is unnecessary here.
  have hearlier (i j : ℕ) (hij : i < j) : f i ∈ history j := by
    induction j with
    | zero => omega
    | succ j ih =>
      change f i ∈ f j :: history j
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hij) with hlt | rfl
      · exact List.mem_cons_of_mem _ (ih hlt)
      · exact List.mem_cons_self
  have hne (i j : ℕ) (hij : i < j) : f i ≠ f j := by
    intro heq
    apply (hchosen (j, history j)).2
    change f j ∈ history j
    rw [← heq]
    exact hearlier i j hij
  refine ⟨f, hf, ?_, ?_⟩
  · intro i j heq
    rcases lt_trichotomy i j with hlt | he | hgt
    · exact (hne i j hlt heq).elim
    · exact he
    · exact (hne j i hgt heq.symm).elim
  · intro z
    have hcyl : (∃ x n : ℕ, x ∈ A ∧ z = Nat.pair x n) ↔ z.unpair.1 ∈ A := by
      constructor
      · rintro ⟨x, n, hx, rfl⟩
        simpa only [Nat.unpair_pair] using hx
      · intro hx
        exact ⟨z.unpair.1, z.unpair.2, hx, (Nat.pair_unpair z).symm⟩
    exact hcyl.trans (hhom _ _ (hchosen (z, history z)).1).symm
