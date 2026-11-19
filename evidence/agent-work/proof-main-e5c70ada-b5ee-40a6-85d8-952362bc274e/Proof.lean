by
  intro X N hX hN
  -- The supplier's Program, step and haltsWith unfold to the reviewed tape
  -- semantics, including undelimited input and acceptance specifically at 1.
  change ∃ (s b : Nat) (p : OracleNegativePullback.Program s b), ∀ n,
    OracleNegativePullback.haltsWith X p n (fun q _ => q = 1) ↔ n ∈ N at hN
  obtain ⟨s, b, p, hp⟩ := hN
  obtain ⟨code, hcode⟩ := (ComputablyEnumerableSet.nat_rePred_iff_exists_code X).mp hX
  -- Cintioli, arXiv:2609.00419v1, p. 10, uses “Since N is c.e. in 0′, we
  -- have N ∈ Σ⁰₂.” This bridge supplies that implication with an arbitrary
  -- c.e. oracle. Post's theorem, Alphabeta Math step 2.1, supplies the
  -- existential transcript and positive witnesses. One universally quantified
  -- fuel tests all the negative answers because each edge is checked at every
  -- fuel. The hierarchy matrix reads the packed transcript and fuel as its
  -- two bound coordinates. Primrec.fin_app reads those coordinates directly
  -- because the hierarchy already supplies the Fin 1 and Fin 2 tuples.
  -- The article-specific Research Portal and defect report returned HTTP 404.
  -- The numbered proof steps above come from the verified Shared Math Library
  -- sources in the support comments.
  change ∃ R : (Fin 1 → Nat) → (Fin 2 → Nat) → Prop,
    PrimrecRel R ∧ ∀ xs, xs 0 ∈ N ↔
      ∃ witness, ∀ u, R xs (Fin.cons witness (Fin.cons u Fin.elim0))
  refine ⟨fun xs ys => CETapeSigmaTwo.check p code (xs 0) (ys 0) (ys 1) = true, ?_, ?_⟩
  · have hfree : Primrec (fun a : (Fin 1 → Nat) × (Fin 2 → Nat) => a.1 0) :=
      Primrec.fin_app.comp Primrec.fst (Primrec.const 0)
    have hwitness : Primrec (fun a : (Fin 1 → Nat) × (Fin 2 → Nat) => a.2 0) :=
      Primrec.fin_app.comp Primrec.snd (Primrec.const 0)
    have hfuel : Primrec (fun a : (Fin 1 → Nat) × (Fin 2 → Nat) => a.2 1) :=
      Primrec.fin_app.comp Primrec.snd (Primrec.const 1)
    exact Primrec.eq.comp
      ((CETapeSigmaTwo.primCheck p code).comp (hfree.pair (hwitness.pair hfuel)))
      (Primrec.const true)
  · intro xs
    change xs 0 ∈ N ↔ ∃ witness, ∀ u, CETapeSigmaTwo.check p code (xs 0) witness u = true
    exact (hp (xs 0)).symm.trans (CETapeSigmaTwo.check_correct (p := p) hcode (xs 0))
