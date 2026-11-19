by
  intro A P p hp _ _ _ C cyl h hh _ hReduction encode decode uniformlyCE stage _ _ indexedRows hIndex V
  -- Cintioli's proof of Theorem 5, §4, p. 11, fixes p and h before
  -- forming the rows. Lemma 1 (ProfileRealization) supplies p in the caller.
  -- Here p and its profile are hypotheses. The row argument uses the
  -- computability of p and h and the reduction's membership equivalence.
  -- https://arxiv.org/pdf/2609.00419v1#page=11
  -- The article passage is unnumbered. The corresponding Research Portal
  -- collection and defect report returned HTTP 404.
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects
  let pack (q : Nat × Nat) : Nat := Nat.pair q.1 (p (h (Nat.pair q.1 q.2)))
  let enumerate (k : Nat) : Nat := pack k.unpair
  let G : Set Nat := {z | ∃ x y, y ∈ V x ∧ z = Nat.pair x y}
  have hPair : Computable (fun q : Nat × Nat => Nat.pair q.1 q.2) :=
    Primrec₂.natPair.to_comp
  have hPack : Computable pack :=
    Primrec₂.natPair.to_comp.comp Computable.fst (hp.comp (hh.comp hPair))
  have hEnumerate : Computable enumerate :=
    hPack.comp Primrec.unpair.to_comp
  have hRange : Set.range enumerate = G := by
    ext z
    change (∃ k, enumerate k = z) ↔ ∃ x y, y ∈ V x ∧ z = Nat.pair x y
    constructor
    · rintro ⟨k, rfl⟩
      let q := k.unpair
      exact ⟨q.1, p (h (Nat.pair q.1 q.2)), ⟨q.2, rfl⟩, rfl⟩
    · rintro ⟨x, y, ⟨n, rfl⟩, rfl⟩
      have hUnpair : (Nat.pair x n).unpair = (x, n) :=
        Nat.pairEquiv.symm_apply_apply (x, n)
      exact ⟨Nat.pair x n, by simp only [enumerate, pack, hUnpair]⟩

  -- Alphabeta Math's recognizability equivalence, step 1.1, searches
  -- a total enumeration for equality with the input. The reviewed supplier
  -- implements this search on Nat. Step 2.1 uses shortlex words and a
  -- time bound. The supplier's Nat bridge searches coded inputs and fuel
  -- and expresses the result with the reviewed true-bit unary encoding.
  -- https://alphabetamath.cc/item/thm-recognizable-iff-enumerable
  have hRecognizer : REPred (fun z => z ∈ G) := by
    rw [← hRange]
    exact ComputablyEnumerableSet.nat_rePred_range hEnumerate
  have hCE : uniformlyCE V :=
    (ComputablyEnumerableSet.nat_rePred_iff true G).mp hRecognizer

  -- The assumed exhaustion of the stage enumeration applies to the whole
  -- coded graph, so the same index represents every row.
  refine ⟨hCE, hIndex V hCE, ?_⟩
  have hCylinder (x n : Nat) : Nat.pair x n ∈ cyl ↔ x ∈ A := by
    change (∃ u v : Nat, u ∈ A ∧ Nat.pair x n = Nat.pair u v) ↔ x ∈ A
    constructor
    · rintro ⟨u, v, hu, hEq⟩
      have huv : (x, n) = (u, v) := Nat.pairEquiv.injective hEq
      have hFirst : x = u := congrArg Prod.fst huv
      exact hFirst.symm ▸ hu
    · exact fun hx => ⟨x, n, hx, rfl⟩
  rintro x y ⟨n, rfl⟩
  exact (hReduction (Nat.pair x n)).symm.trans (hCylinder x n)
