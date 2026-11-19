by
  classical
  -- Cintioli, arXiv:2609.00419v1, §5, Corollary 7, pp. 13–14.
  -- https://arxiv.org/pdf/2609.00419v1#page=13
  -- The article-specific Alphabeta Math portal and defect report returned
  -- HTTP 404. The numbered steps cited below are from the shared library.
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects
  intro finiteOneReducible finiteOneDegree d
  induction d using ManyOneDegree.ind_on with
  | h B =>
    intro representatives hNonrecursive finiteOneDegrees
    have hDichotomy :
        (∃! D, D ∈ finiteOneDegrees) ∨ finiteOneDegrees.Infinite := by
      -- The article splits on the representative of the maximal proper
      -- class. The two compiled dichotomies take witnesses anywhere in
      -- the fibre, so we split before constructing a maximal class.
      by_cases hCe : ∃ X ∈ representatives, REPred (fun n : Nat => n ∈ X)
      · let maslovaRepresentatives : Set (Set Nat) :=
          {X | ManyOneReducibilityOnNat X B ∧ ManyOneReducibilityOnNat B X}
        have hMem (X : Set Nat) : X ∈ maslovaRepresentatives ↔ X ∈ representatives :=
          ManyOneDegree.of_eq_of.symm
        have hFibre : maslovaRepresentatives = representatives := Set.ext hMem
        obtain ⟨X, hXB, hX⟩ := hCe
        -- Recognizability equivalence, Steps 1.2, 2.1 and 3.1, gives a
        -- range presentation with a separate empty case. The Nat bridge
        -- supplies the false-bit word encoding expected by Maslova.
        -- https://alphabetamath.cc/item/thm-recognizable-iff-enumerable
        have hMaslova := MaslovaCeDichotomy B
          (fun ⟨Y, hYB, hY⟩ => hNonrecursive ⟨Y, (hMem Y).mp hYB, hY⟩)
          ⟨X, (hMem X).mpr hXB, (ComputablyEnumerableSet.nat_rePred_iff false X).mp hX⟩
        change (∃! D, D ∈ Set.image finiteOneDegree maslovaRepresentatives) ∨
          (Set.image finiteOneDegree maslovaRepresentatives).Infinite at hMaslova
        rw [hFibre] at hMaslova
        exact hMaslova
      by_cases hCoCe : ∃ X ∈ representatives, REPred (fun n : Nat => n ∈ Xᶜ)
      · -- The compiled complementation dichotomy transfers the two
        -- alternatives along the equivalence of degree fibres.
        exact ComplementCeDichotomy (ManyOneDegree.of B) hNonrecursive hCoCe
      by_cases hFinite : finiteOneDegrees.Finite
      swap
      · exact Or.inr hFinite
      left
      let cylinder (X : Set Nat) : Set Nat := {z | ∃ x n, x ∈ X ∧ z = Nat.pair x n}
      let top := finiteOneDegree (cylinder B)
      have hTop : top ∈ finiteOneDegrees :=
        ⟨cylinder B, (CylinderGreatestFiniteOneDegree B).1, rfl⟩
      refine ⟨top, hTop, ?_⟩
      intro E hE
      by_contra hEne

      -- Alphabeta Math's many-one interface, verification Step 1.1,
      -- composes total Nat reductions and the membership equivalences.
      -- The finite-one composition supplier also checks the finite
      -- fibres. Transport across equal classes uses mutual reductions.
      -- https://alphabetamath.cc/item/def-computable-many-one-reducibility-interface
      have classEq {X Y : Set Nat} :
          finiteOneDegree X = finiteOneDegree Y ↔
            finiteOneReducible X Y ∧ finiteOneReducible Y X :=
        ReducibilityImplications.finiteOneDegree_eq_iff
      have compose {X Y Z : Set Nat} (hXY : finiteOneReducible X Y)
          (hYZ : finiteOneReducible Y Z) : finiteOneReducible X Z :=
        ReducibilityImplications.finiteOneTrans hXY hYZ
      let below (D F : Set (Set Nat)) : Prop :=
        ∃ X Y : Set Nat, finiteOneDegree X = D ∧ finiteOneDegree Y = F ∧
          finiteOneReducible X Y
      have below_iff (X Y : Set Nat) :
          below (finiteOneDegree X) (finiteOneDegree Y) ↔ finiteOneReducible X Y := by
        constructor
        · rintro ⟨U, V, hUX, hVY, hUV⟩
          exact compose (classEq.mp hUX).2 (compose hUV (classEq.mp hVY).1)
        · exact fun h => ⟨X, Y, rfl, rfl, h⟩
      let degreeOrder : LE (Set (Set Nat)) := ⟨below⟩
      have hTrans : IsTrans (Set (Set Nat)) below := ⟨by
        rintro D F G ⟨X, Y, hXD, hYF, hXY⟩ ⟨U, V, hUF, hVG, hUV⟩
        exact ⟨X, V, hXD, hVG, compose hXY
          (compose (classEq.mp (hYF.trans hUF.symm)).1 hUV)⟩⟩
      -- Corollary 7's class covered by the greatest class comes from
      -- maximality in the finite nonempty set with the cylinder removed.
      let proper := finiteOneDegrees \ {top}
      have hProperFinite : proper.Finite := hFinite.sdiff
      have hProperNonempty : proper.Nonempty := ⟨E, hE, by simpa using hEne⟩
      obtain ⟨D, hDmax⟩ :=
        @Set.Finite.exists_maximal _ degreeOrder hTrans proper hProperFinite hProperNonempty
      obtain ⟨A, hA, rfl⟩ := hDmax.1.1
      have hAne : finiteOneDegree A ≠ top := by simpa using hDmax.1.2
      have hAnrec : ¬ ComputablePred (fun n : Nat => n ∈ A) :=
        fun h => hNonrecursive ⟨A, hA, h⟩

      -- The cylinder theorem places both cylinders in the same many-one
      -- fibre and supplies each direction of finite-one reducibility.
      have hAB : ManyOneDegree.of A = ManyOneDegree.of B := hA
      have hCylTop : finiteOneDegree (cylinder A) = top := classEq.mpr
        ⟨(CylinderGreatestFiniteOneDegree B).2 _
            ((CylinderGreatestFiniteOneDegree A).1.trans hAB),
          (CylinderGreatestFiniteOneDegree A).2 _
            ((CylinderGreatestFiniteOneDegree B).1.trans hAB.symm)⟩
      have hAnCyl :
          ¬ (OneOneReducible (fun n : Nat => n ∈ A) (fun n : Nat => n ∈ cylinder A) ∧
            OneOneReducible (fun n : Nat => n ∈ cylinder A) (fun n : Nat => n ∈ A)) := by
        rintro ⟨hTo, hFrom⟩
        exact hAne ((classEq.mpr
          ⟨(ReducibilityImplications A (cylinder A)).1 hTo,
            (ReducibilityImplications (cylinder A) A).1 hFrom⟩).trans hCylTop)

      -- The reverse direction of the encoding bridge implements
      -- recognizability Step 1.1, including the empty case. Theorem 5
      -- uses the true-bit encoding for both colours.
      -- https://alphabetamath.cc/item/thm-recognizable-iff-enumerable
      obtain ⟨C, hCA, ⟨hAC, hNotCA⟩, ⟨_, hNotCylC⟩⟩ :=
        LocalInterpolation A hAnrec hAnCyl
          (fun h => hCe ⟨A, hA, (ComputablyEnumerableSet.nat_rePred_iff true A).mpr h⟩)
          (fun h => hCoCe ⟨A, hA, (ComputablyEnumerableSet.nat_rePred_iff true Aᶜ).mpr h⟩)
      have hCmem : finiteOneDegree C ∈ finiteOneDegrees := ⟨C, hCA.trans hAB, rfl⟩
      have hCne : finiteOneDegree C ≠ top :=
        fun h => hNotCylC (classEq.mp (h.trans hCylTop.symm)).2
      have hCproper : finiteOneDegree C ∈ proper := ⟨hCmem, by simpa using hCne⟩
      exact hNotCA ((below_iff C A).mp
        (hDmax.2 hCproper ((below_iff A C).mpr hAC)))

    -- The endpoint also states the finite-cardinality exclusion explicitly.
    refine ⟨hDichotomy, ?_⟩
    rintro ⟨hFinite, D, hD, E, hE, hDE⟩
    rcases hDichotomy with ⟨T, _, hUnique⟩ | hInfinite
    · exact hDE ((hUnique D hD).trans (hUnique E hE).symm)
    · exact hInfinite hFinite
