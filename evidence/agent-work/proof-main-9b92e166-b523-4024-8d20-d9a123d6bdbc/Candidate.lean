import Proofs.ManyOneReducibilityOnNat
import Proofs.ComputablyEnumerableSet
import Proofs.FiniteMarkerAvoidance
import Proofs.CofiniteDomainLemma
import Proofs.PriorityRequirements
import Proofs.HaltingSigmaOneCompleteness
import Proofs.ProfileRealization
import Proofs.PullbackReductions
import Proofs.HomogeneousRowsFromCylinderReduction
import Proofs.AscendingSelfReductionFromPullbackReduction
import Proofs.CylinderGreatestFiniteOneDegree
import Proofs.ReducibilityImplications

theorem MaslovaCeDichotomy : (let encode (n : _root_.Nat) := _root_.List.replicate n _root_.Bool.false
let decode (w : _root_.List _root_.Bool) :=
  if w = encode (_root_.List.length w) then _root_.Option.some (_root_.List.length w)
  else _root_.Option.none
let ce : _root_.Set _root_.Nat → Prop :=
  _root_.ComputablyEnumerableSet encode decode
    (_root_.List.replicate_left_injective _root_.Bool.false)
    (fun n => by simp [decode, encode])
    (fun w hw => _root_.ite_eq_right (fun h => hw ⟨_root_.List.length w, h.symm⟩))
let finiteOneReducible (X Y : _root_.Set _root_.Nat) : Prop :=
  ∃ f : _root_.Nat → _root_.Nat, _root_.Computable f ∧
    (∀ y : _root_.Nat, _root_.Set.Finite (_root_.Set.preimage f ({y} : _root_.Set _root_.Nat))) ∧
    (∀ x : _root_.Nat, x ∈ X ↔ f x ∈ Y)
let finiteOneDegree (X : _root_.Set _root_.Nat) : _root_.Set (_root_.Set _root_.Nat) :=
  {Y | finiteOneReducible Y X ∧ finiteOneReducible X Y}
∀ A : _root_.Set _root_.Nat,
  let d : _root_.Set (_root_.Set _root_.Nat) :=
    {X | _root_.ManyOneReducibilityOnNat X A ∧ _root_.ManyOneReducibilityOnNat A X}
  (¬ ∃ X ∈ d, _root_.ComputablePred (fun n : _root_.Nat => n ∈ X)) →
  (∃ X ∈ d, ce X) →
  let finiteOneDegrees := _root_.Set.image finiteOneDegree d
  _root_.ExistsUnique (fun D => D ∈ finiteOneDegrees) ∨ _root_.Set.Infinite finiteOneDegrees) :=
by
  classical
  intro encode decode ce finiteOneReducible finiteOneDegree B d hnonrec hce finiteOneDegrees
  let degree := ReducibilityImplications.finiteOneDegree
  let reducible := ReducibilityImplications.FiniteOneReducible
  have degreeEq {X Y : Set Nat} :
      degree X = degree Y ↔ reducible X Y ∧ reducible Y X :=
    ReducibilityImplications.finiteOneDegree_eq_iff
  have compose {X Y Z : Set Nat} (hXY : reducible X Y) (hYZ : reducible Y Z) :
      reducible X Z := ReducibilityImplications.finiteOneTrans hXY hYZ
  have memDegree (X : Set Nat) : X ∈ d ↔ ManyOneDegree.of X = ManyOneDegree.of B :=
    ManyOneDegree.of_eq_of.symm
  let cylinder (X : Set Nat) : Set Nat := {z | ∃ x n, x ∈ X ∧ z = Nat.pair x n}
  let top := degree (cylinder B)
  have hTop : top ∈ finiteOneDegrees :=
    ⟨cylinder B, (memDegree _).mpr (CylinderGreatestFiniteOneDegree B).1, rfl⟩
  by_cases hfinite : finiteOneDegrees.Finite
  swap
  · exact Or.inr hfinite
  left
  refine ⟨top, hTop, ?_⟩
  intro E hE
  by_contra hEne

  -- Cintioli, §5, p. 13, quotes the c.e. case from Maslova [2] in the
  -- formulation of Richter–Stephan–Zhang, arXiv:2607.06218, p. 17.
  -- Neither cited passage contains the proof and the 1979 original was
  -- unavailable. We use the maximal-class argument of Corollary 7 with
  -- the restricted-marker variant of the §4 construction.
  -- https://arxiv.org/pdf/2609.00419v1#page=13
  -- https://arxiv.org/pdf/2607.06218#page=17
  -- The article-specific Research Portal and defect report returned HTTP 404.
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects
  -- Alphabeta Math's many-one interface, Step 1.1, checks composition of
  -- witnesses. For finite-one degrees transport between representatives
  -- using finite-one composition, which additionally preserves finite fibres.
  -- https://alphabetamath.cc/item/def-computable-many-one-reducibility-interface
  let below (D F : Set (Set Nat)) : Prop :=
    D = F ∨ ∃ X Y : Set Nat, degree X = D ∧ degree Y = F ∧ reducible X Y
  have below_iff (X Y : Set Nat) : below (degree X) (degree Y) ↔ reducible X Y := by
    constructor
    · rintro (heq | ⟨U, V, hUX, hVY, hUV⟩)
      · exact (degreeEq.mp heq).1
      · exact compose (degreeEq.mp hUX).2 (compose hUV (degreeEq.mp hVY).1)
    · exact fun h => Or.inr ⟨X, Y, rfl, rfl, h⟩
  let degreeOrder : LE (Set (Set Nat)) := ⟨below⟩
  have hTrans : IsTrans (Set (Set Nat)) below := ⟨by
    intro D F G hDF hFG
    rcases hDF with rfl | ⟨X, Y, rfl, rfl, hXY⟩
    · exact hFG
    rcases hFG with heq | ⟨U, V, hUY, rfl, hUV⟩
    · exact Or.inr ⟨X, Y, rfl, heq, hXY⟩
    · exact Or.inr ⟨X, V, rfl, rfl,
        compose hXY (compose (degreeEq.mp hUY).2 hUV)⟩⟩
  let proper := finiteOneDegrees \ {top}
  have hproper : proper.Finite := hfinite.sdiff
  have hproperNE : proper.Nonempty := ⟨E, hE, by simpa using hEne⟩
  obtain ⟨D, hDmax⟩ :=
    @Set.Finite.exists_maximal _ degreeOrder hTrans proper hproper hproperNE
  obtain ⟨A, hAd, rfl⟩ := hDmax.1.1
  have hAne : degree A ≠ top := by simpa using hDmax.1.2
  have hAnrec : ¬ ComputablePred (fun x : Nat => x ∈ A) :=
    fun h => hnonrec ⟨A, hAd, h⟩
  have hACylIn : cylinder A ∈ d :=
    (memDegree _).mpr ((CylinderGreatestFiniteOneDegree A).1.trans ((memDegree _).mp hAd))
  have hCylTop : degree (cylinder A) = top := by
    apply degreeEq.mpr
    exact ⟨(CylinderGreatestFiniteOneDegree B).2 _ ((memDegree _).mp hACylIn),
      (CylinderGreatestFiniteOneDegree A).2 _
        ((CylinderGreatestFiniteOneDegree B).1.trans ((memDegree _).mp hAd).symm)⟩
  have hAnCyl :
      ¬ (OneOneReducible (fun x : Nat => x ∈ A) (fun x : Nat => x ∈ cylinder A) ∧
        OneOneReducible (fun x : Nat => x ∈ cylinder A) (fun x : Nat => x ∈ A)) := by
    rintro ⟨h₁, h₂⟩
    exact hAne ((degreeEq.mpr ⟨(ReducibilityImplications A (cylinder A)).1 h₁,
      (ReducibilityImplications (cylinder A) A).1 h₂⟩).trans hCylTop)

  -- Recognizability equivalence, Step 3.1, is supplied for the actual
  -- false-bit encoding. Precomposition transports semidecision along the
  -- ordinary many-one reduction. Post's theorem, Step 1.1, rules out the
  -- opposite semidecision since this representative is nonrecursive.
  -- https://alphabetamath.cc/item/thm-recognizable-iff-enumerable
  -- https://alphabetamath.cc/item/thm-posts-theorem
  obtain ⟨Q, hQd, hQce⟩ := hce
  have hQre : REPred (fun x : Nat => x ∈ Q) :=
    (ComputablyEnumerableSet.nat_rePred_iff false Q).mpr hQce
  obtain ⟨f, hf, hfmem⟩ := (ManyOneDegree.of_eq_of.mp
    (((memDegree A).mp hAd).trans ((memDegree Q).mp hQd).symm)).1
  have hAre : REPred (fun x : Nat => x ∈ A) :=
    REPred.of_eq (p := fun x => f x ∈ Q) (Partrec.comp hQre hf) fun x => (hfmem x).symm
  have hAcNre : ¬ REPred (fun x : Nat => x ∈ Aᶜ) :=
    fun h => hAnrec (ComputablePred.computable_iff_re_compl_re'.mpr ⟨hAre, h⟩)

  -- Cintioli’s local interpolation theorem (§4, Theorem 5) requires
  -- both A and Aᶜ to be non-c.e., so it does not apply to this A. The
  -- generalized compiled trace restricts lower markers to Aᶜ. One
  -- halting-oracle query to the code that semidecides A decides admissibility.
  let φ := HaltingSigmaOneCompleteness.canonicalNumbering
  let V := HaltingSigmaOneCompleteness.row
  let stage := HaltingSigmaOneCompleteness.rowAt
  have hφacc : AcceptableNumbering φ := HaltingSigmaOneCompleteness.canonicalNumbering_acceptable
  have hφ : Partrec₂ φ := hφacc.2.2.1
  let K := PriorityRequirements.haltingOracle φ
  let oracle (n : Nat) : Part Nat := Part.some (@ite Nat (n ∈ K) (Classical.propDecidable _) 1 0)
  obtain ⟨code, hcode⟩ := (ComputablyEnumerableSet.nat_rePred_iff_exists_code A).mp hAre
  let index := Encodable.encode code
  have hQuery (x : Nat) : Nat.pair index x ∈ K ↔ x ∈ A := by
    rw [PriorityRequirements.pair_mem_haltingOracle]
    change ((Denumerable.ofNat Nat.Partrec.Code (Encodable.encode code)).eval x).Dom ↔ x ∈ A
    rw [Denumerable.ofNat_encode]
    exact hcode x
  have hInput : Computable (fun x => Nat.pair index x) :=
    Primrec₂.natPair.to_comp.comp (Computable.const index) Computable.id
  have hCall : Nat.RecursiveIn ({oracle} : Set (Nat →. Nat)) oracle :=
    Nat.RecursiveIn.oracle oracle (Set.mem_singleton _)
  have hSwap : Computable (fun b : Nat => 1 - b) :=
    Primrec.nat_sub.to_comp.comp (Computable.const 1) Computable.id
  have hM : Nat.RecursiveIn ({oracle} : Set (Nat →. Nat))
      (fun x => Part.some (@ite Nat (x ∈ Aᶜ) (Classical.propDecidable _) 1 0)) := by
    refine ((RecursiveIn.iff_nat.mp hSwap.computableIn).comp
      (hCall.comp (RecursiveIn.iff_nat.mp hInput.computableIn))).of_eq fun x => ?_
    by_cases hx : x ∈ A
    · simp [oracle, Set.mem_compl_iff, hx, (hQuery x).mpr hx]
    · simp [oracle, Set.mem_compl_iff, hx, (hQuery x).not.mpr hx]
  let before (q r : Nat × Nat) : Prop := Nat.pair q.1 q.2 < Nat.pair r.1 r.2
  have hOrder : IsStrictTotalOrder (Nat × Nat) before :=
    Nat.pairEquiv.injective.isStrictTotalOrder_onFun (· < ·)
  have hPairCode : Primrec (fun q : Nat × Nat => Nat.pair q.1 q.2) :=
    Primrec₂.natPair.comp Primrec.fst Primrec.snd
  have hBefore : ComputablePred (fun p : (Nat × Nat) × (Nat × Nat) => before p.1 p.2) :=
    (Primrec.nat_lt.comp (hPairCode.comp Primrec.fst) (hPairCode.comp Primrec.snd)).computablePred
  obtain ⟨T, _, hSigma⟩ := PriorityRequirements.existsEffectiveTrace φ stage Aᶜ before
    hφ hφacc.2.1 HaltingSigmaOneCompleteness.computable_rowAt_code hOrder hBefore hM
  let N := T.output
  let P : Set Nat := Nᶜ
  -- Post's theorem, Steps 2.1 and 3.1. The supplier gives the transcript
  -- certificate for this trace, and the unary presentation commutes with
  -- complement. Both requirements below use the trace producing that certificate.
  -- https://alphabetamath.cc/item/thm-posts-theorem
  have hPi : {xs : Fin 1 → Nat | xs 0 ∈ P} ∈
      (ArithmeticalHierarchyLevels 2 1 (Nat.le_succ 1)).2.1 := by
    change ({xs : Fin 1 → Nat | xs 0 ∈ N}ᶜᶜ : Set (Fin 1 → Nat)) ∈
      (ArithmeticalHierarchyLevels 2 1 (Nat.le_succ 1)).1
    simpa using hSigma

  have hVre : REPred (fun q : Nat × Nat × Nat => q.2.2 ∈ V q.1 q.2.1) :=
    (hφ.comp Computable.fst (hPairCode.to_comp.comp Computable.snd)).dom_re
  have upper (e : Nat) (homogeneous : ∀ x y, y ∈ V e x → (y ∈ A ↔ x ∈ A)) :
      ∃ x, (V e x).Finite ∧ V e x ⊆ N := by
    apply T.upper_met V HaltingSigmaOneCompleteness.monotone_rowAt
      HaltingSigmaOneCompleteness.mem_row_iff_exists_stage e
    intro Z hZ hZM
    -- Lemma 2's restricted form requires non-enumerability only for
    -- colours represented among these restraints. Every marker is in Aᶜ.
    -- Recognizability equivalence, Steps 1.2, 2.1 and 3.1, supplies the
    -- true-bit c.e. graph from the canonical row-domain semidecision.
    -- https://alphabetamath.cc/item/thm-recognizable-iff-enumerable
    refine FiniteMarkerAvoidance.of_nonCE_marker_colors A (V e) hAnCyl
      ((ComputablyEnumerableSet.nat_rePred_iff true _).mp
        (PriorityRequirements.rowGraphRE hVre e)) homogeneous Z hZ ?_
    intro z hz
    exact ⟨fun hzA => (hZM hz hzA).elim, fun _ hceAc =>
      hAcNre ((ComputablyEnumerableSet.nat_rePred_iff true Aᶜ).mpr hceAc)⟩

  have hAinf : A.Infinite := by
    intro hAfin
    have hmem : PrimrecRel (fun (xs : List Nat) (x : Nat) => x ∈ xs) :=
      (PrimrecRel.exists_mem_list (R := @Eq Nat) Primrec.eq).of_eq (by
        intro xs x
        simp)
    exact hAnrec
      (((hmem.decide.to_comp.comp (Computable.const hAfin.toFinset.toList)
        Computable.id).computablePred).of_eq
          (fun x => Finset.mem_toList.trans hAfin.mem_toFinset))
  obtain ⟨enumerate, hEnumerate, hRange⟩ :=
    ComputablyEnumerableSet.nat_exists_computable_range hAre hAinf.nonempty
  -- Lemma 4 gives unbounded omissions in Nat. To force them into Aᶜ,
  -- race the given self-reduction with a partial map defined exactly on A.
  -- Wait for recognition of x, then search the total enumeration for a
  -- larger member. This is Step 1.1 of recognizability equivalence with
  -- the computable test x < enumerate n in place of equality.
  -- https://alphabetamath.cc/item/thm-recognizable-iff-enumerable
  let pass (x n : Nat) : Part Bool := Part.some (decide (x < enumerate n))
  have hPass : Partrec₂ pass :=
    (Primrec.nat_lt.decide.to_comp.comp Computable.fst
      (hEnumerate.comp Computable.snd)).partrec
  let search (x : Nat) : Part Nat := Part.map enumerate (Nat.rfind (pass x))
  have hSearch : Partrec search :=
    (Partrec.rfind hPass).map (hEnumerate.comp Computable.snd)
  let advance (x : Nat) : Part Nat :=
    (Part.assert (x ∈ A) (fun _ => Part.some ())).bind (fun _ => search x)
  have hAdvance : Partrec advance := Partrec.bind hAre (hSearch.comp Computable.fst)
  have hAdvanceDom (x : Nat) : (advance x).Dom ↔ x ∈ A := by
    rw [Part.dom_iff_mem]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨u, hu, _⟩ := Part.mem_bind_iff.mp hy
      obtain ⟨hx, _⟩ := Part.mem_assert_iff.mp hu
      exact hx
    · intro hx
      obtain ⟨y, hyA, hxy⟩ := hAinf.exists_gt x
      rw [← hRange] at hyA
      obtain ⟨n, rfl⟩ := hyA
      have hFound : (Nat.rfind (pass x)).Dom := (Nat.rfind_dom' (p := pass x)).mpr
        ⟨n, by simp [pass, hxy], fun _ => by simp [pass]⟩
      obtain ⟨k, hk⟩ := Part.dom_iff_mem.mp hFound
      refine ⟨enumerate k, Part.mem_bind_iff.mpr ⟨(), ?_, ?_⟩⟩
      · simp [hx]
      · exact (Part.mem_map_iff _).mpr ⟨k, hk, rfl⟩
  have hAdvanceAsc (x y : Nat) (hy : y ∈ advance x) : x < y ∧ (y ∈ A ↔ x ∈ A) := by
    obtain ⟨u, hu, hySearch⟩ := Part.mem_bind_iff.mp hy
    obtain ⟨hx, _⟩ := Part.mem_assert_iff.mp hu
    obtain ⟨k, hk, rfl⟩ := (Part.mem_map_iff enumerate).mp hySearch
    have hLt : x < enumerate k := by simpa [pass] using Nat.rfind_spec hk
    exact ⟨hLt, iff_of_true (hRange ▸ Set.mem_range_self k) hx⟩
  have lower (e : Nat) (ascending : ∀ x y, y ∈ φ e x → x < y ∧ (y ∈ A ↔ x ∈ A)) :
      ∃ m, m ∈ P ∧ ¬ (φ e m).Dom := by
    obtain ⟨race, hRace, hRaceDom, hRaceVal⟩ :=
      CofiniteDomainLemma.partrec_union (hφacc.1 e) hAdvance
    have hRaceAsc (x y : Nat) (hy : y ∈ race x) : x < y ∧ (y ∈ A ↔ x ∈ A) :=
      (hRaceVal x y hy).elim (ascending x y) (hAdvanceAsc x y)
    have hMissing := CofiniteDomainLemma A race hAnrec hAnCyl hRace hRaceAsc
    obtain ⟨m, _, hmN, hmDom⟩ := T.lower_met e fun b => by
      obtain ⟨m, hm, hb⟩ := hMissing.exists_gt b
      change ¬ (race m).Dom at hm
      rw [hRaceDom, hAdvanceDom] at hm
      exact ⟨m, hb, fun h => hm (Or.inr h), fun h => hm (Or.inl h)⟩
    exact ⟨m, hmN, hmDom⟩

  -- Cintioli, Lemma 1 and the proof of Theorem 5, pp. 11–12. Realize
  -- the Π₂ set as the infinite-fibre profile and use the computable section
  -- for the forward reduction to the pullback.
  -- https://arxiv.org/pdf/2609.00419v1#page=11
  obtain ⟨p, hp, hpSurj, hProfile, s, hs, hSection⟩ := ProfileRealization P hPi
  let C := Set.preimage p A
  have hsExists : ∃ s : Nat → Nat, Computable s ∧ Function.RightInverse s p :=
    ⟨s, hs, hSection⟩
  obtain ⟨_, hAC, _, hCdeg⟩ := PullbackReductions A P p s hp hpSurj hProfile hs hSection
  have hCd : C ∈ d := (memDegree C).mpr (hCdeg.trans ((memDegree A).mp hAd))
  have hCnotA : ¬ reducible C A := by
    rintro ⟨h, hh, hFib, hMem⟩
    obtain ⟨hPartial, hAsc, hDom⟩ :=
      AscendingSelfReductionFromPullbackReduction A P p h hp hpSurj hsExists hProfile hh hFib hMem
    obtain ⟨e, he⟩ := hφacc.2.1 _ hPartial
    obtain ⟨m, hmP, hmDom⟩ := lower e (by simpa only [he] using hAsc)
    exact hmDom (by rw [he]; exact hDom hmP)
  have hCnotTop : ¬ reducible (cylinder A) C := by
    rintro ⟨h, hh, hFib, hMem⟩
    -- Exhaust the whole row family at one canonical index. The row
    -- supplier uses true bits and its graph packs (x,y) with Nat.pair.
    obtain ⟨_, ⟨e, he⟩, hHom⟩ :=
      HomogeneousRowsFromCylinderReduction A P p hp hpSurj hsExists hProfile h hh hFib hMem
        stage HaltingSigmaOneCompleteness.computable_rowAt_code
        HaltingSigmaOneCompleteness.monotone_rowAt (by
          intro W hW
          obtain ⟨e, he⟩ := HaltingSigmaOneCompleteness.exists_index_stages
            ((ComputablyEnumerableSet.nat_rePred_iff true _).mpr hW)
          refine ⟨e, fun x => Set.ext fun y => ?_⟩
          refine Iff.trans ?_ (he x y)
          constructor
          · exact fun hy => ⟨x, y, hy, rfl⟩
          · rintro ⟨u, v, hv, huv⟩
            obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp huv
            exact hv)
    have hRows (x : Nat) : Set.range (fun n => p (h (Nat.pair x n))) = V e x :=
      (he x).trans (Set.ext fun y => (HaltingSigmaOneCompleteness.mem_row_iff_exists_stage e x y).symm)
    obtain ⟨x, hxFin, hxSub⟩ := upper e fun u y hy =>
      hHom u y (by
        change y ∈ Set.range (fun n => p (h (Nat.pair u n)))
        rwa [hRows u])
    have hpFib : ∀ y ∈ V e x, (Set.preimage p ({y} : Set Nat)).Finite := by
      intro y hy
      by_contra hInf
      have hyP : y ∈ P := by
        rw [← hProfile]
        exact hInf
      exact hyP (hxSub hy)
    -- Pull the selected finite row back along each finite-fibre map over
    -- that row. The resulting finite set would contain the whole x-column.
    have hImageFinite : (Set.preimage h (Set.preimage p (V e x))).Finite :=
      (hxFin.preimage' hpFib).preimage' (fun y _ => hFib y)
    have hColumnInf : (Set.range (Nat.pair x)).Infinite :=
      Set.infinite_range_of_injective (fun _ _ hEq => (Nat.pair_eq_pair.mp hEq).2)
    apply hImageFinite.not_infinite
    apply hColumnInf.mono
    rintro _ ⟨n, rfl⟩
    change p (h (Nat.pair x n)) ∈ V e x
    rw [← hRows x]
    exact Set.mem_range_self n
  have hCneTop : degree C ≠ top := fun heq =>
    hCnotTop (degreeEq.mp (hCylTop.trans heq.symm)).1
  have hCproper : degree C ∈ proper := ⟨⟨C, hCd, rfl⟩, by simpa using hCneTop⟩
  exact hCnotA ((below_iff C A).mp (hDmax.2 hCproper ((below_iff A C).mpr hAC)))

#print axioms MaslovaCeDichotomy
