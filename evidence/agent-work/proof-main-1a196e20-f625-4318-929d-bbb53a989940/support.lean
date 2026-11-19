/-- Cintioli, arXiv:2609.00419v1, §3, Lemma 2, pp. 4–6.
Only the colour classes represented among the finite markers need be non-c.e. -/
theorem FiniteMarkerAvoidance.of_nonCE_marker_colors
    (A : Set ℕ) (V : ℕ → Set ℕ) :
    let cyl : Set ℕ := {z | ∃ x n : ℕ, x ∈ A ∧ z = Nat.pair x n}
    let encode : ℕ → List Bool := fun n => List.replicate n true
    let decode : List Bool → Option ℕ := fun w =>
      if encode w.length = w then some w.length else none
    let ce : Set ℕ → Prop :=
      ComputablyEnumerableSet encode decode
        (Function.LeftInverse.injective
          (show Function.LeftInverse List.length encode from fun _ => List.length_replicate))
        (by intro n; simp [decode, encode])
        (fun w hw => ite_eq_right (fun h => hw ⟨w.length, h⟩))
    ¬ (OneOneReducible (fun x => x ∈ A) (fun x => x ∈ cyl) ∧
        OneOneReducible (fun x => x ∈ cyl) (fun x => x ∈ A)) →
    ce {z | ∃ x y : ℕ, y ∈ V x ∧ z = Nat.pair x y} →
    (∀ x y : ℕ, y ∈ V x → (y ∈ A ↔ x ∈ A)) →
    ∀ Z : Set ℕ, Z.Finite →
      (∀ z ∈ Z, (z ∈ A → ¬ ce A) ∧ (z ∉ A → ¬ ce (Aᶜ))) →
      ∃ x : ℕ, (V x).Finite ∧ V x ∩ Z = ∅ := by
  classical
  intro cyl encode decode ce hnotCyl hV hhom Z hZ hcolors
  by_contra hno
  have hinfinite (x : ℕ) (havoid : V x ∩ Z = ∅) : (V x).Infinite :=
    fun hfin => hno ⟨x, hfin, havoid⟩
  have hforward : OneOneReducible (fun x => x ∈ A) (fun x => x ∈ cyl) := by
    refine ⟨fun x => Nat.pair x 0,
      Primrec₂.natPair.to_comp.comp Computable.id (Computable.const 0), ?_, ?_⟩
    · intro x y h
      exact (Nat.pair_eq_pair.mp h).1
    · intro x
      constructor
      · intro hx
        exact ⟨x, 0, hx, rfl⟩
      · rintro ⟨y, n, hy, hp⟩
        exact (Nat.pair_eq_pair.mp hp).1.symm ▸ hy

  -- Lemma 2, pp. 4–5: the reviewed supplier provides the greedy
  -- injection for the exact true-bit c.e. row graph, homogeneity and
  -- infinitude. Its search follows the freshness and termination arguments
  -- in steps 1.1, 2.1 and 3.1 of the Alphabeta Math item
  -- https://alphabetamath.cc/item/thm-infinite-ce-sets-have-computable-injective-enumerations.
  -- The supplier searches a different row at each input and tracks all
  -- earlier outputs. Empty restraints use the original rows directly.
  by_cases hempty : Z = ∅
  · exact hnotCyl ⟨hforward, InfiniteHomogeneousRows A V hV hhom
      (fun x => hinfinite x (by simp [hempty]))⟩

  -- The article-specific Alphabeta Math portal and defect-report routes
  -- returned HTTP 404. For computability, use the shared item
  -- https://alphabetamath.cc/item/thm-recognizable-iff-enumerable.
  -- Steps 1.1 and 3.1 inspire the range-to-domain bridge below. Its
  -- identity word encoding is replaced by the supplier's true-bit unary
  -- Nat encoding. As in step 2.1, pair candidate data with bounded fuel.
  -- The local nat_rePred_iff_exists_code supplier gives a domain code.
  -- Use evaln to certify individual memberships in place of the article's
  -- simultaneous finite stage approximations.
  let graph (W : ℕ → Set ℕ) : Set ℕ :=
    {z | ∃ x y : ℕ, y ∈ W x ∧ z = Nat.pair x y}
  have hpair (W : ℕ → Set ℕ) (n : ℕ) :
      n ∈ graph W ↔ n.unpair.2 ∈ W n.unpair.1 := by
    constructor
    · rintro ⟨x, y, hy, rfl⟩
      simpa using hy
    · intro hy
      exact ⟨n.unpair.1, n.unpair.2, hy, (Nat.pair_unpair n).symm⟩
  have hbridge (S : Set ℕ) : REPred (fun n => n ∈ S) ↔ ce S :=
    ComputablyEnumerableSet.nat_rePred_iff true S
  obtain ⟨code, hcode⟩ :=
    (ComputablyEnumerableSet.nat_rePred_iff_exists_code (graph V)).mp ((hbridge _).mpr hV)
  let bounded (t x y : ℕ) : Bool := (code.evaln t (Nat.pair x y)).isSome
  have hbounded {t x y : ℕ × ℕ → ℕ} (ht : Primrec t) (hx : Primrec x) (hy : Primrec y) :
      Primrec (fun p => bounded (t p) (x p) (y p)) :=
    Primrec.option_isSome.comp
      (Nat.Partrec.Code.primrec_evaln.comp
        ((ht.pair (Primrec.const code)).pair (Primrec₂.natPair.comp hx hy)))
  have hstage (x y : ℕ) : y ∈ V x ↔ ∃ t, bounded t x y := by
    have hxy : Nat.pair x y ∈ graph V ↔ y ∈ V x := by
      simpa using hpair V (Nat.pair x y)
    rw [← hxy, ← hcode, Part.dom_iff_mem]
    constructor
    · rintro ⟨out, hout⟩
      obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp hout
      exact ⟨t, Option.isSome_iff_exists.mpr ⟨out, ht⟩⟩
    · rintro ⟨t, ht⟩
      obtain ⟨out, hout⟩ := Option.isSome_iff_exists.mp ht
      exact ⟨out, Nat.Partrec.Code.evaln_complete.mpr ⟨t, hout⟩⟩
  -- Minimization on a total test uses the same terminating individual
  -- tests as step 1.1, now with fuel code and markers in the witness.
  have hsearch {test : ℕ × ℕ → Bool} (htest : Primrec test) :
      REPred (fun x => ∃ k, test (x, k)) := by
    have hrec : Partrec (fun x : ℕ => Nat.rfind (fun k => Part.some (test (x, k)))) :=
      Partrec.rfind htest.to_comp.partrec
    refine hrec.dom_re.of_eq fun x => ?_
    exact (Nat.rfind_dom (p := fun k => Part.some (test (x, k)))).trans (by simp)

  have listMem {α : Type} [Primcodable α] :
      PrimrecRel (fun (xs : List α) (y : α) => y ∈ xs) :=
    (PrimrecRel.exists_mem_list (R := @Eq α) Primrec.eq).of_eq (by intro xs y; simp)
  let L := hZ.toFinset.toList
  have hL (z : ℕ) : z ∈ L ↔ z ∈ Z := by simp [L]
  let Avoid (x : ℕ) : Prop := V x ∩ Z = ∅
  by_cases hgood : ∀ z ∈ Z, ∃ d, Avoid d ∧ (d ∈ A ↔ z ∈ A)
  · -- Lemma 2, pp. 5–6: hardcode one avoiding row of the same colour
    -- for each marker. Choice supplies the constants; the recognizer
    -- only reads the resulting finite table.
    have hchoose (z : ℕ) : ∃ d, z ∈ Z → Avoid d ∧ (d ∈ A ↔ z ∈ A) := by
      by_cases hz : z ∈ Z
      · obtain ⟨d, hd⟩ := hgood z hz
        exact ⟨d, fun _ => hd⟩
      · exact ⟨0, fun h => (hz h).elim⟩
    choose d hd using hchoose
    let table := L.map (fun z => (z, d z))
    have htable (z r : ℕ) : (z, r) ∈ table ↔ z ∈ Z ∧ r = d z := by
      simp [table, hL, eq_comm]
    let W (x : ℕ) : Set ℕ := {u | u ∈ V x ∨ ∃ z ∈ Z, z ∈ V x ∧ u ∈ V (d z)}
    have hW : ce (graph W) := by
      apply (hbridge _).mp
      -- Direct membership searches one fuel. Added membership searches
      -- a table entry (marker, row) and two independent successful fuels.
      let test (p : ℕ × ℕ) : Bool :=
        bounded p.2 p.1.unpair.1 p.1.unpair.2 ||
          (decide (p.2.unpair.1.unpair ∈ table) &&
            bounded p.2.unpair.2.unpair.1 p.1.unpair.1 p.2.unpair.1.unpair.1 &&
            bounded p.2.unpair.2.unpair.2 p.2.unpair.1.unpair.2 p.1.unpair.2)
      have hinput := Primrec.unpair.comp (Primrec.fst : Primrec (Prod.fst : ℕ × ℕ → ℕ))
      have hwitness := Primrec.unpair.comp (Primrec.snd : Primrec (Prod.snd : ℕ × ℕ → ℕ))
      have hentry := Primrec.unpair.comp (Primrec.fst.comp hwitness)
      have hfuel := Primrec.unpair.comp (Primrec.snd.comp hwitness)
      have hrow := Primrec.fst.comp hinput
      have hvalue := Primrec.snd.comp hinput
      have htest : Primrec test :=
        Primrec.or.comp (hbounded Primrec.snd hrow hvalue)
          (Primrec.and.comp
            (Primrec.and.comp (listMem.decide.comp (Primrec.const table) hentry)
              (hbounded (Primrec.fst.comp hfuel) hrow (Primrec.fst.comp hentry)))
            (hbounded (Primrec.snd.comp hfuel) (Primrec.snd.comp hentry) hvalue))
      refine (hsearch htest).of_eq fun n => ?_
      rw [hpair]
      constructor
      · rintro ⟨k, hk⟩
        simp only [test, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hk
        rcases hk with h | ⟨⟨hentry, ht₁⟩, ht₂⟩
        · exact Or.inl ((hstage _ _).mpr ⟨k, h⟩)
        · obtain ⟨hz, hr⟩ := (htable k.unpair.1.unpair.1 k.unpair.1.unpair.2).mp hentry
          exact Or.inr ⟨_, hz, (hstage _ _).mpr ⟨_, ht₁⟩,
            hr ▸ (hstage _ _).mpr ⟨_, ht₂⟩⟩
      · intro hu
        change _ ∨ _ at hu
        rcases hu with hu | ⟨z, hz, hzx, hu⟩
        · obtain ⟨t, ht⟩ := (hstage _ _).mp hu
          exact ⟨t, by simp [test, ht]⟩
        · obtain ⟨t₁, ht₁⟩ := (hstage _ _).mp hzx
          obtain ⟨t₂, ht₂⟩ := (hstage _ _).mp hu
          exact ⟨Nat.pair (Nat.pair z (d z)) (Nat.pair t₁ t₂),
            by simp [test, htable, hz, ht₁, ht₂]⟩
    have hWhom (x u : ℕ) (hu : u ∈ W x) : u ∈ A ↔ x ∈ A := by
      rcases hu with hu | ⟨z, hz, hzx, hu⟩
      · exact hhom x u hu
      · exact (hhom (d z) u hu).trans ((hd z hz).2.trans (hhom x z hzx))
    have hWinf (x : ℕ) : (W x).Infinite := by
      by_cases ha : Avoid x
      · exact (hinfinite x ha).mono (fun _ hu => Or.inl hu)
      · obtain ⟨z, hzx, hz⟩ := Set.nonempty_iff_ne_empty.mpr ha
        exact (hinfinite (d z) (hd z hz).1).mono (fun _ hu => Or.inr ⟨z, hz, hzx, hu⟩)
    exact hnotCyl ⟨hforward, InfiniteHomogeneousRows A W hW hWhom hWinf⟩

  · -- Lemma 2, p. 6: a marker with no avoiding row of the same colour
    -- witnesses an entire colour class covered by its same-colour sections.
    obtain ⟨z, hz, hcover⟩ : ∃ z ∈ Z, ∀ x, Avoid x → ¬ (x ∈ A ↔ z ∈ A) := by
      simpa only [not_forall, not_exists, not_and, exists_prop] using hgood
    let markers := L.filter (fun w => decide (w ∈ A ↔ z ∈ A))
    have hmarkers (w : ℕ) : w ∈ markers ↔ w ∈ Z ∧ (w ∈ A ↔ z ∈ A) := by
      simp [markers, hL]
    let test (p : ℕ × ℕ) : Bool :=
      decide (p.2.unpair.1 ∈ markers) && bounded p.2.unpair.2 p.1 p.2.unpair.1
    have hwitness := Primrec.unpair.comp (Primrec.snd : Primrec (Prod.snd : ℕ × ℕ → ℕ))
    have hmarker := Primrec.fst.comp hwitness
    have htest : Primrec test :=
      Primrec.and.comp (listMem.decide.comp (Primrec.const markers) hmarker)
        (hbounded (Primrec.snd.comp hwitness) Primrec.fst hmarker)
    let color : Set ℕ := {x | x ∈ A ↔ z ∈ A}
    have hceColor : ce color := by
      apply (hbridge _).mp
      refine (hsearch htest).of_eq fun x => ?_
      constructor
      · rintro ⟨k, hk⟩
        simp only [test, Bool.and_eq_true, decide_eq_true_eq] at hk
        have hw := (hstage _ _).mpr ⟨_, hk.2⟩
        exact (hhom x _ hw).symm.trans ((hmarkers _).mp hk.1).2
      · intro hx
        have hhit : ¬ Avoid x := fun ha => hcover x ha hx
        obtain ⟨w, hwx, hwZ⟩ := Set.nonempty_iff_ne_empty.mpr hhit
        have hw := (hmarkers w).mpr ⟨hwZ, (hhom x w hwx).trans hx⟩
        obtain ⟨t, ht⟩ := (hstage _ _).mp hwx
        exact ⟨Nat.pair w t, by simp [test, hw, ht]⟩
    by_cases hzA : z ∈ A
    · have hEq : color = A := Set.ext (fun x => by simp [color, hzA])
      exact (hcolors z hz).1 hzA (hEq ▸ hceColor)
    · have hEq : color = Aᶜ := Set.ext (fun x => by simp [color, hzA])
      exact (hcolors z hz).2 hzA (hEq ▸ hceColor)
