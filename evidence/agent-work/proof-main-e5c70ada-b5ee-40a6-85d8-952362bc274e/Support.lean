namespace CETapeSigmaTwo

open OracleNegativePullback (Program Cfg numeral readNumeral halting write step haltsWith)
open Nat.Partrec (Code)

variable {s b : Nat}

/- Alphabeta Math's Post's theorem, step 2.1, uses the finite transcript
   of a halting jump-oracle computation. The same argument applies to any
   c.e. oracle by taking a code for its semidecider. Each transcript entry
   records a reviewed configuration and its positive-query fuel witness.
   See https://alphabetamath.cc/item/thm-posts-theorem and
   https://alphabetamath.cc/item/lem-oracle-computation-has-a-finite-query-witness
   (steps 1.1 and 2.1). -/

private theorem primNumeral (b : Nat) : Primrec (numeral b) := by
  exact (Primrec.list_map OracleNegativePullback.prim_bits
    ((Primrec.dom_finite (OracleNegativePullback.letterCode (b := b))).comp Primrec.snd).to₂).of_eq
    (OracleNegativePullback.numeral_code b)

-- The supplier's read_output theorem certifies a prepared output at cell
-- zero. Queries start at the current head and may be malformed. Prove
-- primitive recursiveness of the reviewed parser on every tape suffix
-- using the delimiter test, numeral reconstruction and full word equality.
private theorem primRead (b : Nat) : Primrec₂ (readNumeral b) := by
  let tail (p : List (Fin (b + 4)) × Nat) := p.1.drop p.2
  let word (p : List (Fin (b + 4)) × Nat) := (tail p).takeWhile (· != 3)
  let value (p : List (Fin (b + 4)) × Nat) :=
    (word p).foldl (fun acc digit => 2 * acc + digit.val) 0
  have ht : Primrec tail := Primrec.list_drop.comp Primrec.snd Primrec.fst
  have hw : Primrec word :=
    (Primrec.list_takeWhile (Primrec.dom_finite (fun d : Fin (b + 4) => d != 3))).comp ht
  have hfold : Primrec (fun p : Nat × Fin (b + 4) => 2 * p.1 + p.2.val) :=
    Primrec.nat_add.comp (Primrec.nat_double.comp Primrec.fst)
      (Primrec.fin_val.comp Primrec.snd)
  have hv : Primrec value :=
    Primrec.list_foldl hw (Primrec.const 0) (hfold.comp Primrec.snd).to₂
  have hd := Primrec.eq.comp
    ((Primrec.list_getD (2 : Fin (b + 4))).comp ht (Primrec.list_length.comp hw))
    (Primrec.const (3 : Fin (b + 4)))
  exact Primrec.ite (hd.and (Primrec.eq.comp hw ((primNumeral b).comp hv)))
    (Primrec.option_some.comp hv) (Primrec.const none)

private theorem primReplicate {α : Type} [Primcodable α] (a : α) :
    Primrec (fun n : Nat => List.replicate n a) := by
  have hstep : Primrec₂ (fun (_ : Nat) (xs : List α) => a :: xs) :=
    (Primrec.list_cons.comp (Primrec.const a) Primrec.snd).to₂
  refine (Primrec.nat_rec₁ [] hstep).of_eq ?_
  intro n
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (List.cons a) ih

private def ordinaryNext (c : Cfg s b) (action : Fin (s + 3) × Fin (b + 4) × Bool) :
    Cfg s b :=
  (action.1, if action.2.2 then c.2.1 + 1 else c.2.1 - 1,
    write 2 c.2.2 c.2.1 action.2.1)

private theorem primOrdinaryNext :
    Primrec₂ (ordinaryNext (s := s) (b := b)) := by
  let head : Cfg s b × (Fin (s + 3) × Fin (b + 4) × Bool) → Nat := fun a => a.1.2.1
  let tape : Cfg s b × (Fin (s + 3) × Fin (b + 4) × Bool) → List (Fin (b + 4)) :=
    fun a => a.1.2.2
  have hh : Primrec head := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ht : Primrec tape := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hr : Primrec (fun a : Cfg s b × (Fin (s + 3) × Fin (b + 4) × Bool) => a.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hsym : Primrec (fun a : Cfg s b × (Fin (s + 3) × Fin (b + 4) × Bool) => a.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hlen := Primrec.nat_sub.comp (Primrec.succ.comp hh) (Primrec.list_length.comp ht)
  have hpadded := Primrec.list_append.comp ht ((primReplicate (2 : Fin (b + 4))).comp hlen)
  simpa only [Primrec₂, ordinaryNext, write, Bool.cond_eq_ite] using
    (Primrec.fst.comp Primrec.snd).pair
    ((Primrec.cond hr (Primrec.succ.comp hh) (Primrec.nat_sub.comp hh (Primrec.const 1))).pair
      (Primrec.list_set.comp hpadded (hh.pair hsym)))

private def answers (code : Code) (fuel query : Nat) : Bool :=
  (Code.evaln fuel code query).isSome

private theorem primAnswers (code : Code) : Primrec₂ (answers code) :=
  Primrec.option_isSome.comp (Code.primrec_evaln.comp
    ((Primrec.fst.pair (Primrec.const code)).pair Primrec.snd))

private theorem mem_iff_answers {X : Set Nat} {code : Code}
    (hc : ∀ q, (code.eval q).Dom ↔ q ∈ X) (q : Nat) :
    q ∈ X ↔ ∃ fuel, answers code fuel q = true := by
  rw [← hc, Part.dom_iff_mem]
  constructor
  · rintro ⟨out, hout⟩
    obtain ⟨fuel, hfuel⟩ := Code.evaln_complete.mp hout
    exact ⟨fuel, Option.isSome_iff_exists.mpr ⟨out, hfuel⟩⟩
  · rintro ⟨fuel, hfuel⟩
    obtain ⟨out, hout⟩ := Option.isSome_iff_exists.mp hfuel
    exact ⟨out, Code.evaln_sound hout⟩

private abbrev Outcome (s b : Nat) := Cfg s b ⊕ (Nat × Fin (s + 3) × Fin (s + 3))

private def inspect (p : Program s b) (c : Cfg s b) : Outcome s b :=
  Sum.casesOn (p c.1)
    (fun ordinary => .inl (ordinaryNext c (ordinary (c.2.2.getD c.2.1 2))))
    (fun branches => Option.casesOn (readNumeral b c.2.2 c.2.1)
      (.inl (branches.2, c.2)) (fun q => .inr (q, branches)))

private theorem primInspect (p : Program s b) : Primrec (inspect p) := by
  let Ordinary := Fin (b + 4) → Fin (s + 3) × Fin (b + 4) × Bool
  let Query := Fin (s + 3) × Fin (s + 3)
  have ordinary : Primrec₂ (fun (c : Cfg s b) (f : Ordinary) =>
      (Sum.inl (ordinaryNext c (f (c.2.2.getD c.2.1 2))) : Outcome s b)) := by
    have hread : Primrec (fun c : Cfg s b => c.2.2.getD c.2.1 2) :=
      (Primrec.list_getD (2 : Fin (b + 4))).comp (Primrec.snd.comp Primrec.snd)
        (Primrec.fst.comp Primrec.snd)
    exact (Primrec.sumInl.comp
      (primOrdinaryNext.comp Primrec.fst (Primrec.fin_app.comp Primrec.snd
        (hread.comp Primrec.fst)))).to₂
  have query : Primrec₂ (fun (c : Cfg s b) (branches : Query) =>
      (Option.casesOn (readNumeral b c.2.2 c.2.1)
        (.inl (branches.2, c.2)) (fun q => .inr (q, branches)) : Outcome s b)) := by
    have hread : Primrec (fun a : Cfg s b × Query =>
        readNumeral b a.1.2.2 a.1.2.1) :=
      (primRead b).comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    exact (Primrec.option_casesOn hread
      (Primrec.sumInl.comp ((Primrec.snd.comp Primrec.snd).pair
        (Primrec.snd.comp Primrec.fst)))
      (Primrec.sumInr.comp (Primrec.snd.pair
        (Primrec.snd.comp Primrec.fst))).to₂).to₂
  exact Primrec.sumCasesOn ((Primrec.dom_finite p).comp Primrec.fst) ordinary query

private abbrev Entry (s b : Nat) := Cfg s b × Nat

/-- A positive query needs the ticket supplied with the source configuration.
A negative query must pass the test at the universally quantified fuel. -/
private def edge (p : Program s b) (code : Code) (u : Nat) (entry : Entry s b)
    (target : Cfg s b) : Bool :=
  let (c, ticket) := entry
  !halting s c.1 && Sum.casesOn (inspect p c)
    (fun next => decide (target = next))
    (fun branches =>
      bif answers code ticket branches.1 then decide (target = (branches.2.1, c.2))
      else !answers code u branches.1 && decide (target = (branches.2.2, c.2)))

private theorem primEdge (p : Program s b) (code : Code) :
    Primrec (fun a : Nat × Entry s b × Cfg s b => edge p code a.1 a.2.1 a.2.2) := by
  let Input := Nat × Entry s b × Cfg s b
  let source (a : Input) := a.2.1.1
  let ticket (a : Input) := a.2.1.2
  let target (a : Input) := a.2.2
  have hs : Primrec source := Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have ht : Primrec ticket := Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hd : Primrec target := Primrec.snd.comp Primrec.snd
  have ordinary : Primrec₂ (fun (a : Input) (next : Cfg s b) =>
      decide (target a = next)) :=
    (Primrec.eq.comp (hd.comp Primrec.fst) Primrec.snd).decide.to₂
  have query : Primrec₂ (fun (a : Input) (branches : Nat × Fin (s + 3) × Fin (s + 3)) =>
      bif answers code (ticket a) branches.1 then
        decide (target a = (branches.2.1, (source a).2))
      else !answers code a.1 branches.1 &&
        decide (target a = (branches.2.2, (source a).2))) := by
    have hq : Primrec (fun z : Input × (Nat × Fin (s + 3) × Fin (s + 3)) => z.2.1) :=
      Primrec.fst.comp Primrec.snd
    have hyes := (primAnswers code).comp (ht.comp Primrec.fst) hq
    have hno := Primrec.not.comp ((primAnswers code).comp (Primrec.fst.comp Primrec.fst) hq)
    have hstate : Primrec (fun z : Input × (Nat × Fin (s + 3) × Fin (s + 3)) => z.2.2) :=
      Primrec.snd.comp Primrec.snd
    have hrest : Primrec (fun z : Input × (Nat × Fin (s + 3) × Fin (s + 3)) => (source z.1).2) :=
      Primrec.snd.comp (hs.comp Primrec.fst)
    have hyesTarget : Primrec (fun z : Input × (Nat × Fin (s + 3) × Fin (s + 3)) =>
        decide (target z.1 = (z.2.2.1, (source z.1).2))) :=
      (Primrec.eq.comp (hd.comp Primrec.fst) ((Primrec.fst.comp hstate).pair hrest)).decide
    have hnoTarget : Primrec (fun z : Input × (Nat × Fin (s + 3) × Fin (s + 3)) =>
        decide (target z.1 = (z.2.2.2, (source z.1).2))) :=
      (Primrec.eq.comp (hd.comp Primrec.fst) ((Primrec.snd.comp hstate).pair hrest)).decide
    exact (Primrec.cond hyes hyesTarget (Primrec.and.comp hno hnoTarget)).to₂
  have hhalt := Primrec.not.comp ((Primrec.dom_finite (halting s)).comp
    (Primrec.fst.comp hs))
  exact Primrec.and.comp hhalt
    (Primrec.sumCasesOn ((primInspect p).comp hs) ordinary query)

private theorem edge_correct {X : Set Nat} {p : Program s b} {code : Code}
    (hc : ∀ q, (code.eval q).Dom ↔ q ∈ X) (c target : Cfg s b) :
    step X p c target ↔ ∃ ticket, ∀ u, edge p code u (c, ticket) target = true := by
  rcases c with ⟨state, head, tape⟩
  cases hp : p state with
  | inl ordinary =>
    rcases ordinary (tape.getD head 2) with ⟨next, letter, right⟩
    simp [step, edge, inspect, ordinaryNext, hp]
  | inr branches =>
    rcases branches with ⟨yes, no⟩
    cases hr : readNumeral b tape head with
    | none => simp [step, edge, inspect, hp, hr]
    | some q =>
      have hq := mem_iff_answers hc q
      simp only [step, edge, inspect, hp, hr,
        Bool.and_eq_true, Bool.not_eq_true']
      constructor
      · rintro ⟨hguard, (⟨hmem, htarget⟩ | ⟨hmem, htarget⟩)⟩
        · obtain ⟨ticket, ht⟩ := hq.mp hmem
          exact ⟨ticket, fun u => by simp [hguard, ht, htarget]⟩
        · have hn (u : Nat) : answers code u q = false :=
            Bool.eq_false_of_not_eq_true (fun h => hmem (hq.mpr ⟨u, h⟩))
          exact ⟨0, fun u => by simp [hguard, hn, htarget]⟩
      · rintro ⟨ticket, ht⟩
        by_cases hpos : answers code ticket q = true
        · have h := ht 0
          simp [hpos] at h
          exact ⟨h.1, Or.inl ⟨hq.mpr ⟨ticket, hpos⟩, h.2⟩⟩
        · have hn := Bool.eq_false_of_not_eq_true hpos
          have h (u : Nat) := ht u
          simp [hn] at h
          exact ⟨(h 0).1, Or.inr ⟨fun hmem => by
            obtain ⟨u, hu⟩ := hq.mp hmem
            simp [(h u).2.1] at hu, (h 0).2.2⟩⟩

private def foldTrace (p : Program s b) (code : Code) (u : Nat) (last : Cfg s b)
    (entries : List (Entry s b)) : Bool × Cfg s b :=
  entries.foldr (fun entry acc => (edge p code u entry acc.2 && acc.1, entry.1))
    (true, last)

private theorem primFoldTrace (p : Program s b) (code : Code) :
    Primrec (fun a : Nat × Cfg s b × List (Entry s b) => foldTrace p code a.1 a.2.1 a.2.2) := by
  let Input := Nat × Cfg s b × List (Entry s b)
  have stepCheck : Primrec₂ (fun (a : Input) (z : Entry s b × (Bool × Cfg s b)) =>
      (edge p code a.1 z.1 z.2.2 && z.2.1, z.1.1)) := by
    have he : Primrec (fun z : Input × (Entry s b × (Bool × Cfg s b)) =>
        edge p code z.1.1 z.2.1 z.2.2.2) :=
      (primEdge p code).comp ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    exact ((Primrec.and.comp he (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).pair
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))).to₂
  exact Primrec.list_foldr (Primrec.snd.comp Primrec.snd)
    ((Primrec.const true).pair (Primrec.fst.comp Primrec.snd)) stepCheck

private def firstCfg (last : Cfg s b) : List (Entry s b) → Cfg s b
  | [] => last
  | entry :: _ => entry.1

private theorem foldTrace_first (p : Program s b) (code : Code) (u : Nat) (last : Cfg s b)
    (entries : List (Entry s b)) :
    (foldTrace p code u last entries).2 = firstCfg last entries := by
  cases entries <;> rfl

private theorem foldTrace_cons (p : Program s b) (code : Code) (u : Nat) (last : Cfg s b)
    (entry : Entry s b) (entries : List (Entry s b)) :
    (foldTrace p code u last (entry :: entries)).1 =
      (edge p code u entry (firstCfg last entries) && (foldTrace p code u last entries).1) := by
  change (edge p code u entry (foldTrace p code u last entries).2 &&
    (foldTrace p code u last entries).1) = _
  rw [foldTrace_first]

-- Head induction on the reviewed closure builds the configuration chain
-- and attaches each edge's witness in the same induction. The reverse
-- induction recovers a reviewed edge from each universally tested entry.
private theorem trace_correct {X : Set Nat} {p : Program s b} {code : Code}
    (hc : ∀ q, (code.eval q).Dom ↔ q ∈ X) (first last : Cfg s b) :
    Relation.ReflTransGen (step X p) first last ↔
      ∃ entries, firstCfg last entries = first ∧
        ∀ u, (foldTrace p code u last entries).1 = true := by
  constructor
  · intro run
    induction run using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨[], rfl, fun _ => rfl⟩
    | @head c next hstep _ ih =>
      obtain ⟨entries, hfirst, htail⟩ := ih
      obtain ⟨ticket, hedge⟩ := (edge_correct hc c next).mp hstep
      refine ⟨(c, ticket) :: entries, rfl, fun u => ?_⟩
      simp only [foldTrace_cons, hfirst, hedge u, htail u, Bool.and_self]
  · rintro ⟨entries, rfl, hall⟩
    induction entries with
    | nil => exact .refl
    | cons entry entries ih =>
      have h (u : Nat) := hall u
      simp only [foldTrace_cons, Bool.and_eq_true] at h
      exact Relation.ReflTransGen.head
        ((edge_correct hc entry.1 _).mpr ⟨entry.2, fun u => (h u).1⟩)
        (ih (fun u => (h u).2))

private abbrev Certificate (s b : Nat) := Cfg s b × List (Entry s b)

private def check (p : Program s b) (code : Code) (n witness u : Nat) : Bool :=
  Option.casesOn (Encodable.decode witness : Option (Certificate s b)) false
    (fun cert => decide (cert.1.1 = 1) &&
      decide (foldTrace p code u cert.1 cert.2 = (true, (0, 0, numeral b n))))

private theorem primCheck (p : Program s b) (code : Code) :
    Primrec (fun a : Nat × Nat × Nat => check p code a.1 a.2.1 a.2.2) := by
  let Input := Nat × Nat × Nat
  have hd : Primrec (fun a : Input => Encodable.decode a.2.1 : Input → Option (Certificate s b)) :=
    Primrec.decode.comp (Primrec.fst.comp Primrec.snd)
  have hcheck : Primrec₂ (fun (a : Input) (cert : Certificate s b) =>
      decide (cert.1.1 = 1) &&
      decide (foldTrace p code a.2.2 cert.1 cert.2 = (true, (0, 0, numeral b a.1)))) := by
    have hscan := (primFoldTrace p code).comp
      ((Primrec.snd.comp (Primrec.snd.comp
        (Primrec.fst : Primrec (Prod.fst : Input × Certificate s b → Input)))).pair Primrec.snd)
    have hstart : Primrec (fun a : Input × Certificate s b =>
        (true, (0, 0, numeral b a.1.1)) : Input × Certificate s b → Bool × Cfg s b) :=
      (Primrec.const true).pair ((Primrec.const 0).pair
        ((Primrec.const 0).pair ((primNumeral b).comp (Primrec.fst.comp Primrec.fst))))
    have hstate : Primrec (fun a : Input × Certificate s b => a.2.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
    exact (Primrec.and.comp (Primrec.eq.comp hstate (Primrec.const 1)).decide
      (Primrec.eq.comp hscan hstart).decide).to₂
  exact Primrec.option_casesOn hd (Primrec.const false) hcheck

private theorem check_correct {X : Set Nat} {p : Program s b} {code : Code}
    (hc : ∀ q, (code.eval q).Dom ↔ q ∈ X) (n : Nat) :
    haltsWith X p n (fun q _ => q = 1) ↔ ∃ witness, ∀ u, check p code n witness u = true := by
  constructor
  · rintro ⟨q, head, tape, hrun, _, hstate⟩
    subst q
    obtain ⟨entries, hfirst, hall⟩ := (trace_correct (code := code) hc _ _).mp hrun
    let cert : Certificate s b := ((1, head, tape), entries)
    refine ⟨Encodable.encode cert, fun u => ?_⟩
    have hscan : foldTrace p code u (1, head, tape) entries = (true, (0, 0, numeral b n)) :=
      Prod.ext (hall u) ((foldTrace_first p code u _ _).trans hfirst)
    simp [check, Encodable.encodek, cert, hscan]
  · rintro ⟨witness, hall⟩
    cases hw : (Encodable.decode witness : Option (Certificate s b)) with
    | none =>
      have h := hall 0
      simp [check, hw] at h
    | some cert =>
      rcases cert with ⟨⟨q, head, tape⟩, entries⟩
      have h (u : Nat) := hall u
      simp only [check, hw, Bool.and_eq_true, decide_eq_true_eq] at h
      have hstate := (h 0).1
      have hfirst : firstCfg (q, head, tape) entries = (0, 0, numeral b n) :=
        (foldTrace_first p code 0 _ _).symm.trans (congrArg Prod.snd (h 0).2)
      refine ⟨q, head, tape, (trace_correct hc _ _).mpr ⟨entries, hfirst, ?_⟩, ?_, hstate⟩
      · intro u
        exact congrArg Prod.fst (h u).2
      · simp [halting, hstate]

end CETapeSigmaTwo
