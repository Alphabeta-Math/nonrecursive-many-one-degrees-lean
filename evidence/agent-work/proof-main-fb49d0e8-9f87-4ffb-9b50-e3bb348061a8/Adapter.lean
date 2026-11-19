import Proofs.RelativeComputabilityAndEnumerability
import Supplier

set_option maxHeartbeats 2000000
noncomputable section

namespace OracleNegativePullback
open Relation
open OAI.FiniteAlgebraicEnvelopes.Compiler.Simulator (Machine Command Move)
open OAI.FiniteAlgebraicEnvelopes.MachineRealization

abbrev Letter := Fin 3

def ofChar (c : Char) : Letter := if c = '0' then 0 else 1
def bits (n : Nat) : List Letter := (Nat.toDigits 2 n).map ofChar
def parse (w : List Letter) : Nat := w.foldl (fun a b => 2 * a + b.val) 0
def out (n : Nat) : List Letter := bits n ++ [2]

theorem parse_bits (n : Nat) : parse (bits n) = n := by
  have aux (w : List Char) (a : Nat) (hw : ∀ c ∈ w, c = '0' ∨ c = '1') :
      (w.map ofChar).foldl (fun a (b : Letter) => 2 * a + b.val) a = Nat.ofDigitChars 2 w a := by
    induction w generalizing a with
    | nil => rfl
    | cons c w ih =>
      simp only [List.map_cons, List.foldl_cons, Nat.ofDigitChars_cons]
      rw [ih _ (fun d hd => hw d (List.mem_cons_of_mem _ hd))]
      rcases hw c List.mem_cons_self with rfl | rfl <;> rfl
  have hchars (fuel n : Nat) (acc : List Char) (ha : ∀ c ∈ acc, c = '0' ∨ c = '1') :
      ∀ c ∈ Nat.toDigitsCore 2 fuel n acc, c = '0' ∨ c = '1' := by
    induction fuel generalizing n acc with
    | zero => exact ha
    | succ fuel ih =>
      have hd : (n % 2).digitChar = '0' ∨ (n % 2).digitChar = '1' := by
        have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
        rcases h with h | h <;> simp [h, Nat.digitChar]
      have hc : ∀ c ∈ (n % 2).digitChar :: acc, c = '0' ∨ c = '1' := by
        intro c h
        rcases List.mem_cons.mp h with rfl | h
        · exact hd
        · exact ha c h
      simp only [Nat.toDigitsCore]
      split_ifs
      · exact hc
      · exact ih _ _ hc
  have hw : ∀ c ∈ Nat.toDigits 2 n, c = '0' ∨ c = '1' := hchars (n + 1) n [] (by simp)
  rw [parse, bits, aux _ _ hw]
  exact Nat.ofDigitChars_toDigits (by decide) (by decide)

def bitStep (p : Nat × List Letter) : Nat × List Letter :=
  if p.1 = 0 then p else
    let n := p.1 - 1
    let q := n / 2
    (if q = 0 then 0 else q + 1, (if n % 2 = 0 then 0 else 1) :: p.2)

theorem prim_bitStep : Primrec bitStep := by
  have hm := Primrec.nat_sub.comp (Primrec.fst : Primrec (Prod.fst : Nat × List Letter → Nat))
    (Primrec.const 1)
  have hq := Primrec.nat_div.comp hm (Primrec.const 2)
  have hr := Primrec.nat_mod.comp hm (Primrec.const 2)
  have hbit : Primrec (fun p : Nat × List Letter => if (p.1 - 1) % 2 = 0 then (0 : Letter) else 1) :=
    Primrec.ite (Primrec.eq.comp hr (Primrec.const 0)) (Primrec.const 0) (Primrec.const 1)
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) Primrec.id
    ((Primrec.ite (Primrec.eq.comp hq (Primrec.const 0)) (Primrec.const 0)
      (Primrec.succ.comp hq)).pair (Primrec.list_cons.comp hbit Primrec.snd))

theorem iterate_bitStep_zero (fuel : Nat) (w : List Letter) :
    (bitStep^[fuel]) (0, w) = (0, w) :=
  Function.iterate_fixed (by simp [bitStep]) fuel

theorem iterate_bitStep (fuel n : Nat) (acc : List Char) :
    ((bitStep^[fuel]) (n + 1, acc.map ofChar)).2 = (Nat.toDigitsCore 2 fuel n acc).map ofChar := by
  induction fuel generalizing n acc with
  | zero => rfl
  | succ fuel ih =>
    have hd : ofChar ((n % 2).digitChar) = if n % 2 = 0 then 0 else 1 := by
      have h : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases h with h | h <;> simp [h, ofChar, Nat.digitChar]
    rw [Function.iterate_succ_apply, Nat.toDigitsCore]
    simp only [bitStep, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
    by_cases hq : n / 2 = 0 <;> simp only [hq, ite_true, ite_false]
    · rw [iterate_bitStep_zero]
      simp [hd]
    · simpa [hd] using ih (n / 2) ((n % 2).digitChar :: acc)

theorem prim_bits : Primrec bits := by
  have h : Primrec (fun n : Nat => (bitStep^[n + 1]) (n + 1, [])) :=
    Primrec.nat_iterate (Primrec.succ.comp Primrec.id)
      ((Primrec.succ.comp Primrec.id).pair (Primrec.const []))
      (prim_bitStep.comp Primrec.snd).to₂
  apply (Primrec.snd.comp h).of_eq
  intro n
  exact iterate_bitStep (n + 1) n []

theorem comp_preprocess {f : Nat → Nat} (hf : Computable f) :
    Computable (fun w => out (f (parse w))) := by
  have step : Primrec (fun ab : Nat × Letter => 2 * ab.1 + ab.2.val) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)
      (Primrec.fin_val.comp Primrec.snd)
  have hparse : Primrec parse :=
    Primrec.list_foldl Primrec.id (Primrec.const 0) (step.comp Primrec.snd).to₂
  exact ((Primrec.list_append.comp Primrec.id (Primrec.const [2])).to_comp.comp
    (prim_bits.to_comp.comp (hf.comp hparse.to_comp)))

abbrev Program (s b : Nat) :=
  Fin (s + 3) → Sum (Fin (b + 4) → Fin (s + 3) × Fin (b + 4) × Bool)
    (Fin (s + 3) × Fin (s + 3))

abbrev Cfg (s b : Nat) := Fin (s + 3) × Nat × List (Fin (b + 4))

def numeral (b n : Nat) : List (Fin (b + 4)) :=
  (Nat.toDigits 2 n).map fun d => if d = '0' then 0 else 1

def readNumeral (b : Nat) (tape : List (Fin (b + 4))) (start : Nat) : Option Nat :=
  let tail := List.drop start tape
  let word := List.takeWhile (fun digit => digit != 3) tail
  let n := List.foldl (fun acc digit => 2 * acc + Fin.val digit) 0 word
  if List.getD tail (List.length word) 2 = 3 ∧ word = numeral b n then some n else none

def halting (s : Nat) (q : Fin (s + 3)) : Bool := q == 1 || q == 2

def write {α : Type} (blank : α) (tape : List α) (head : Nat) (symbol : α) : List α :=
  (tape ++ List.replicate (head + 1 - tape.length) blank).set head symbol

def step (X : Set Nat) {s b : Nat} (program : Program s b) (c t : Cfg s b) : Prop :=
  let (q, head, tape) := c
  halting s q = false ∧
    match program q with
    | Sum.inl ordinary =>
      let (next, symbol, right) := ordinary (List.getD tape head 2)
      t = (next, if right then head + 1 else head - 1, write 2 tape head symbol)
    | Sum.inr (yes, no) =>
      match readNumeral b tape head with
      | none => t = (no, head, tape)
      | some n => (n ∈ X ∧ t = (yes, head, tape)) ∨ (n ∉ X ∧ t = (no, head, tape))

theorem step_unique (X : Set Nat) {s b : Nat} (p : Program s b) :
    Relator.RightUnique (step X p) := by
  rintro ⟨q, head, tape⟩ a c ha hc
  rcases ha with ⟨_, ha⟩
  rcases hc with ⟨_, hc⟩
  cases he : p q with
  | inl ordinary =>
    simp only [he] at ha hc
    exact ha.trans hc.symm
  | inr query =>
    rcases query with ⟨yes, no⟩
    cases hr : readNumeral b tape head with
    | none =>
      simp only [he, hr] at ha hc
      exact ha.trans hc.symm
    | some n =>
      simp only [he, hr] at ha hc
      rcases ha with ⟨ha, rfl⟩ | ⟨ha, rfl⟩ <;>
        rcases hc with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
      · rfl
      · exact (hc ha).elim
      · exact (ha hc).elim
      · rfl

theorem halt_unique {X : Set Nat} {s b : Nat} {p : Program s b} {c u v : Cfg s b}
    (hu : ReflTransGen (step X p) c u) (hv : ReflTransGen (step X p) c v)
    (h₁ : halting s u.1 = true) (h₂ : halting s v.1 = true) : u = v := by
  have terminal (a : Cfg s b) (ha : halting s a.1 = true) (z : Cfg s b)
      (h : step X p a z) : False := by
    rcases a with ⟨q, head, tape⟩
    exact Bool.noConfusion (ha.symm.trans h.1)
  rcases hu.total_of_right_unique (step_unique X p) hv with huv | hvu
  · exact ((Relation.reflTransGen_iff_eq (terminal u h₁)).mp huv).symm
  · exact (Relation.reflTransGen_iff_eq (terminal v h₂)).mp hvu

theorem padded_getD {α : Type} (blank : α) (tape : List α) (n i : Nat) :
    (tape ++ List.replicate n blank).getD i blank = tape.getD i blank := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : i < tape.length
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_append_right (Nat.le_of_not_gt h), List.getElem?_eq_none (Nat.le_of_not_gt h)]
    simp only [List.getElem?_replicate]
    split <;> rfl

theorem write_getD {α : Type} (blank : α) (tape : List α) (head i : Nat) (a : α) :
    (write blank tape head a).getD i blank =
      Function.update (fun j => tape.getD j blank) head a i := by
  by_cases h : i = head
  · subst i
    rw [Function.update_self]
    rw [write, List.getD_eq_getElem?_getD, List.getElem?_set_self]
    · rfl
    · simp only [List.length_append,List.length_replicate]; omega
  · rw [Function.update_of_ne h]
    unfold write
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h), ← List.getD_eq_getElem?_getD]
    exact padded_getD _ _ _ _

theorem write_same {α : Type} (blank : α) (tape : List α) (head i : Nat) :
    (write blank tape head (tape.getD head blank)).getD i blank = tape.getD i blank := by
  rw [write_getD, Function.update_eq_self]

section Simulation
variable {Q Γ : Type} [Fintype Q]
abbrev states (Q : Type) [Fintype Q] := Fintype.card (Q × Bool)

def stateCode (qb : Q × Bool) : Fin (states Q + 3) :=
  ⟨(Fintype.equivFin (Q × Bool) qb).val + 3, by
    exact Nat.add_lt_add_right (Fintype.equivFin (Q × Bool) qb).isLt 3⟩

theorem stateCode_injective : Function.Injective (stateCode (Q := Q)) := by
  intro a b h
  apply (Fintype.equivFin (Q × Bool)).injective
  apply Fin.ext
  exact Nat.add_right_cancel (congrArg Fin.val h)

@[simp] theorem stateCode_ne_zero (qb : Q × Bool) : stateCode qb ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  change (Fintype.equivFin (Q × Bool) qb).val + 3 = 0 at hv
  omega

@[simp] theorem stateCode_nonhalting (qb : Q × Bool) : halting (states Q) (stateCode qb) = false := by
  have h1 : stateCode qb ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    change (Fintype.equivFin (Q × Bool) qb).val + 3 = 1 at hv
    omega
  have h2 : stateCode qb ≠ 2 := by
    intro h
    have hv := congrArg Fin.val h
    change (Fintype.equivFin (Q × Bool) qb).val + 3 = 2 at hv
    omega
  simp [halting, h1, h2]

variable (M : Machine Q Γ) (stop : Q) {b : Nat} (blank : Γ) (enc : Γ → Fin (b + 4))
include M in
def program : Program (states Q) b := by
  classical
  letI : Nonempty Q := ⟨M.initial⟩
  letI : Nonempty Γ := ⟨blank⟩
  exact fun q =>
    if q = 0 then .inl (fun a => (stateCode (M.initial, false), a, false)) else
      let (src, back) := Function.invFun stateCode q
      if back then .inl (fun a => (stateCode (src, false), a, false)) else
        if src = stop then .inr (2, 1) else
          .inl fun a =>
            match M.transition src (Function.invFun enc a) with
            | none => (2, a, false)
            | some cmd => (stateCode (cmd.state, decide (cmd.move = Move.stay)), enc cmd.write, decide (cmd.move ≠ Move.left))

@[simp] theorem program_start :
    program M stop blank enc 0 = .inl (fun a => (stateCode (M.initial, false), a, false)) := by
  simp [program]

theorem program_back (q : Q) :
    program M stop blank enc (stateCode (q, true)) =
      .inl (fun a => (stateCode (q, false), a, false)) := by
  letI : Nonempty Q := ⟨M.initial⟩
  simp [program, Function.leftInverse_invFun stateCode_injective (q, true)]

theorem program_query :
    program M stop blank enc (stateCode (stop, false)) = .inr (2, 1) := by
  letI : Nonempty Q := ⟨M.initial⟩
  simp [program, Function.leftInverse_invFun stateCode_injective (stop, false)]

theorem program_run {q : Q} (hq : q ≠ stop) (he : Function.Injective enc) {a : Γ}
    {cmd : Command Q Γ} (hcmd : M.transition q a = some cmd) :
    ∃ instr, program M stop blank enc (stateCode (q, false)) = .inl instr ∧
      instr (enc a) = (stateCode (cmd.state, decide (cmd.move = Move.stay)), enc cmd.write, decide (cmd.move ≠ Move.left)) := by
  classical
  letI : Nonempty Q := ⟨M.initial⟩
  letI : Nonempty Γ := ⟨blank⟩
  simp only [program, stateCode_ne_zero, ite_false,
    Function.leftInverse_invFun stateCode_injective (q, false), hq]
  refine ⟨_, rfl, ?_⟩
  change (match M.transition q (Function.invFun enc (enc a)) with
    | none => (2, enc a, false)
    | some c => (stateCode (c.state, decide (c.move = Move.stay)), enc c.write, decide (c.move ≠ Move.left))) = _
  rw [Function.leftInverse_invFun he a, hcmd]

def simulates (c : OneSided.Cfg Γ Q) (t : Cfg (states Q) b) : Prop :=
  t.1 = stateCode (c.state, false) ∧ t.2.1 = c.pos ∧
    ∀ i, t.2.2.getD i 2 = enc (c.cell i)

theorem simulate_step (X : Set Nat) (he : Function.Injective enc)
    (hstop : ∀ a, M.transition stop a = none)
    {c d : OneSided.Cfg Γ Q} {t : Cfg (states Q) b}
    (ht : simulates enc c t) (hcd : OneSided.step M c = some d) :
    ∃ u, ReflTransGen (step X (program M stop blank enc)) t u ∧ simulates enc d u := by
  rcases c with ⟨q, head, cell⟩
  rcases t with ⟨r, pos, tape⟩
  rcases ht with ⟨hr, hp, ht⟩
  dsimp at hr hp ht
  subst r pos
  cases hc : M.transition q (cell head) with
  | none => simp [OneSided.step, hc] at hcd
  | some cmd =>
    have hq : q ≠ stop := by
      intro h
      subst q
      rw [hstop] at hc
      cases hc
    simp only [OneSided.step, hc, Option.map_some, Option.some.injEq] at hcd
    subst d
    obtain ⟨instr, hi, ha⟩ := program_run M stop blank enc hq he hc
    let tape' := write (2 : Fin (b + 4)) tape head (enc cmd.write)
    have hw (i : Nat) : tape'.getD i 2 = enc (Function.update cell head cmd.write i) := by
      dsimp [tape']
      rw [write_getD]
      by_cases h : i = head
      · subst i
        simp
      · rw [Function.update_of_ne h, Function.update_of_ne h]
        exact ht i
    have hfirst :
        step X (program M stop blank enc) (stateCode (q, false), head, tape)
          (stateCode (cmd.state, decide (cmd.move = Move.stay)),
            if decide (cmd.move ≠ Move.left) then head + 1 else head - 1, tape') := by
      refine ⟨stateCode_nonhalting _, ?_⟩
      rw [hi]
      -- This ordinary transition uses the encoded current tape cell.
      rw [ht head]
      dsimp only
      rw [ha]
    cases move : cmd.move with
    | left =>
      refine ⟨(stateCode (cmd.state, false), head - 1, tape'), .single ?_, ⟨rfl, ?_, hw⟩⟩
      · simpa [move] using hfirst
      · simp [move]
    | right =>
      refine ⟨(stateCode (cmd.state, false), head + 1, tape'), .single ?_, ⟨rfl, ?_, hw⟩⟩
      · simpa [move] using hfirst
      · simp [move]
    | stay =>
      -- A right move followed by a preserving left move implements stay.
      let tape'' := write (2 : Fin (b + 4)) tape' (head + 1) (tape'.getD (head + 1) 2)
      have hb : step X (program M stop blank enc) (stateCode (cmd.state, true), head + 1, tape')
          (stateCode (cmd.state, false), head, tape'') := by
        refine ⟨stateCode_nonhalting _, ?_⟩
        simp [program_back, tape'']
      refine ⟨(stateCode (cmd.state, false), head, tape''), (ReflTransGen.single ?_).tail hb, ⟨rfl, ?_, ?_⟩⟩
      · simpa [move] using hfirst
      · simp [move]
      · intro i
        exact (write_same _ _ _ _).trans (hw i)

theorem simulate_run (X : Set Nat) (he : Function.Injective enc)
    (hstop : ∀ a, M.transition stop a = none)
    {c d : OneSided.Cfg Γ Q} {t : Cfg (states Q) b}
    (ht : simulates enc c t) (hcd : StateTransition.Reaches (OneSided.step M) c d) :
    ∃ u, ReflTransGen (step X (program M stop blank enc)) t u ∧ simulates enc d u := by
  induction hcd with
  | refl => exact ⟨t, .refl, ht⟩
  | tail _ h ih =>
    obtain ⟨u, htu, hu⟩ := ih
    obtain ⟨v, huv, hv⟩ := simulate_step M stop blank enc X he hstop hu h
    exact ⟨v, htu.trans huv, hv⟩
end Simulation

abbrev Work := FoldLiteral.Gamma Letter

def mainLetter (a : Work) := a.pos.2 Turing.PartrecToTM2.K'.main

theorem input_injective : Function.Injective (FoldLiteral.input (S := Letter)) := by
  intro a b h
  have hm := congrArg mainLetter h
  change some (Sum.inr a) = some (Sum.inr b) at hm
  exact Sum.inr.inj (Option.some.inj hm)

theorem input_ne_blank (a : Letter) : FoldLiteral.input a ≠ FoldLiteral.blank := by
  intro h
  have hm := congrArg mainLetter h
  change some (Sum.inr a) = none at hm
  cases hm

variable {b : Nat}

def letterCode (a : Letter) : Fin (b + 4) :=
  if a = 0 then 0 else if a = 1 then 1 else 3

variable (e : Work ≃ Fin b)

def symbolIndex (a : Work) : Nat := by
  classical
  exact if a = FoldLiteral.blank then 2 else
    if a = FoldLiteral.input 0 then 0 else
      if a = FoldLiteral.input 1 then 1 else
        if a = FoldLiteral.input 2 then 3 else (e a).val + 4

def symbolCode (a : Work) : Fin (b + 4) :=
  ⟨symbolIndex e a, by
    unfold symbolIndex
    have h := (e a).isLt
    split_ifs <;> omega⟩

@[simp] theorem symbolCode_blank : symbolCode e FoldLiteral.blank = 2 := by
  apply Fin.ext
  simp [symbolCode, symbolIndex] <;> rw [Nat.mod_eq_of_lt (by omega)]

@[simp] theorem symbolCode_input (a : Letter) : symbolCode e (FoldLiteral.input a) = letterCode a := by
  apply Fin.ext
  simp only [symbolCode, symbolIndex, input_ne_blank, ite_false, input_injective.eq_iff, letterCode]
  fin_cases a <;> simp <;> rw [Nat.mod_eq_of_lt (by omega)]

theorem symbolCode_injective : Function.Injective (symbolCode e) := by
  intro a b h
  have hv := congrArg Fin.val h
  dsimp only [symbolCode, symbolIndex] at hv
  split_ifs at hv <;> first | omega | (subst_vars; rfl) | skip
  apply e.injective
  exact Fin.ext (Nat.add_right_cancel hv)

theorem list_getD_map {α β : Type} (g : α → β) (w : List α) (i : Nat) (a : α) :
    (w.map g).getD i (g a) = g (w.getD i a) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> rfl

theorem stream_getD {α : Type} (w : List α) (blank : α) (i : Nat) :
    Stream'.appendStream' w (Stream'.const blank) i = w.getD i blank := by
  induction w generalizing i with
  | nil => simp [Stream'.appendStream', Stream'.const]
  | cons a w ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem raw_code (w : List Letter) (i : Nat) :
    symbolCode e (FoldLiteral.raw w i) = (w.map letterCode).getD i 2 := by
  rw [FoldLiteral.raw, stream_getD, ← symbolCode_blank e,
    ← list_getD_map (symbolCode e), List.map_map]
  simp [Function.comp_def]

 theorem numeral_code (b n : Nat) : (bits n).map (letterCode (b := b)) = numeral b n := by
  simp only [bits, List.map_map, numeral, Function.comp_def, ofChar]
  congr 1
  funext d
  split <;> rfl

theorem bits_no_delimiter (b n : Nat) : ∀ a ∈ (bits n).map (letterCode (b := b)), a != 3 := by
  rw [numeral_code]
  intro a ha
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp ha
  split <;> rfl

theorem list_prefix_of_getD {α : Type} (tape w : List α) (blank delim : α) (hne : delim ≠ blank)
    (h : ∀ i, tape.getD i blank = (w ++ [delim]).getD i blank) :
    ∃ rest, tape = w ++ delim :: rest := by
  have hh := h w.length
  have hdelim : (w ++ [delim]).getD w.length blank = delim := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]
  rw [hdelim] at hh
  have ht : w.length < tape.length := by
    by_contra! hle
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hle] at hh
    exact hne hh.symm
  have hprefix : tape.take w.length = w := by
    apply List.ext_getElem
    · simp [Nat.min_eq_left (Nat.le_of_lt ht)]
    · intro i hi hw
      have he := h i
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left hw,
        List.getElem?_eq_getElem (Nat.lt_trans hw ht), List.getElem?_eq_getElem hw] at he
      simpa using he
  have ha : tape[w.length] = delim := by
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some] using hh
  exact ⟨tape.drop (w.length + 1), by
    conv_lhs => rw [← List.take_append_drop w.length tape]
    rw [hprefix, List.drop_eq_getElem_cons ht, ha]⟩

theorem read_output (n : Nat) (tape : List (Fin (b + 4)))
    (h : ∀ i, tape.getD i 2 = symbolCode e (FoldLiteral.raw (out n) i)) :
    readNumeral b tape 0 = some n := by
  have hp : ∀ i, tape.getD i 2 = ((bits n).map letterCode ++ [3]).getD i 2 := by
    intro i
    rw [h, raw_code, out, List.map_append]
    rfl
  obtain ⟨rest, rfl⟩ := list_prefix_of_getD tape ((bits n).map letterCode) 2 3 (by intro h; have := congrArg Fin.val h; change 3 = 2 at this; omega) hp
  have hfold : ((bits n).map (letterCode (b := b))).foldl (fun a b => 2 * a + b.val) 0 = n := by
    have aux (w : List Letter) (a : Nat) (hw : ∀ c ∈ w, c = 0 ∨ c = 1) :
        (w.map (letterCode (b := b))).foldl (fun a c => 2 * a + c.val) a =
          w.foldl (fun a c => 2 * a + c.val) a := by
      induction w generalizing a with
      | nil => rfl
      | cons c w ih =>
        simp only [List.map_cons, List.foldl_cons]
        rw [ih _ (fun d hd => hw d (List.mem_cons_of_mem _ hd))]
        rcases hw c List.mem_cons_self with rfl | rfl <;> rfl
    rw [aux _ _]
    · exact parse_bits n
    · intro c hc
      obtain ⟨d, _, rfl⟩ := List.mem_map.mp hc
      unfold ofChar
      split <;> simp
  have hword :
      ((bits n).map (letterCode (b := b)) ++ 3 :: rest).takeWhile (fun d => d != 3) =
        (bits n).map letterCode := by
    rw [List.takeWhile_append_of_pos (bits_no_delimiter b n)]
    simp
  have hdelim :
      ((bits n).map (letterCode (b := b)) ++ 3 :: rest).getD ((bits n).map (letterCode (b := b))).length 2 = 3 := by
    simp [List.getD_eq_getElem?_getD]
  unfold readNumeral
  simp only [List.drop_zero]
  rw [hword, hfold, hdelim, numeral_code]
  simp

def haltsWith (X : Set Nat) {s b : Nat} (p : Program s b) (n : Nat)
    (post : Fin (s + 3) → List (Fin (b + 4)) → Prop) : Prop :=
  ∃ (q : Fin (s + 3)) (head : Nat) (tape : List (Fin (b + 4))),
    ReflTransGen (step X p) (0, 0, numeral b n) (q, head, tape) ∧
    halting s q = true ∧ post q tape

theorem decide_with {Q : Type} [Fintype Q] (M : Machine Q Work) (stop : Q)
    (hstop : ∀ a, M.transition stop a = none) (X : Set Nat) (f : Nat → Nat)
    (hM : ∀ n, StateTransition.Reaches (OneSided.step M)
      ⟨M.initial, 0, FoldLiteral.raw (bits n)⟩ ⟨stop, 0, FoldLiteral.raw (out (f n))⟩)
    (e : Work ≃ Fin b) :
    (RelativeComputabilityAndEnumerability X).1 {n | f n ∉ X} := by
  classical
  let enc := symbolCode e
  let p := program M stop FoldLiteral.blank enc
  change ∃ (s b : Nat) (p : Program s b), ∀ n,
    haltsWith X p n (fun _ _ => True) ∧
      (haltsWith X p n (fun q _ => q = 1) ↔ f n ∉ X)
  refine ⟨states Q, b, p, fun n => ?_⟩
  let tape := numeral b n
  let tape' := write (2 : Fin (b + 4)) tape 0 (tape.getD 0 2)
  let q₀ := stateCode (M.initial, false)
  have hboot : step X p (0, 0, tape) (q₀, 0, tape') := by
    refine ⟨rfl, ?_⟩
    simp [p, q₀, tape']
  have hs : simulates enc ⟨M.initial, 0, FoldLiteral.raw (bits n)⟩ (q₀, 0, tape') := by
    refine ⟨rfl, rfl, fun i => ?_⟩
    change tape'.getD i 2 = symbolCode e (FoldLiteral.raw (bits n) i)
    rw [write_same, raw_code, numeral_code]
  obtain ⟨u, hu, hsim⟩ := simulate_run M stop FoldLiteral.blank enc X
    (symbolCode_injective e) hstop hs (hM n)
  rcases u with ⟨q, head, tail⟩
  rcases hsim with ⟨hq, hh, hc⟩
  dsimp only [OneSided.Cfg.state, OneSided.Cfg.pos, OneSided.Cfg.cell, Prod.fst, Prod.snd] at hq hh hc
  subst q head
  have hread := read_output e (f n) tail hc
  have hrun := (ReflTransGen.single hboot).trans hu
  let qf : Fin (states Q + 3) := if f n ∈ X then 2 else 1
  have hquery : step X p (stateCode (stop, false), 0, tail) (qf, 0, tail) := by
    refine ⟨stateCode_nonhalting _, ?_⟩
    unfold p
    rw [program_query]
    dsimp only
    rw [hread]
    by_cases hx : f n ∈ X
    · exact Or.inl ⟨hx, by simp [qf, hx]⟩
    · exact Or.inr ⟨hx, by simp [qf, hx]⟩
  have hhalt : halting (states Q) qf = true := by
    by_cases hx : f n ∈ X <;> simp [qf, hx, halting]
  have hreach := hrun.tail hquery
  refine ⟨⟨qf, 0, tail, hreach, hhalt, trivial⟩, ?_, ?_⟩
  · rintro ⟨r, j, w, hr, hrt, hr1⟩ hx
    have he := congrArg Prod.fst (halt_unique hreach hr hhalt hrt)
    have h21 : (2 : Fin (states Q + 3)) = 1 := by
      simpa [qf, hx, hr1] using he
    have hv := congrArg Fin.val h21
    change 2 = 1 at hv
    omega
  · intro hx
    exact ⟨qf, 0, tail, hreach, hhalt, by simp [qf, hx]⟩

end OracleNegativePullback

theorem OracleNegativePullbackDecision :
    ∀ (X : Set Nat) (f : Nat → Nat), Computable f →
      (RelativeComputabilityAndEnumerability X).1 {n | f n ∉ X} := by
  open OracleNegativePullback OAI.FiniteAlgebraicEnvelopes.MachineRealization in
  intro X f hf
  classical
  let g : List Letter →. List Letter := fun w => Part.some (out (f (parse w)))
  have hg : Partrec g := (comp_preprocess hf).partrec
  obtain ⟨Λ, fintypeΛ, inhabitedΛ, M, start, stop, safe, eval⟩ := WordEvaluator.exists_safe_tape hg
  letI : Fintype Λ := fintypeΛ
  letI : Inhabited Λ := inhabitedΛ
  apply decide_with (FoldLiteral.wrapper M start)
    (some none) (fun _ => rfl) X f _ (Fintype.equivFin Work)
  intro n
  refine (StateTransition.mem_eval.mp ?_).1
  change FoldLiteral.final (out (f n)) ∈
    StateTransition.eval (OneSided.step (FoldLiteral.wrapper M start)) (FoldLiteral.initial (bits n))
  rw [FoldLiteral.wrapper_eval M start stop safe eval]
  apply Part.mem_map _ 
  change out (f n) ∈ Part.some (out (f (parse (bits n))))
  rw [parse_bits]
  exact Part.mem_some _

#print axioms OracleNegativePullbackDecision
