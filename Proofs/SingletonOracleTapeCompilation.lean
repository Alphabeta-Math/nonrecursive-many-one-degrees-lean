import Mathlib

import Proofs.OracleNegativePullbackDecision
import Proofs.RelativeComputabilityAndEnumerability

set_option maxHeartbeats 2000000

namespace SingletonTape
open Computable
open scoped Classical

def agrees (X : Set Nat) (w : List Bool) : Prop :=
  ∀ i b, w[i]? = some b → (b = true ↔ i ∈ X)

def tracks {α β : Type} (X : Set Nat) (F : List Bool × α →. β) (f : α →. β) : Prop :=
  (∀ {w a b}, agrees X w → b ∈ F (w, a) → b ∈ f a) ∧
  (∀ {a b}, b ∈ f a → ∃ k : Nat, ∀ w : List Bool,
    agrees X w → k ≤ w.length → b ∈ F (w, a))

theorem tracks_ignore {α β : Type} (X : Set Nat) (f : α →. β) :
    tracks X (fun p : List Bool × α => f p.2) f :=
  ⟨fun _ h => h, fun h => ⟨0, fun _ _ _ => h⟩⟩

theorem tracks_input {α β γ : Type} {X : Set Nat} {F : List Bool × β →. γ}
    {f : β →. γ} (h : tracks X F f) (g : α → β) :
    tracks X (fun p : List Bool × α => F (p.1, g p.2)) (fun a => f (g a)) :=
  ⟨fun hw hm => h.1 hw hm, fun hm => h.2 hm⟩

theorem tracks_map {α β γ : Type} {X : Set Nat} {F : List Bool × α →. β}
    {f : α →. β} (h : tracks X F f) (g : α → β → γ) :
    tracks X (fun p : List Bool × α => (F p).map (g p.2))
      (fun a => (f a).map (g a)) := by
  constructor
  · intro w a c hw hc
    obtain ⟨b, hb, rfl⟩ := (Part.mem_map_iff _).mp hc
    exact Part.mem_map _ (h.1 hw hb)
  · intro a c hc
    obtain ⟨b, hb, rfl⟩ := (Part.mem_map_iff _).mp hc
    obtain ⟨k, hk⟩ := h.2 hb
    exact ⟨k, fun w hw hl => Part.mem_map _ (hk w hw hl)⟩

theorem tracks_bind {α β γ : Type} {X : Set Nat} {F : List Bool × α →. β}
    {G : List Bool × (α × β) →. γ} {f : α →. β} {g : α × β →. γ}
    (hf : tracks X F f) (hg : tracks X G g) :
    tracks X (fun p : List Bool × α => (F p).bind fun b => G (p.1, p.2, b))
      (fun a => (f a).bind fun b => g (a, b)) := by
  constructor
  · intro w a c hw hc
    obtain ⟨b, hb, hbc⟩ := Part.mem_bind_iff.mp hc
    exact Part.mem_bind_iff.mpr ⟨b, hf.1 hw hb, hg.1 hw hbc⟩
  · intro a c hc
    obtain ⟨b, hb, hbc⟩ := Part.mem_bind_iff.mp hc
    obtain ⟨k, hk⟩ := hf.2 hb
    obtain ⟨l, hl⟩ := hg.2 hbc
    refine ⟨max k l, fun w hw hs => Part.mem_bind_iff.mpr ⟨b, ?_, ?_⟩⟩
    · exact hk w hw ((le_max_left k l).trans hs)
    · exact hl w hw ((le_max_right k l).trans hs)

theorem getOracle_tracks (X : Set Nat) :
    tracks X (fun p : List Bool × Nat => (p.1[p.2]?.map Bool.toNat : Part Nat))
      (fun n => Part.some (if n ∈ X then 1 else 0)) := by
  classical
  constructor
  · intro w n y hw hy
    change y ∈ (w[n]?.map Bool.toNat : Part Nat) at hy
    cases hn : w[n]? with
    | none => simp [hn] at hy
    | some b =>
      have h := hw n b hn
      cases b <;> simp_all [Bool.toNat]
  · intro n y hy
    refine ⟨n + 1, fun w hw hn => ?_⟩
    have hn' : n < w.length := hn
    change y ∈ (w[n]?.map Bool.toNat : Part Nat)
    rw [List.getElem?_eq_getElem hn']
    have h := hw n w[n] (List.getElem?_eq_getElem hn')
    cases he : w[n] <;> simp_all [Bool.toNat]

theorem tracks_rfind {α : Type} {X : Set Nat}
    {F : List Bool × (α × Nat) →. Bool} {f : α × Nat →. Bool}
    (h : tracks X F f) :
    tracks X (fun p : List Bool × α => Nat.rfind fun n => F (p.1, p.2, n))
      (fun a => Nat.rfind fun n => f (a, n)) := by
  constructor
  · intro w a y hw hy
    obtain ⟨hs, hm⟩ := Nat.mem_rfind.mp hy
    exact Nat.mem_rfind.mpr ⟨h.1 hw hs, fun {m} hm' => h.1 hw (hm (m := m) hm')⟩
  · intro a y hy
    obtain ⟨hs, hm⟩ := Nat.mem_rfind.mp hy
    obtain ⟨k, hk⟩ := h.2 hs
    have uniform (n : Nat) (hn : n ≤ y) : ∃ l : Nat, ∀ w : List Bool,
        agrees X w → l ≤ w.length → ∀ j < n, false ∈ F (w, a, j) := by
      induction n with
      | zero => exact ⟨0, by simp⟩
      | succ n ih =>
        obtain ⟨l, hl⟩ := ih (Nat.le_of_succ_le hn)
        obtain ⟨l', hl'⟩ := h.2 (hm (m := n) hn)
        refine ⟨max l l', fun w hw hs j hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact hl w hw ((le_max_left l l').trans hs) j hj
        · exact hl' w hw ((le_max_right l l').trans hs)
    obtain ⟨l, hl⟩ := uniform y le_rfl
    exact ⟨max k l, fun w hw hs => Nat.mem_rfind.mpr
      ⟨hk w hw ((le_max_left k l).trans hs),
        fun {m} hm => hl w hw ((le_max_right k l).trans hs) m hm⟩⟩

theorem tracks_prec {X : Set Nat} {G : List Bool × Nat →. Nat}
    {H : List Bool × Nat →. Nat} {g h : Nat →. Nat}
    (hg : tracks X G g) (hh : tracks X H h) :
    tracks X (fun p : List Bool × Nat =>
      let (a, n) := p.2.unpair
      n.rec (G (p.1, a)) fun y ih => ih.bind fun b => H (p.1, a.pair (y.pair b)))
      (fun p =>
        let (a, n) := p.unpair
        n.rec (g a) fun y ih => ih.bind fun b => h (a.pair (y.pair b))) := by
  have aux (a n : Nat) :
      tracks X (fun p : List Bool × Unit =>
        n.rec (G (p.1, a)) fun y ih => ih.bind fun b => H (p.1, a.pair (y.pair b)))
        (fun _ => n.rec (g a) fun y ih => ih.bind fun b => h (a.pair (y.pair b))) := by
    induction n with
    | zero => exact tracks_input hg (fun _ : Unit => a)
    | succ n ih =>
      exact tracks_bind ih (tracks_input hh (fun p : Unit × Nat => a.pair (n.pair p.2)))
  constructor
  · intro w p b hw hb
    rcases hp : p.unpair with ⟨a, n⟩
    dsimp only at hb ⊢
    rw [hp] at hb ⊢
    obtain ⟨hs, _⟩ := aux a n
    exact hs (a := ()) hw hb
  · intro p b hb
    rcases hp : p.unpair with ⟨a, n⟩
    dsimp only at hb
    rw [hp] at hb
    obtain ⟨_, hc⟩ := aux a n
    obtain ⟨k, hk⟩ := hc (a := ()) hb
    exact ⟨k, fun w hw hwk => by dsimp only; simpa only [hp] using hk w hw hwk⟩

theorem approximate (X : Set Nat) (f : Nat →. Nat)
    (hf : Nat.RecursiveIn {fun n => Part.some (if n ∈ X then 1 else 0)} f) :
    ∃ F : List Bool × Nat →. Nat, Partrec F ∧ tracks X F f := by
  classical
  -- The finite-use statement of Alphabeta Math steps 1.1 and 2.1
  -- assumes a completed tape run. Here finiteness and replay are obtained
  -- from the native recursion derivation before constructing a tape.
  have basic {g : Nat → Nat} (hg : Computable g) :
      ∃ F : List Bool × Nat →. Nat, Partrec F ∧ tracks X F (fun n => Part.some (g n)) :=
    ⟨_, (hg.comp Computable.snd).partrec, tracks_ignore X (fun n => Part.some (g n))⟩
  induction hf with
  | zero => exact basic (Computable.const 0)
  | succ => exact basic (Computable.succ)
  | left => exact basic (Computable.fst.comp Computable.unpair)
  | right => exact basic (Computable.snd.comp Computable.unpair)
  | oracle g hg =>
    obtain rfl := Set.mem_singleton_iff.mp hg
    refine ⟨_, ofOption ?_, getOracle_tracks X⟩
    exact Computable.option_map Computable.list_getElem?
      ((Primrec.dom_bool Bool.toNat).to_comp.comp Computable.snd).to₂
  | pair hf hg ihf ihg =>
    obtain ⟨F, hF, htF⟩ := ihf
    obtain ⟨G, hG, htG⟩ := ihg
    have hP : Computable₂ (fun (p : (List Bool × Nat) × Nat) b => Nat.pair p.2 b) :=
      (Primrec₂.natPair.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd).to₂
    let lift : (List Bool × Nat) × Nat → List Bool × Nat := Prod.fst
    have hlift : Computable lift := Computable.fst
    refine ⟨_, hF.bind ((hG.comp hlift).map hP).to₂, ?_⟩
    have hh := tracks_input htG (Prod.fst : Nat × Nat → Nat)
    simpa only [seq_eq_bind_map, Part.bind_eq_bind, Part.map_eq_map, Part.bind_map]
      using (tracks_bind htF (tracks_map hh (fun p b => p.2.pair b)))
  | comp hf hg ihf ihg =>
    obtain ⟨F, hF, htF⟩ := ihf
    obtain ⟨G, hG, htG⟩ := ihg
    exact ⟨_, hG.bind (hF.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)).to₂,
      tracks_bind htG (tracks_input htF Prod.snd)⟩
  | prec hf hg ihf ihg =>
    obtain ⟨F, hF, htF⟩ := ihf
    obtain ⟨G, hG, htG⟩ := ihg
    let c : List Bool × Nat → Nat × Nat := Nat.unpair ∘ Prod.snd
    have hc : Computable c := Computable.unpair.comp Computable.snd
    have hp := Primrec₂.natPair.to_comp
    have step : Computable (fun p : (List Bool × Nat) × (Nat × Nat) =>
        (p.1.1, (c p.1).1.pair (p.2.1.pair p.2.2))) :=
      (Computable.fst.comp Computable.fst).pair
        (hp.comp (Computable.fst.comp (hc.comp Computable.fst)) (hp.comp Computable.fst Computable.snd |>.comp Computable.snd))
    refine ⟨_, ?_, tracks_prec htF htG⟩
    exact (Partrec.nat_rec (Computable.snd.comp hc)
      (hF.comp (Computable.fst.pair (Computable.fst.comp hc))) (hG.comp step).to₂).of_eq
        (fun p => by rcases hp' : p.2.unpair with ⟨a, n⟩; simp [c, hp'])
  | rfind hf ih =>
    obtain ⟨F, hF, htF⟩ := ih
    have hP : Computable (fun p : List Bool × (Nat × Nat) => (p.1, p.2.1.pair p.2.2)) :=
      Computable.fst.pair (Primrec₂.natPair.to_comp.comp
        (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd))
    have hTest : Computable₂ (fun (_ : List Bool × (Nat × Nat)) (v : Nat) => decide (v = 0)) :=
      (Primrec.eq.decide.comp Primrec.snd (Primrec.const 0)).to_comp.to₂
    let G : List Bool × (Nat × Nat) →. Bool := fun p => (F (p.1, p.2.1.pair p.2.2)).map
      (fun v => decide (v = 0))
    have hG : Partrec G := (hF.comp hP).map hTest
    have htrack := tracks_rfind (tracks_map (tracks_input htF (fun p : Nat × Nat => p.1.pair p.2))
      (fun _ v => decide (v = 0)))
    exact ⟨_, Partrec.rfind ((hG.comp ((Computable.fst.comp Computable.fst).pair
      ((Computable.snd.comp Computable.fst).pair Computable.snd))).to₂), htrack⟩

end SingletonTape


namespace SingletonTape
open Relation OracleNegativePullback
open OracleTapeSupplier.OAI.FiniteAlgebraicEnvelopes
open MachineRealization Compiler.Simulator
open scoped Classical

inductive Control | advance | query | answer (b : Bool) | store (b : Bool)
  deriving DecidableEq, Fintype

abbrev Label (Q : Type) := Q ⊕ Control

def extend {Q : Type} (M : Machine Q Work) : Machine (Label Q) Work where
  initial := .inl M.initial
  transition
    | .inl q, a => (M.transition q a).map fun cmd => ⟨.inl cmd.state, cmd.write, cmd.move⟩
    | .inr _, _ => none

def liftCfg {Q : Type} (c : OneSided.Cfg Work Q) : OneSided.Cfg Work (Label Q) :=
  ⟨.inl c.state, c.pos, c.cell⟩

theorem extend_run {Q : Type} (M : Machine Q Work) {c d : OneSided.Cfg Work Q}
    (h : StateTransition.Reaches (OneSided.step M) c d) :
    StateTransition.Reaches (OneSided.step (extend M)) (liftCfg c) (liftCfg d) := by
  induction h with
  | refl => exact .refl
  | @tail a z _ h ih =>
    apply ih.tail
    change OneSided.step (extend M) (liftCfg a) = some (liftCfg z)
    have he : OneSided.step (extend M) (liftCfg a) =
        (OneSided.step M a).map liftCfg := by
      simp only [OneSided.step, liftCfg, extend]
      cases M.transition a.state (a.cell a.pos) <;> rfl
    rw [he, h]
    rfl

variable {Q : Type} [Fintype Q] {b : Nat}

abbrev stateCount (Q : Type) [Fintype Q] := OracleNegativePullback.states (Label Q)

noncomputable def code (q : Q) : Fin (stateCount Q + 3) := stateCode (Sum.inl q, false)
noncomputable def ctrl (c : Control) : Fin (stateCount Q + 3) := stateCode (Sum.inr c, false)
def boolLetter (v : Bool) : Letter := if v then 1 else 0

abbrev Instruction (s b : Nat) :=
  Sum (Fin (b + 4) → Fin (s + 3) × Fin (b + 4) × Bool) (Fin (s + 3) × Fin (s + 3))

noncomputable def control (init : Q) (c : Control) : Instruction (stateCount Q) b :=
  match c with
  | .advance => .inl fun a => (ctrl .query, a, true)
  | .query => .inr (ctrl (.answer true), ctrl (.answer false))
  | .answer v => .inl fun a => (ctrl (.store v), a, false)
  | .store v => .inl fun _ => (code init, letterCode (boolLetter v), false)

noncomputable def oldProgram (M : Machine Q Work) (stop : Q) (e : Work ≃ Fin b) : Program (stateCount Q) b :=
  program (extend M) (.inl stop) FoldLiteral.blank (symbolCode e)

noncomputable def tapeProgram (M : Machine Q Work) (stop : Q) (e : Work ≃ Fin b) : Program (stateCount Q) b :=
  fun q =>
    if q = code stop then
      .inl fun a => if a = letterCode 2 then (ctrl .advance, a, true) else (1, a, false)
    else if h : ∃ c, q = ctrl (Q := Q) c then control M.initial h.choose
    else oldProgram M stop e q

theorem ctrl_inj : Function.Injective (ctrl (Q := Q)) := by
  intro c d h
  have hh := congrArg Prod.fst (stateCode_injective h)
  exact Sum.inr.inj hh

theorem ctrl_ne_code (c : Control) (q : Q) : ctrl (Q := Q) c ≠ code q := by
  intro h
  have hh : (Sum.inr c : Label Q) = Sum.inl q := congrArg Prod.fst (stateCode_injective h)
  cases hh

theorem tapeProgram_ctrl (M : Machine Q Work) (stop : Q) (e : Work ≃ Fin b) (c : Control) :
    tapeProgram M stop e (ctrl c) = control M.initial c := by
  have hc : ∃ d, ctrl (Q := Q) c = ctrl d := ⟨c, rfl⟩
  rw [tapeProgram, ite_eq_right (ctrl_ne_code c stop), dite_eq_left hc]
  rw [← ctrl_inj hc.choose_spec]

theorem old_ctrl (M : Machine Q Work) (stop : Q) (e : Work ≃ Fin b) (c : Control) :
    oldProgram M stop e (ctrl c) = .inl (fun a => (2, a, false)) := by
  let : Nonempty (Label Q) := ⟨(extend M).initial⟩
  let : Nonempty Work := ⟨FoldLiteral.blank⟩
  simp [oldProgram, ctrl, program, extend,
    Function.leftInverse_invFun stateCode_injective (Sum.inr c, false)]

theorem old_step_lift (M : Machine Q Work) (stop : Q) (e : Work ≃ Fin b) (X : Set Nat)
    {t u : Cfg (stateCount Q) b} (ht : step X (oldProgram M stop e) t u)
    (hu : halting (stateCount Q) u.1 = false) : step X (tapeProgram M stop e) t u := by
  rcases t with ⟨q, j, w⟩
  by_cases hq : q = code stop
  · subst q
    simp only [step, oldProgram, code, program_query] at ht
    have hh := ht.2
    cases hr : readNumeral b w j with
    | none =>
      simp only [hr] at hh
      subst u
      simp [halting] at hu
    | some n =>
      simp only [hr] at hh
      rcases hh with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [halting] at hu
  · by_cases hc : ∃ c, q = ctrl (Q := Q) c
    · obtain ⟨c, rfl⟩ := hc
      simp only [step, old_ctrl] at ht
      have hh := ht.2
      subst u
      simp [halting] at hu
    · exact ⟨ht.1, by simpa only [tapeProgram, ite_eq_right hq, dite_eq_right hc] using ht.2⟩

theorem old_run_lift (M : Machine Q Work) (stop : Q) (e : Work ≃ Fin b) (X : Set Nat)
    {t u : Cfg (stateCount Q) b} (h : ReflTransGen (step X (oldProgram M stop e)) t u)
    (hu : halting (stateCount Q) u.1 = false) : ReflTransGen (step X (tapeProgram M stop e)) t u := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact (ih h.1).tail (old_step_lift M stop e X h hu)

def wordOnTape (w : List Letter) (t : List (Fin (b + 4))) : Prop :=
  ∀ i, t.getD i 2 = (w.map letterCode).getD i 2

theorem tape_run (M : Machine Q Work) (stop : Q) (e : Work ≃ Fin b) (X : Set Nat)
    (hstop : ∀ a, M.transition stop a = none)
    {w w' : List Letter} {t : List (Fin (b + 4))}
    (ht : wordOnTape w t)
    (hrun : StateTransition.Reaches (OneSided.step M)
      ⟨M.initial, 0, FoldLiteral.raw w⟩ ⟨stop, 0, FoldLiteral.raw w'⟩) :
    ∃ t', ReflTransGen (step X (tapeProgram M stop e))
      (code M.initial, 0, t) (code stop, 0, t') ∧ wordOnTape w' t' := by
  have hsim : simulates (symbolCode e) (liftCfg (⟨M.initial, 0, FoldLiteral.raw w⟩ :
      OneSided.Cfg Work Q)) (code M.initial, 0, t) :=
    ⟨rfl, rfl, fun i => (ht i).trans (raw_code e w i).symm⟩
  have hs : ∀ a, (extend M).transition (.inl stop) a = none := by
    intro a
    simp [extend, hstop]
  obtain ⟨u, hu, hsu⟩ := simulate_run (extend M) (.inl stop) FoldLiteral.blank
    (symbolCode e) X (symbolCode_injective e) hs hsim (extend_run M hrun)
  rcases u with ⟨q, j, t'⟩
  rcases hsu with ⟨hq, hj, ht'⟩
  change q = code stop at hq
  change j = 0 at hj
  subst q j
  refine ⟨t', old_run_lift M stop e X hu (stateCode_nonhalting _), fun i => ?_⟩
  exact (ht' i).trans (raw_code e w' i)

theorem tape_boot (M : Machine Q Work) (stop : Q) (e : Work ≃ Fin b) (X : Set Nat) (n : Nat) :
    ∃ t, step X (tapeProgram M stop e) (0, 0, numeral b n) (code M.initial, 0, t) ∧
      wordOnTape (bits n) t := by
  let w := numeral b n
  let t := write (2 : Fin (b + 4)) w 0 (w.getD 0 2)
  have hc : ¬∃ c, (0 : Fin (stateCount Q + 3)) = ctrl (Q := Q) c := by
    rintro ⟨c, hc⟩
    exact stateCode_ne_zero _ hc.symm
  refine ⟨t, ⟨rfl, ?_⟩, fun i => ?_⟩
  · simp [tapeProgram, (stateCode_ne_zero (Sum.inl stop, false)).symm, hc,
      oldProgram, program_start, extend, code, w, t]
  · change (write 2 w 0 (w.getD 0 2)).getD i 2 = _
    rw [write_same, numeral_code]

theorem finDelim_ne_blank : (3 : Fin (b + 4)) ≠ 2 := by
  intro h
  have hv := congrArg Fin.val h
  change 3 = 2 at hv
  omega

theorem finite_prefix (t w : List (Fin (b + 4)))
    (h : ∀ i ≤ w.length, t.getD i 2 = (w ++ [3]).getD i 2) :
    ∃ rest, t = w ++ 3 :: rest := by
  have hc (i : Nat) : (t.take (w.length + 1)).getD i 2 = (w ++ [3]).getD i 2 := by
    by_cases hi : i < w.length + 1
    · rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi, ← List.getD_eq_getElem?_getD]
      exact h i (Nat.le_of_lt_succ hi)
    · have hi' : w.length + 1 ≤ i := Nat.le_of_not_gt hi
      simp [List.getD_eq_getElem?_getD, List.getElem?_take_eq_none hi',
        List.getElem?_eq_none (l := w ++ [3]) (by simpa using hi')]
  obtain ⟨rest, hr⟩ := list_prefix_of_getD _ w 2 3 finDelim_ne_blank hc
  refine ⟨rest ++ t.drop (w.length + 1), ?_⟩
  conv_lhs => rw [← List.take_append_drop (w.length + 1) t]
  rw [hr, List.append_assoc]
  rfl

theorem read_delimited (e : Work ≃ Fin b) (n : Nat) (t : List (Fin (b + 4)))
    (h : ∀ i ≤ (bits n).length, t.getD i 2 = ((out n).map letterCode).getD i 2) :
    readNumeral b t 0 = some n := by
  let w := (bits n).map (letterCode (b := b))
  have hl : w.length = (bits n).length := List.length_map ..
  have hword (i : Nat) (hi : i ≤ w.length) :
      t.getD i 2 = (w ++ [3]).getD i 2 := by
    rw [hl] at hi
    simpa [w, out, List.map_append, letterCode] using h i hi
  obtain ⟨rest, rfl⟩ := finite_prefix t w hword
  have hread : readNumeral b (w ++ [3]) 0 = some n :=
    read_output e n _ (fun i => by rw [raw_code]; simp [w, out, List.map_append, letterCode])
  have hi (r : List (Fin (b + 4))) :
      (w ++ 3 :: r).takeWhile (· != 3) = w := by
    rw [List.takeWhile_append_of_pos (bits_no_delimiter b n)]
    simp [w]
  have hd (r : List (Fin (b + 4))) : (w ++ 3 :: r).getD w.length 2 = 3 := by
    simp [List.getD_eq_getElem?_getD]
  unfold readNumeral at hread ⊢
  simpa only [List.drop_zero, hi, hd] using hread

def queryWord (v : Bool) (q : Nat) (payload : List Letter) : List Letter :=
  2 :: boolLetter v :: (out q ++ payload)

theorem wordOnTape_writeSame {w : List Letter} {t : List (Fin (b + 4))}
    (h : wordOnTape w t) (i : Nat) :
    wordOnTape w (write 2 t i (t.getD i 2)) :=
  fun j => (write_same _ _ _ _).trans (h j)

theorem wordOnTape_setAnswer {q : Nat} {payload : List Letter} {t : List (Fin (b + 4))}
    (h : wordOnTape (queryWord false q payload) t) (v : Bool) :
    wordOnTape (queryWord v q payload) (write 2 t 1 (letterCode (boolLetter v))) := by
  intro i
  rw [write_getD]
  rcases i with _ | _ | i
  · exact h 0
  · simp [queryWord]
  · exact h (i + 2)

theorem read_queryWord (e : Work ≃ Fin b) {v : Bool} {q : Nat} {payload : List Letter}
    {t : List (Fin (b + 4))} (h : wordOnTape (queryWord v q payload) t) :
    readNumeral b t 2 = some q := by
  have he : readNumeral b t 2 = readNumeral b (t.drop 2) 0 := by
    simp only [readNumeral, List.drop_zero]
  rw [he]
  apply read_delimited e
  intro i hi
  have hg : (t.drop 2).getD i 2 = t.getD (2 + i) 2 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [hg, h]
  have hi' : i < ((out q).map (letterCode (b := b))).length := by
    simp [out]
    omega
  simp [queryWord, Nat.add_comm 2 i, List.getD_eq_getElem?_getD, List.getElem?_append_left hi']

theorem tape_accept (M : Machine Q Work) (stop : Q) (e : Work ≃ Fin b) (X : Set Nat)
    (y : Nat) {t : List (Fin (b + 4))} (ht : wordOnTape (out y) t) :
    ∃ u, step X (tapeProgram M stop e) (code stop, 0, t) (1, 0, u) ∧
      readNumeral b u 0 = some y := by
  let u := write (2 : Fin (b + 4)) t 0 (t.getD 0 2)
  have hbit : t.getD 0 2 ≠ letterCode (2 : Letter) := by
    intro he
    have hd : t.getD 0 2 = 3 := he
    have hn : (bits y).length ≠ 0 := by
      intro h
      have hempty : bits y = [] := List.length_eq_zero_iff.mp h
      have hne := Nat.toDigits_ne_nil (b := 2) (n := y)
      apply hne
      simpa only [bits, List.map_eq_nil_iff] using hempty
    have h0 : 0 < ((bits y).map (letterCode (b := b))).length := by simpa using Nat.pos_of_ne_zero hn
    have helem : t.getD 0 2 ∈ (bits y).map (letterCode (b := b)) := by
      rw [ht 0, out, List.map_append, List.getD_eq_getElem?_getD, List.getElem?_append_left h0,
        List.getElem?_eq_getElem h0, Option.getD_some]
      exact List.getElem_mem _
    have hb := bits_no_delimiter b y _ helem
    simp only [hd, bne_self_eq_false, Bool.false_eq_true] at hb
  refine ⟨u, ⟨stateCode_nonhalting _, ?_⟩, ?_⟩
  · simp only [List.getD_eq_getElem?_getD] at hbit
    simp [tapeProgram, hbit, u]
  · apply read_output e
    intro i
    exact (wordOnTape_writeSame ht 0 i).trans (raw_code e (out y) i).symm

theorem tape_query (M : Machine Q Work) (stop : Q) (e : Work ≃ Fin b) (X : Set Nat)
    (q : Nat) (payload : List Letter) {t : List (Fin (b + 4))}
    (ht : wordOnTape (queryWord false q payload) t) :
    ∃ u v,
      step X (tapeProgram M stop e) (code stop, 0, t) u ∧
      ReflTransGen (step X (tapeProgram M stop e)) u (code M.initial, 0, v) ∧
      wordOnTape (queryWord (decide (q ∈ X)) q payload) v := by
  let bit := decide (q ∈ X)
  let t₀ := write (2 : Fin (b + 4)) t 0 (t.getD 0 2)
  let t₁ := write (2 : Fin (b + 4)) t₀ 1 (t₀.getD 1 2)
  let t₂ := write (2 : Fin (b + 4)) t₁ 2 (t₁.getD 2 2)
  let t₃ := write (2 : Fin (b + 4)) t₂ 1 (letterCode (boolLetter bit))
  have htag : t.getD 0 2 = letterCode (2 : Letter) := ht 0
  have h₀ : step X (tapeProgram M stop e) (code stop, 0, t) (ctrl .advance, 1, t₀) := by
    refine ⟨stateCode_nonhalting _, ?_⟩
    simp only [List.getD_eq_getElem?_getD] at htag
    simp [tapeProgram, htag, t₀]
  have h₁ : step X (tapeProgram M stop e) (ctrl .advance, 1, t₀) (ctrl .query, 2, t₁) := by
    refine ⟨stateCode_nonhalting _, ?_⟩
    simp [tapeProgram_ctrl, control, t₁]
  have ht₁ := wordOnTape_writeSame (wordOnTape_writeSame ht 0) 1
  have hr : readNumeral b t₁ 2 = some q := read_queryWord e ht₁
  have h₂ : step X (tapeProgram M stop e) (ctrl .query, 2, t₁) (ctrl (.answer bit), 2, t₁) := by
    refine ⟨stateCode_nonhalting _, ?_⟩
    simp only [tapeProgram_ctrl, control, hr]
    by_cases hx : q ∈ X
    · exact Or.inl ⟨hx, by simp [bit, hx]⟩
    · exact Or.inr ⟨hx, by simp [bit, hx]⟩
  have h₃ : step X (tapeProgram M stop e) (ctrl (.answer bit), 2, t₁) (ctrl (.store bit), 1, t₂) := by
    refine ⟨stateCode_nonhalting _, ?_⟩
    simp [tapeProgram_ctrl, control, t₂]
  have h₄ : step X (tapeProgram M stop e) (ctrl (.store bit), 1, t₂) (code M.initial, 0, t₃) := by
    refine ⟨stateCode_nonhalting _, ?_⟩
    simp [tapeProgram_ctrl, control, t₃]
  exact ⟨_, _, h₀, (((ReflTransGen.single h₁).tail h₂).tail h₃).tail h₄,
    wordOnTape_setAnswer (wordOnTape_writeSame ht₁ 2) bit⟩

end SingletonTape


namespace SingletonTape
open Relation OracleNegativePullback
open OracleTapeSupplier.OAI.FiniteAlgebraicEnvelopes
open MachineRealization Compiler.Simulator
open scoped Classical

noncomputable def oraclePrefix (X : Set Nat) : Nat → List Bool
  | 0 => []
  | n + 1 => oraclePrefix X n ++ [decide (n ∈ X)]

@[simp] theorem oraclePrefix_len (X : Set Nat) (k : Nat) : (oraclePrefix X k).length = k := by
  induction k <;> simp [oraclePrefix, *]

theorem oraclePrefix_agrees (X : Set Nat) (k : Nat) : agrees X (oraclePrefix X k) := by
  induction k with
  | zero => simp [agrees, oraclePrefix]
  | succ k ih =>
    intro i v hv
    by_cases hl : i < k
    · rw [oraclePrefix, List.getElem?_append_left (by simpa using hl)] at hv
      exact ih i v hv
    · have he : k ≤ i := Nat.le_of_not_gt hl
      rw [oraclePrefix, List.getElem?_append_right (by simpa using he), oraclePrefix_len] at hv
      have hi : i = k := by
        by_contra hne
        rw [List.getElem?_eq_none (by simp; omega)] at hv
        cases hv
      subst i
      simp at hv
      rw [← hv]
      exact decide_eq_true_iff

theorem oraclePrefix_take (X : Set Nat) {k n : Nat} (h : k ≤ n) :
    (oraclePrefix X n).take k = oraclePrefix X k := by
  induction n with
  | zero => have : k = 0 := Nat.eq_zero_of_le_zero h; simp [this, oraclePrefix]
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hl
    · apply List.take_of_length_le
      simp
    · have h' : k ≤ n := Nat.le_of_lt_succ hl
      rw [oraclePrefix, List.take_append_of_le_length (by simpa using h')]
      exact ih h'

theorem findTest (X : Set Nat) {F : List Bool × Nat →. Nat} {f : Nat →. Nat}
    (hF : Partrec F) (ht : tracks X F f) :
    ∃ test : List Bool × Nat → Option Nat, Computable test ∧
      ∀ n y, (∃ k, test (oraclePrefix X k, n) = some y) ↔ y ∈ f n := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hF
  have ceval (p : List Bool × Nat) : c.eval (Encodable.encode p) = F p := by
    rw [hc]
    simp [Encodable.encodek, Part.map_id']
  let test : List Bool × Nat → Option Nat := fun p =>
    let kl := p.1.length.unpair
    Nat.Partrec.Code.evaln kl.2 c (Encodable.encode (p.1.take kl.1, p.2))
  have hkl : Primrec (fun p : List Bool × Nat => p.1.length.unpair) :=
    Primrec.unpair.comp (Primrec.list_length.comp Primrec.fst)
  have htake := Primrec.list_take.comp (Primrec.fst.comp hkl) (Primrec.fst : Primrec (@Prod.fst (List Bool) Nat))
  have hp := Primrec.encode.comp (htake.pair Primrec.snd)
  refine ⟨test, (Nat.Partrec.Code.primrec_evaln.comp
    (((Primrec.snd.comp hkl).pair (Primrec.const c)).pair hp)).to_comp, fun n y => ⟨?_, ?_⟩⟩
  · rintro ⟨k, hk⟩
    have h₁ : (Nat.unpair k).1 ≤ k := Nat.unpair_left_le k
    have hr : y ∈ F (oraclePrefix X (Nat.unpair k).1, n) := by
      rw [← ceval]
      apply Nat.Partrec.Code.evaln_sound
      have he := oraclePrefix_take X h₁
      simpa only [test, oraclePrefix_len, he, Option.mem_def] using hk
    exact ht.1 (oraclePrefix_agrees X _) hr
  · intro hy
    obtain ⟨k, hk⟩ := ht.2 hy
    have hy' : y ∈ c.eval (Encodable.encode (oraclePrefix X k, n)) := by
      rw [ceval]
      exact hk _ (oraclePrefix_agrees X k) (by simp)
    obtain ⟨l, hl⟩ := Nat.Partrec.Code.evaln_complete.mp hy'
    refine ⟨Nat.pair k l, ?_⟩
    simpa only [test, oraclePrefix_len, Nat.unpair_pair, oraclePrefix_take X (Nat.left_le_pair k l),
      Option.mem_def] using hl

def packed (n : Nat) (w : List Bool) : List Letter :=
  bits (Nat.pair n (Encodable.encode w))

def stageWord (test : List Bool × Nat → Option Nat) (n : Nat) (w : List Bool) : List Letter :=
  match test (w, n) with
  | some y => out y
  | none => queryWord false w.length (packed n w)

def afterQuery (w : List Letter) : Nat × List Bool :=
  let p := (parse (((w.drop 2).dropWhile (· != 2)).drop 1)).unpair
  (p.1, (Encodable.decode (α := List Bool) p.2).getD [] ++ [w.getD 1 0 == 1])

def dispatch (test : List Bool × Nat → Option Nat) (w : List Letter) : List Letter :=
  if w.getD 0 0 == 2 then stageWord test (afterQuery w).1 (afterQuery w).2
  else stageWord test (parse w) []

theorem not_delim_bits (n : Nat) : ∀ l ∈ bits n, l != 2 := by
  intro l hl
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp hl
  unfold ofChar
  split <;> decide

theorem bits_head_not_delim (n : Nat) : (bits n).getD 0 0 ≠ 2 := by
  cases hk : (bits n)[0]? with
  | none => simp [List.getD_eq_getElem?_getD, hk]
  | some l =>
    have hl := not_delim_bits n l (List.mem_of_getElem? hk)
    simpa [List.getD_eq_getElem?_getD, hk] using hl

theorem dispatch_initial (test : List Bool × Nat → Option Nat) (n : Nat) :
    dispatch test (bits n) = stageWord test n [] := by
  have h := bits_head_not_delim n
  simp only [List.getD_eq_getElem?_getD] at h
  simp [dispatch, h, parse_bits]

theorem dispatch_afterQuery (test : List Bool × Nat → Option Nat) (v : Bool) (q n : Nat)
    (w : List Bool) :
    dispatch test (queryWord v q (packed n w)) = stageWord test n (w ++ [v]) := by
  unfold dispatch afterQuery queryWord
  have hv : (boolLetter v == 1) = v := by cases v <;> rfl
  simp [out, List.append_assoc, List.dropWhile_append_of_pos (not_delim_bits q),
    packed, parse_bits, Encodable.encodek, hv]

theorem comp_dispatch (test : List Bool × Nat → Option Nat) (ht : Computable test) :
    Computable (dispatch test) := by
  open Primrec in
  have pparse : Primrec parse := by
    have digit : Primrec (fun p : Nat × Letter => 2 * p.1 + p.2.val) :=
      nat_add.comp (nat_mul.comp (const 2) fst) (fin_val.comp snd)
    exact list_foldl Primrec.id (const 0) (digit.comp snd).to₂
  open Primrec in
  have pout : Primrec out := list_append.comp prim_bits (const [2])
  open Primrec in
  have pPacked : Primrec (fun p : Nat × List Bool => packed p.1 p.2) :=
    prim_bits.comp (Primrec₂.natPair.comp fst (Primrec.encode.comp snd))
  open Primrec in
  have pQuery : Primrec (fun p : List Bool × Nat =>
      queryWord false p.1.length (packed p.2 p.1)) :=
    list_cons.comp (const 2) (list_cons.comp (const (boolLetter false))
      (list_append.comp (pout.comp (list_length.comp fst)) (pPacked.comp (snd.pair fst))))
  have hStage : Computable (fun p : List Bool × Nat => stageWord test p.2 p.1) := by
    apply (Computable.option_casesOn ht pQuery.to_comp (pout.to_comp.comp Computable.snd).to₂).of_eq
    intro p
    unfold stageWord
    cases test p <;> rfl
  open Primrec in
  have pAfter : Primrec afterQuery := by
    have he : Primrec (fun w : List Letter =>
        (parse (((w.drop 2).dropWhile (· != 2)).drop 1)).unpair) :=
      unpair.comp (pparse.comp (list_drop.comp (const 1)
        ((list_dropWhile (Primrec.not.comp (Primrec.beq.comp Primrec.id (const 2)))).comp
          (list_drop.comp (const 2) Primrec.id))))
    have hbit : Primrec (fun w : List Letter => w.getD 1 0 == 1) :=
      Primrec.beq.comp (list_getD 0 |>.comp Primrec.id (const 1)) (const 1)
    exact (fst.comp he).pair (list_append.comp
      (option_getD.comp (Primrec.decode.comp (snd.comp he)) (const []))
      (list_cons.comp hbit (const [])))
  have hp : Primrec (fun w : List Letter => w.getD 0 0 == 2) :=
    Primrec.beq.comp (Primrec.list_getD 0 |>.comp Primrec.id (Primrec.const 0)) (Primrec.const 2)
  apply (Computable.cond hp.to_comp
    (hStage.comp ((Primrec.snd.comp pAfter).pair (Primrec.fst.comp pAfter)).to_comp)
    (hStage.comp ((Primrec.const []).pair pparse).to_comp)).of_eq
  intro w
  unfold dispatch
  cases w.getD 0 0 == 2 <;> rfl

end SingletonTape

namespace SingletonTape
open Relation OracleNegativePullback
open OracleTapeSupplier.OAI.FiniteAlgebraicEnvelopes
open MachineRealization Compiler.Simulator
open scoped Classical

theorem no_terminal_of_progress {α : Type} {r : α → α → Prop}
    (hu : Relator.RightUnique r) {ready : α → Prop}
    (ha : ∀ a, ready a → ∃ b, TransGen r a b ∧ ready b) {a t : α}
    (hready : ready a) (hr : ReflTransGen r a t) : ∃ v, r t v := by
  let live (s : α) : Prop := ∃ z, TransGen r s z ∧ ready z
  have forward {s u : α} (h : r s u) (hs : live s) : live u := by
    obtain ⟨z, hz, hreadyz⟩ := hs
    obtain ⟨v, hv, hvz⟩ := TransGen.head'_iff.mp hz
    obtain rfl := hu h hv
    rcases reflTransGen_iff_eq_or_transGen.mp hvz with rfl | h'
    · exact ha _ hreadyz
    · exact ⟨z, h', hreadyz⟩
  have ht : live t := by
    induction hr with
    | refl => exact ha _ hready
    | tail _ h ih => exact forward h ih
  obtain ⟨_, hz, _⟩ := ht
  obtain ⟨v, hv, _⟩ := TransGen.head'_iff.mp hz
  exact ⟨v, hv⟩

noncomputable def entryWord (X : Set Nat) (n : Nat) : Nat → List Letter
  | 0 => bits n
  | k + 1 => queryWord (decide (k ∈ X)) k (packed n (oraclePrefix X k))

theorem dispatch_entry (X : Set Nat) (test : List Bool × Nat → Option Nat) (n k : Nat) :
    dispatch test (entryWord X n k) = stageWord test n (oraclePrefix X k) := by
  cases k with
  | zero => exact dispatch_initial test n
  | succ k => exact dispatch_afterQuery test (decide (k ∈ X)) k n (oraclePrefix X k)

theorem compileTest (X : Set Nat) (f : Nat →. Nat) (test : List Bool × Nat → Option Nat)
    (hc : Computable test)
    (htest : ∀ n y, (∃ k, test (oraclePrefix X k, n) = some y) ↔ y ∈ f n) :
    ∃ (s b : Nat) (p : Program s b), ∀ n,
      (haltsWith X p n (fun q _ => q = 1) ↔ (f n).Dom) ∧
      (∀ y ∈ f n, haltsWith X p n (fun _ t => readNumeral b t 0 = some y)) := by
  obtain ⟨Λ, hΛ, iΛ, M₀, first, last, hs, hEval₀⟩ :=
    WordEvaluator.exists_safe_tape (comp_dispatch test hc).partrec
  let : Fintype Λ := hΛ
  let : Inhabited Λ := iΛ
  let M := FoldLiteral.wrapper M₀ first
  let stop : FoldLiteral.State Λ := some none
  let Q := FoldLiteral.State Λ
  let e := Fintype.equivFin Work
  let b := Fintype.card Work
  let s := stateCount Q
  let p := tapeProgram M stop e
  let r := step X p
  have hstop : ∀ a, M.transition stop a = none := fun _ => rfl
  have hEval (w : List Letter) : StateTransition.Reaches (OneSided.step M)
      ⟨M.initial, 0, FoldLiteral.raw w⟩ ⟨stop, 0, FoldLiteral.raw (dispatch test w)⟩ := by
    apply (StateTransition.mem_eval.mp ?_).1
    change FoldLiteral.final (dispatch test w) ∈
      StateTransition.eval (OneSided.step M) (FoldLiteral.initial w)
    rw [FoldLiteral.wrapper_eval M₀ first last hs hEval₀]
    exact Part.mem_map _ (Part.mem_some _)
  refine ⟨s, b, p, fun n => ?_⟩
  let boot : Cfg s b := (0, 0, numeral b n)
  let QInit := code M.initial
  let QStop := code stop
  let entry := entryWord X n
  let check := fun k => test (oraclePrefix X k, n)
  have hzero : ∃ t, r boot (QInit, 0, t) ∧ wordOnTape (entry 0) t :=
    tape_boot M stop e X n
  have transform {k : Nat} {t : List (Fin (b+4))} (ht : wordOnTape (entry k) t) :
      ∃ t', ReflTransGen r (QInit, 0, t) (QStop, 0, t') ∧
        wordOnTape (stageWord test n (oraclePrefix X k)) t' := by
    obtain ⟨t', hreach, hout⟩ := tape_run M stop e X hstop ht (hEval (entry k))
    refine ⟨t', hreach, ?_⟩
    rw [dispatch_entry] at hout
    exact hout
  have advance {k : Nat} {t : List (Fin (b+4))} (ht : wordOnTape (entry k) t)
      (hk : check k = none) :
      ∃ t', TransGen r (QInit, 0, t) (QInit, 0, t') ∧ wordOnTape (entry (k+1)) t' := by
    obtain ⟨t', hr, hout⟩ := transform ht
    have ho : wordOnTape (queryWord false k (packed n (oraclePrefix X k))) t' := by
      simpa only [stageWord, show test (oraclePrefix X k, n) = none from hk, oraclePrefix_len]
        using hout
    obtain ⟨_, u, h₁, h₂, h₃⟩ := tape_query M stop e X k _ ho
    exact ⟨u, (TransGen.tail' hr h₁).trans_left h₂, h₃⟩
  have accept {k y : Nat} {t : List (Fin (b+4))} (ht : wordOnTape (entry k) t)
      (hk : check k = some y) :
      ∃ t', ReflTransGen r (QInit, 0, t) (1, 0, t') ∧ readNumeral b t' 0 = some y := by
    obtain ⟨t', hr, hout⟩ := transform ht
    have ho : wordOnTape (out y) t' := by
      simpa only [stageWord, show test (oraclePrefix X k, n) = some y from hk] using hout
    obtain ⟨u, hu, hy⟩ := tape_accept M stop e X y ho
    exact ⟨u, hr.tail hu, hy⟩
  have reach (k : Nat) (hk : ∀ i < k, check i = none) :
      ∃ t, ReflTransGen r boot (QInit, 0, t) ∧ wordOnTape (entry k) t := by
    induction k with
    | zero =>
      obtain ⟨t, ht, hw⟩ := hzero
      exact ⟨t, .single ht, hw⟩
    | succ k ih =>
      obtain ⟨t, ht, hw⟩ := ih (fun i hi => hk i (Nat.lt_succ_of_lt hi))
      obtain ⟨t', hr, hw'⟩ := advance hw (hk k (Nat.lt_succ_self k))
      exact ⟨t', ht.trans hr.to_reflTransGen, hw'⟩
  have outcome (y : Nat) (hy : y ∈ f n) :
      ∃ t, ReflTransGen r boot (1, 0, t) ∧ readNumeral b t 0 = some y := by
    have hex : ∃ k, check k = some y := (htest n y).mpr hy
    let k := Nat.find hex
    have earlier (i : Nat) (hi : i < k) : check i = none := by
      cases he : check i with
      | none => rfl
      | some z =>
        have hzy := Part.mem_unique ((htest n z).mp ⟨i, he⟩) hy
        subst z
        exact (Nat.find_min hex hi he).elim
    obtain ⟨t, ht, hw⟩ := reach k earlier
    obtain ⟨u, hu, hread⟩ := accept hw (Nat.find_spec hex)
    exact ⟨u, ht.trans hu, hread⟩
  have acceptsOnly (hh : haltsWith X p n (fun q _ => q = 1)) : (f n).Dom := by
    by_contra hd
    have allNone (k : Nat) : check k = none := by
      cases he : check k with
      | none => rfl
      | some y => exact (hd ((htest n y).mp ⟨k, he⟩).fst).elim
    let ready (a : Cfg s b) : Prop := ∃ k t, a = (QInit, 0, t) ∧ wordOnTape (entry k) t
    have progress (a : Cfg s b) (ha : ready a) : ∃ t, TransGen r a t ∧ ready t := by
      obtain ⟨k, t, rfl, hw⟩ := ha
      obtain ⟨u, hu, hw'⟩ := advance hw (allNone k)
      exact ⟨_, hu, k+1, u, rfl, hw'⟩
    obtain ⟨t, hb, hw⟩ := hzero
    obtain ⟨q, j, tape, hrun, hhalt, _⟩ := hh
    have ht := no_terminal_of_progress (step_unique X p) progress
      (show ready (QInit, 0, t) from ⟨0, t, rfl, hw⟩)
      (show ReflTransGen r (QInit, 0, t) (q, j, tape) from by
        rcases ReflTransGen.cases_head hrun with he | ⟨u, hu, htail⟩
        · have hq := congrArg Prod.fst he
          have he' : q = 0 := hq.symm
          rw [he'] at hhalt
          change false = true at hhalt
          contradiction
        · have h := step_unique X p hb hu
          rw [h]
          exact htail)
    obtain ⟨v, hv⟩ := ht
    exact Bool.noConfusion (hhalt.symm.trans hv.1)
  have hhalt : halting s (1 : Fin (s+3)) = true := by simp [halting]
  refine ⟨⟨acceptsOnly, ?_⟩, ?_⟩
  · intro hd
    obtain ⟨t, ht, _⟩ := outcome _ (Part.get_mem hd)
    exact ⟨1, 0, t, ht, hhalt, rfl⟩
  · intro y hy
    obtain ⟨t, ht, hr⟩ := outcome y hy
    exact ⟨1, 0, t, ht, hhalt, hr⟩

end SingletonTape

theorem SingletonOracleTapeCompilation : (∀ X : Set Nat,
  let O : Set (Nat →. Nat) :=
    {fun n => Part.some (@ite Nat (n ∈ X) (Classical.propDecidable _) 1 0)}
  (∀ f : Nat →. Nat, Nat.RecursiveIn O f →
    (RelativeComputabilityAndEnumerability X).2.1 {n | (f n).Dom}) ∧
  (∀ f : Nat → Nat, Nat.RecursiveIn O (fun n => Part.some (f n)) →
    (RelativeComputabilityAndEnumerability X).2.2 f)) :=
(by
  -- Cintioli, arXiv:2609.00419v1, §2 (p. 2), identifies each set with
  -- its characteristic function and uses relative computability and
  -- relative enumerability without giving a tape compiler.
  -- https://arxiv.org/pdf/2609.00419v1
  --
  -- Alphabeta Math, An oracle computation has a finite query witness,
  -- steps 1.1 and 2.1, starts with a halting tape run and replays its
  -- finite queries. Here approximate proves the corresponding finite-use
  -- and replay properties by induction on Nat.RecursiveIn, before a tape
  -- run is available. In the minimization branch, Nat.mem_rfind requires
  -- a successful test and a defined false result at every earlier test.
  -- https://alphabetamath.cc/item/lem-oracle-computation-has-a-finite-query-witness
  --
  -- The coordinator suggested a stack of continuations for native
  -- recursion. We use dovetailed ordinary evaluations on finite oracle
  -- prefixes, so the tape needs only a prefix and the original input.
  -- The pairing schedule visits every prefix-length/fuel pair and tests
  -- an exact prefix. The resulting finite loop uses exists_safe_tape
  -- and wrapper_eval for its ordinary word transformer. To reuse
  -- simulate_run, old_run_lift shows that paths ending in a nonhalting
  -- state cannot traverse any of the replaced terminal instructions.
  -- The new query circuit reads the numeral beyond a two-cell header,
  -- records the bit in that header, and restores the head to the origin.
  -- The numeral codec reuses prim_bits, parse_bits, raw_code, numeral_code,
  -- list_prefix_of_getD and read_output from OracleNegativePullback.
  -- Its step_unique and no_terminal_of_progress exclude accepting runs
  -- when no finite approximation yields a result.
  --
  -- These two conclusions use the installed semidecision and total-output
  -- projections of the shared definition. The article-specific collection
  -- and its defect-report URL both returned HTTP 404 when checked.
  -- https://alphabetamath.cc/item/def-relative-computability-and-enumerability
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects
  intro X
  dsimp only
  have compile {f : Nat →. Nat}
      (hf : Nat.RecursiveIn
        {fun n => Part.some (@ite Nat (n ∈ X) (Classical.propDecidable _) 1 0)} f) :
      ∃ (s b : Nat) (p : OracleNegativePullback.Program s b), ∀ n,
        (OracleNegativePullback.haltsWith X p n (fun q _ => q = 1) ↔ (f n).Dom) ∧
        (∀ y ∈ f n, OracleNegativePullback.haltsWith X p n
          (fun _ t => OracleNegativePullback.readNumeral b t 0 = some y)) := by
    obtain ⟨F, hF, ht⟩ := SingletonTape.approximate X f hf
    obtain ⟨test, hc, htest⟩ := SingletonTape.findTest X hF ht
    exact SingletonTape.compileTest X f test hc htest
  constructor
  · intro f hf
    obtain ⟨s, b, p, hp⟩ := compile hf
    exact ⟨s, b, p, fun n => (hp n).1⟩
  · intro f hf
    obtain ⟨s, b, p, hp⟩ := compile hf
    exact ⟨s, b, p, fun n => (hp n).2 (f n) (Part.mem_some _)⟩)
