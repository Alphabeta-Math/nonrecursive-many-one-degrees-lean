import Mathlib
set_option maxHeartbeats 2000000

namespace OAI

/-!
Literal finite-quota machine simulation and readout correctness.
-/

namespace FiniteAlgebraicEnvelopes.Compiler.Simulator

inductive Move
  | stay | left | right
  deriving DecidableEq

instance : Fintype Move := ⟨{.stay, .left, .right}, by intro x; cases x <;> simp⟩

structure Command (Q Γ : Type*) where
  state : Q
  write : Γ
  move : Move
  deriving DecidableEq, Fintype

/-- A deterministic left-ended one-tape machine. `none` is halt, recognized
    only while the head is at a workspace cell. -/
structure Machine (Q Γ : Type*) where
  initial : Q
  transition : Q → Γ → Option (Command Q Γ)

end FiniteAlgebraicEnvelopes.Compiler.Simulator
end OAI

namespace OAI

/-!
Stack, binary, TM2, and TM0 realizations of partial recursive programs.
-/

namespace FiniteAlgebraicEnvelopes.MachineRealization.StackLift
open Turing Relation
open Turing.PartrecToTM2

 def swap : K' → K'
  | .main => .rev | .rev => .main | .aux => .aux | .stack => .stack
 @[simp] theorem swap_swap (k : K') : swap (swap k) = k := by cases k <;> rfl
 theorem swap_injective : Function.Injective swap := Function.LeftInverse.injective swap_swap

 variable {S Λ : Type*}
 abbrev Symbol (S : Type*) := Γ' ⊕ S
 abbrev Store (S : Type*) := Option (Symbol S)
 inductive Label (S Λ : Type*)
  | pre | emit : S → Label S Λ
  | run : Λ → Label S Λ
  | post | reject
  deriving DecidableEq, Fintype

 def proj : Store S → Option Γ'
  | some (.inl a) => some a | _ => none
 def store (v : Option Γ') : Store S := v.map Sum.inl
 @[simp] theorem proj_store (v : Option Γ') : proj (store (S := S) v) = v := by cases v <;> rfl

 def embedStacks (t : K' → List Γ') : K' → List (Symbol S) := fun k => (t (swap k)).map Sum.inl
 @[simp] theorem embedStacks_swap (t : K' → List Γ') (k : K') :
    embedStacks (S := S) t (swap k) = (t k).map Sum.inl := by simp [embedStacks]
 theorem embedStacks_update (t : K' → List Γ') (k : K') (w : List Γ') :
    embedStacks (S := S) (Function.update t k w) =
      Function.update (embedStacks t) (swap k) (w.map Sum.inl) := by
  funext j
  by_cases h : j = swap k
  · subst j; simp
  · have hh : swap j ≠ k := fun e => h (by rw [←e,swap_swap])
    simp [embedStacks,Function.update_of_ne h,Function.update_of_ne hh]

 def stmt : TM2.Stmt (fun _ : K' => Γ') Λ (Option Γ') →
    TM2.Stmt (fun _ : K' => Symbol S) (Label S Λ) (Store S)
  | .push k f q => .push (swap k) (fun v => .inl (f (proj v))) (stmt q)
  | .peek k f q => .peek (swap k) (fun v a => store (f (proj v) (proj a))) (stmt q)
  | .pop k f q => .pop (swap k) (fun v a => store (f (proj v) (proj a))) (stmt q)
  | .load f q => .load (fun v => store (f (proj v))) (stmt q)
  | .branch f p q => .branch (fun v => f (proj v)) (stmt p) (stmt q)
  | .goto f => .goto (fun v => .run (f (proj v)))
  | .halt => .goto (fun _ => .post)

 def cfg (c : TM2.Cfg (fun _ : K' => Γ') Λ (Option Γ')) :
    TM2.Cfg (fun _ : K' => Symbol S) (Label S Λ) (Store S) :=
  ⟨some (c.l.elim .post .run),store c.var,embedStacks c.stk⟩

 theorem stmt_correct (q : TM2.Stmt (fun _ : K' => Γ') Λ (Option Γ'))
    (v : Option Γ') (t : K' → List Γ') :
    TM2.stepAux (stmt (S := S) q) (store v) (embedStacks t) = cfg (TM2.stepAux q v t) := by
  induction q generalizing v t with
  | push k f q ih =>
      simp only [stmt,TM2.stepAux,proj_store,embedStacks_swap]
      rw [←List.map_cons,←embedStacks_update]
      exact ih _ _
  | peek k f q ih =>
      simp only [stmt,TM2.stepAux,proj_store,embedStacks_swap]
      have he : proj (((t k).map Sum.inl).head? : Store S) = (t k).head? := by
        cases t k <;> rfl
      rw [he]; exact ih _ _
  | pop k f q ih =>
      simp only [stmt,TM2.stepAux,proj_store,embedStacks_swap]
      have he : proj (((t k).map Sum.inl).head? : Store S) = (t k).head? := by
        cases t k <;> rfl
      rw [he,←List.map_tail,←embedStacks_update]
      exact ih _ _
  | load f q ih => simpa only [stmt,TM2.stepAux,proj_store] using ih (f v) t
  | branch f p q ihp ihq =>
      cases h : f v <;> simp only [stmt,TM2.stepAux,proj_store,h,Bool.cond_false,Bool.cond_true]
      · exact ihq _ _
      · exact ihp _ _
  | goto f => simp [stmt,TM2.stepAux,cfg]
  | halt => rfl

 variable (M : Λ → TM2.Stmt (fun _ : K' => Γ') Λ (Option Γ'))
  (W : Label S Λ → TM2.Stmt (fun _ : K' => Symbol S) (Label S Λ) (Store S))
  (hW : ∀ l, W (.run l) = stmt (M l))

 include hW
 theorem step_correct (c : TM2.Cfg (fun _ : K' => Γ') Λ (Option Γ'))
    (d : TM2.Cfg (fun _ : K' => Γ') Λ (Option Γ')) (h : d ∈ TM2.step M c) :
    cfg (S := S) d ∈ TM2.step W (cfg c) := by
  rcases c with ⟨l,v,t⟩
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
      simp only [TM2.step,Option.mem_some_iff] at h
      subst d
      simpa only [cfg,Option.elim_some,TM2.step,hW,Option.mem_some_iff] using stmt_correct (M l) v t

 theorem reaches_correct {c d : TM2.Cfg (fun _ : K' => Γ') Λ (Option Γ')}
    (h : TM2.Reaches M c d) : TM2.Reaches W (cfg (S := S) c) (cfg d) := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (step_correct M W hW _ _ h)

 /-- Until the original interpreter halts, the wrapper cannot escape its run
     sector. This is the divergence/soundness half, not only a terminating test. -/
 theorem path_cases {c : TM2.Cfg (fun _ : K' => Γ') Λ (Option Γ')}
    {z : TM2.Cfg (fun _ : K' => Symbol S) (Label S Λ) (Store S)}
    (h : TM2.Reaches W (cfg c) z) :
    (∃ d, TM2.Reaches M c d ∧ z = cfg d) ∨
    (∃ d, TM2.Reaches M c d ∧ d.l = none ∧ TM2.Reaches W (cfg d) z) := by
  induction h with
  | refl => exact Or.inl ⟨c,.refl,rfl⟩
  | @tail z z' _ hs ih =>
      rcases ih with ⟨d,hd,rfl⟩ | ⟨d,hd,hh,hr⟩
      · cases hl : d.l with
        | none => exact Or.inr ⟨d,hd,hl,ReflTransGen.single hs⟩
        | some l =>
            let e := TM2.stepAux (M l) d.var d.stk
            have he : e ∈ TM2.step M d := by
              rcases d with ⟨ld,vd,td⟩
              simp only at hl
              simp [TM2.step,hl,e]
            have hh := step_correct M W hW d e he
            have hz : z' = cfg e := Option.mem_unique hs hh
            exact Or.inl ⟨e,hd.tail he,hz⟩
      · exact Or.inr ⟨d,hd,hh,hr.tail hs⟩

end FiniteAlgebraicEnvelopes.MachineRealization.StackLift

namespace FiniteAlgebraicEnvelopes.MachineRealization.BinaryCode
open Turing Turing.PartrecToTM2

def value : List Γ' → ℕ
  | [] => 0
  | .bit0 :: l => 2 * value l
  | .bit1 :: l => 2 * value l + 1
  | _ :: l => value l

@[simp] theorem value_pos (n : PosNum) : value (trPosNum n) = (n : ℕ) := by
  induction n with
  | one => rfl
  | bit0 n ih => simpa [trPosNum,value,ih] using (show 2 * (n : ℕ) = (n : ℕ) + (n : ℕ) by omega)
  | bit1 n ih => simpa [trPosNum,value,ih] using (show 2 * (n : ℕ) + 1 = (n : ℕ) + (n : ℕ) + 1 by omega)

@[simp] theorem value_num (n : Num) : value (trNum n) = (n : ℕ) := by cases n <;> simp [trNum,value]
@[simp] theorem value_nat (n : ℕ) : value (trNat n) = n := by simp [trNat]
 theorem trNat_injective : Function.Injective trNat := by
  intro a b h
  simpa using congrArg value h

def block (n : ℕ) : List Γ' := trNat n ++ [.cons]

theorem delimiter_cancel {x y u v : List Γ'}
    (hx : ∀ a ∈ x, natEnd a = false) (hy : ∀ a ∈ y, natEnd a = false)
    (h : x ++ .cons :: u = y ++ .cons :: v) : x = y ∧ u = v := by
  induction x generalizing y with
  | nil =>
      cases y with
      | nil => simpa using h
      | cons a y =>
          have ha : a = Γ'.cons := (List.cons.inj h).1.symm
          have hh := hy a (List.mem_cons_self)
          subst a
          cases hh
  | cons a x ih =>
      cases y with
      | nil =>
          have ha : a = Γ'.cons := (List.cons.inj h).1
          have hh := hx a List.mem_cons_self
          subst a
          cases hh
      | cons b y =>
          obtain ⟨rfl,hh⟩ := List.cons.inj h
          obtain ⟨rfl,hu⟩ := ih (fun c hc => hx c (List.mem_cons_of_mem _ hc))
            (fun c hc => hy c (List.mem_cons_of_mem _ hc)) hh
          exact ⟨rfl,hu⟩

theorem block_cancel {a b : ℕ} {u v : List Γ'}
    (h : block a ++ u = block b ++ v) : a = b ∧ u = v := by
  simp only [block,List.append_assoc,List.singleton_append] at h
  obtain ⟨hab,huv⟩ := delimiter_cancel (trNat_natEnd a) (trNat_natEnd b) h
  exact ⟨trNat_injective hab,huv⟩

end FiniteAlgebraicEnvelopes.MachineRealization.BinaryCode

namespace FiniteAlgebraicEnvelopes.MachineRealization.RawTM
open Turing Turing.PartrecToTM2 Relation
open StackLift BinaryCode
variable {S Λ : Type*} [DecidableEq S] [Encodable S]

abbrev Stmt (S Λ : Type*) := TM2.Stmt (fun _ : K' => Symbol S) (Label S Λ) (Store S)
abbrev Config (S Λ : Type*) := TM2.Cfg (fun _ : K' => Symbol S) (Label S Λ) (Store S)

def tracks (out : List S) (binary : List Γ') : K' → List (Symbol S)
  | .main => out.map Sum.inr
  | .rev => binary.map Sum.inl
  | .aux | .stack => []

omit [DecidableEq S] [Encodable S] in
@[simp] theorem tracks_main (out : List S) (binary : List Γ') : tracks out binary .main = out.map Sum.inr := rfl
omit [DecidableEq S] [Encodable S] in
@[simp] theorem tracks_rev (out : List S) (binary : List Γ') : tracks out binary .rev = binary.map Sum.inl := rfl
omit [DecidableEq S] [Encodable S] in
 theorem tracks_update_main (out : List S) (binary : List Γ') (out' : List S) :
    Function.update (tracks out binary) .main (out'.map Sum.inr) = tracks out' binary := by
  funext k; cases k <;> simp [tracks]
omit [DecidableEq S] [Encodable S] in
 theorem tracks_update_rev (out : List S) (binary binary' : List Γ') :
    Function.update (tracks out binary) .rev (binary'.map Sum.inl) = tracks out binary' := by
  funext k; cases k <;> simp [tracks]

def postCfg (out : List S) (binary : List Γ') : Config S Λ := ⟨some .post,none,tracks out binary⟩
def reject : Stmt S Λ := .goto (fun _ => .reject)
def finish (pre : List Γ') : Stmt S Λ :=
  match Encodable.decode (α := S) (value pre.reverse - 1) with
  | some s => .push .main (fun _ => .inr s) (.load (fun _ => none) (.goto (fun _ => .post)))
  | none => reject

def decoder : ℕ → List Γ' → Stmt S Λ
  | n, pre => .pop .rev (fun _ a => a)
      (.branch (fun v => decide (StackLift.proj v = some .cons)) (finish pre)
        (match n with
        | 0 => reject
        | n+1 => .branch (fun v => decide (StackLift.proj v = some .bit0)) (decoder n (.bit0::pre))
            (.branch (fun v => decide (StackLift.proj v = some .bit1)) (decoder n (.bit1::pre)) reject)))

omit [DecidableEq S] in
theorem decoder_correct (fuel : ℕ) (pre l : List Γ') (tail : List Γ')
    (out : List S) (s : S) (v : Store S)
    (hlen : l.length ≤ fuel) (hbits : ∀ a ∈ l, natEnd a = false)
    (hdec : Encodable.decode (α := S) (value (pre.reverse ++ l) - 1) = some s) :
    TM2.stepAux (decoder (Λ := Λ) fuel pre) v (tracks out (l ++ .cons :: tail)) =
      postCfg (s::out) tail := by
  induction l generalizing fuel pre v with
  | nil =>
      simp only [List.append_nil] at hdec
      cases fuel <;> simp only [decoder,TM2.stepAux,tracks_rev,List.nil_append,List.map_cons,
        List.head?_cons,StackLift.proj,List.tail_cons,decide_true,Bool.cond_true,finish,hdec]
      all_goals
        rw [tracks_update_rev]
        simp only [tracks_main]
        rw [← List.map_cons,tracks_update_main]
        rfl
  | cons a l ih =>
      cases fuel with
      | zero => simp at hlen
      | succ fuel =>
          have hb := hbits a List.mem_cons_self
          have hb' : ∀ a ∈ l, natEnd a = false := fun a ha => hbits a (List.mem_cons_of_mem _ ha)
          have hl : l.length ≤ fuel := by simpa using hlen
          cases a <;> try cases hb
          · simp only [decoder,TM2.stepAux,tracks_rev,List.cons_append,List.map_cons,
              List.head?_cons,StackLift.proj,List.tail_cons,decide_true,Bool.cond_true]
            rw [tracks_update_rev]
            apply ih fuel (.bit0::pre) _ hl hb'
            simpa [List.reverse_cons,List.append_assoc] using hdec
          · simp only [decoder,TM2.stepAux,tracks_rev,List.cons_append,List.map_cons,
              List.head?_cons,StackLift.proj,List.tail_cons,decide_true,Bool.cond_true]
            rw [tracks_update_rev]
            apply ih fuel (.bit1::pre) _ hl hb'
            simpa [List.reverse_cons,List.append_assoc] using hdec

omit [DecidableEq S] in
theorem decoder_block (fuel : ℕ) (tail : List Γ') (out : List S) (s : S) (v : Store S)
    (h : (trNat (Encodable.encode s + 1)).length ≤ fuel) :
    TM2.stepAux (decoder (Λ := Λ) fuel []) v
      (tracks out (block (Encodable.encode s + 1) ++ tail)) = postCfg (s::out) tail := by
  simp only [block,List.append_assoc,List.singleton_append]
  apply decoder_correct fuel [] _ tail out s v h (trNat_natEnd _)
  simp

def pushList : List Γ' → Stmt S Λ → Stmt S Λ
  | [], q => q
  | a::l,q => pushList l (.push .rev (fun _ => .inl a) q)

omit [DecidableEq S] [Encodable S] in
theorem pushList_correct (l : List Γ') (q : Stmt S Λ) (v : Store S)
    (out : List S) (binary : List Γ') :
    TM2.stepAux (pushList l q) v (tracks out binary) =
      TM2.stepAux q v (tracks out (l ++ binary)) := by
  induction l generalizing q binary with
  | nil => rfl
  | cons a l ih =>
      rw [pushList,ih]
      simp only [TM2.stepAux,tracks_rev]
      rw [←List.map_cons,tracks_update_rev]
      rfl

def machine (B : ℕ) (M : Λ → TM2.Stmt (fun _ : K' => Γ') Λ (Option Γ')) (start : Λ) :
    Label S Λ → Stmt S Λ
  | .pre => .pop .main (fun _ a => a) (.goto (fun v =>
      match v with
      | some (.inr s) => .emit s
      | none => .run start
      | _ => .reject))
  | .emit s => pushList (block (Encodable.encode s + 1))
      (.load (fun _ => none) (.goto (fun _ => .pre)))
  | .run l => StackLift.stmt (M l)
  | .post => .peek .rev (fun _ a => a)
      (.branch (fun v => v.isNone) (.load (fun _ => none) .halt) (decoder B []))
  | .reject => reject

def preCfg (out : List S) (binary : List Γ') : Config S Λ := ⟨some .pre,none,tracks out binary⟩
def haltCfg (out : List S) : Config S Λ := ⟨none,none,tracks out []⟩
def runCfg (start : Λ) (binary : List Γ') : Config S Λ := ⟨some (.run start),none,tracks [] binary⟩

variable (B : ℕ) (M : Λ → TM2.Stmt (fun _ : K' => Γ') Λ (Option Γ')) (start : Λ)

omit [DecidableEq S] in
theorem pre_cons (s : S) (out : List S) (binary : List Γ') :
    TM2.Reaches (machine B M start) (preCfg (s::out) binary)
      (preCfg out (block (Encodable.encode s + 1) ++ binary)) := by
  let mid : Config S Λ := ⟨some (.emit s),some (.inr s),tracks out binary⟩
  apply ReflTransGen.trans (b := mid) (ReflTransGen.single ?_) (ReflTransGen.single ?_)
  · simp only [preCfg,TM2.step,machine,TM2.stepAux,tracks_main,List.map_cons,
      List.head?_cons,List.tail_cons]
    rw [tracks_update_main]
    rfl
  · simp only [mid,TM2.step,machine]
    rw [pushList_correct]
    rfl

omit [DecidableEq S] in
theorem pre_nil (binary : List Γ') :
    TM2.Reaches (machine (S := S) B M start) (preCfg [] binary) (runCfg start binary) := by
  apply ReflTransGen.single
  simp only [preCfg,TM2.step,machine,TM2.stepAux,tracks_main,List.map_nil,
    List.head?_nil,List.tail_nil]
  rw [show ([] : List (Symbol S)) = [].map Sum.inr from rfl,tracks_update_main]
  rfl

def numbers (w : List S) : List ℕ := w.map (fun s => Encodable.encode s + 1)

omit [DecidableEq S] [Encodable S] in
@[simp] theorem trList_append (u v : List ℕ) : trList (u ++ v) = trList u ++ trList v := by
  induction u with
  | nil => rfl
  | cons a u ih => simp [trList,ih,List.append_assoc]

omit [DecidableEq S] in
theorem pre_complete (w : List S) (binary : List Γ') :
    TM2.Reaches (machine B M start) (preCfg w binary)
      (runCfg start (trList (numbers w.reverse) ++ binary)) := by
  induction w generalizing binary with
  | nil => simpa [numbers] using pre_nil (S := S) B M start binary
  | cons s w ih =>
      apply (pre_cons B M start s w binary).trans
      simpa [TM2.Reaches,List.reverse_cons,numbers,List.map_append,trList,block,List.append_assoc] using
        ih (block (Encodable.encode s + 1) ++ binary)

omit [DecidableEq S] in
theorem post_cons (s : S) (w out : List S)
    (hB : (trNat (Encodable.encode s + 1)).length ≤ B) :
    TM2.Reaches (machine B M start) (postCfg out (trList (numbers (s::w))))
      (postCfg (s::out) (trList (numbers w))) := by
  apply ReflTransGen.single
  simp only [postCfg,TM2.step,machine,TM2.stepAux,tracks_rev]
  have hn : (trList (numbers (s::w))).map (Sum.inl : Γ' → Symbol S) ≠ [] := by
    simp [numbers,trList]
  rw [show ((trList (numbers (s::w))).map (Sum.inl : Γ' → Symbol S)).head?.isNone = false from by
    simpa using hn]
  simp only [Bool.cond_false,numbers,List.map_cons,trList]
  have hh := decoder_block (Λ := Λ) B (trList (numbers w)) out s
      (((trList (numbers (s::w))).map Sum.inl).head?) hB
  simpa only [Option.mem_some_iff,block,List.append_assoc,List.singleton_append,numbers,
      List.map_cons,trList,postCfg] using hh

omit [DecidableEq S] in
theorem post_nil (out : List S) :
    TM2.Reaches (machine B M start) (postCfg out []) (haltCfg out) := by
  apply ReflTransGen.single
  rfl

omit [DecidableEq S] in
theorem post_complete (w out : List S)
    (hB : ∀ s ∈ w, (trNat (Encodable.encode s + 1)).length ≤ B) :
    TM2.Reaches (machine B M start) (postCfg out (trList (numbers w))) (haltCfg (w.reverse ++ out)) := by
  induction w generalizing out with
  | nil => simpa [numbers] using post_nil B M start out
  | cons s w ih =>
      apply (post_cons B M start s w out (hB s List.mem_cons_self)).trans
      simpa [TM2.Reaches,List.reverse_cons,List.append_assoc] using
        ih (s::out) (fun a ha => hB a (List.mem_cons_of_mem _ ha))

def baseCfg (l : Option Λ) (binary : List Γ') : TM2.Cfg (fun _ : K' => Γ') Λ (Option Γ') :=
  ⟨l,none,K'.elim binary [] [] []⟩

omit [DecidableEq S] [Encodable S] in
@[simp] theorem lift_base_some (l : Λ) (binary : List Γ') :
    StackLift.cfg (S := S) (baseCfg (some l) binary) = runCfg l binary := by
  simp only [StackLift.cfg,baseCfg,runCfg,Option.elim_some]
  congr 1
  funext k; cases k <;> rfl
omit [DecidableEq S] [Encodable S] in
@[simp] theorem lift_base_none (binary : List Γ') :
    StackLift.cfg (S := S) (baseCfg (Λ := Λ) none binary) = postCfg [] binary := by
  simp only [StackLift.cfg,baseCfg,postCfg,Option.elim_none]
  congr 1
  funext k; cases k <;> rfl

omit [DecidableEq S] in
 theorem eval_run {w : List S} {f : List S →. List S}
    (hB : ∀ s : S, (trNat (Encodable.encode s + 1)).length ≤ B)
    (hM : StateTransition.eval (TM2.step M) (baseCfg (some start) (trList (numbers w))) =
      (f w).map (fun out => baseCfg none (trList (numbers out)))) :
    StateTransition.eval (TM2.step (machine B M start)) (runCfg start (trList (numbers w))) =
      (f w).map (fun out => haltCfg out.reverse) := by
  have complete : ∀ out ∈ f w, haltCfg out.reverse ∈
      StateTransition.eval (TM2.step (machine B M start)) (runCfg start (trList (numbers w))) := by
    intro out hout
    have ht : baseCfg (Λ := Λ) none (trList (numbers out)) ∈
        StateTransition.eval (TM2.step M) (baseCfg (some start) (trList (numbers w))) := by
      rw [hM]; exact Part.mem_map _ hout
    have hh := StackLift.reaches_correct (S := S) M (machine B M start) (fun _ => rfl)
      (StateTransition.mem_eval.mp ht).1
    simp only [lift_base_some,lift_base_none] at hh
    apply StateTransition.mem_eval.mpr
    refine ⟨hh.trans ?_,rfl⟩
    simpa only [TM2.Reaches,List.append_nil] using post_complete B M start out [] (fun s _ => hB s)
  apply Part.ext
  intro z
  rw [Part.mem_map_iff]
  constructor
  · intro hz
    obtain ⟨hr,ht⟩ := StateTransition.mem_eval.mp hz
    rw [←lift_base_some] at hr
    rcases StackLift.path_cases M (machine B M start) (fun _ => rfl) hr with
        ⟨d,hd,rfl⟩ | ⟨d,hd,hhalt,hdz⟩
    · simp [StackLift.cfg,TM2.step] at ht
    · have hmem : d ∈ StateTransition.eval (TM2.step M)
          (baseCfg (some start) (trList (numbers w))) := by
        apply StateTransition.mem_eval.mpr
        refine ⟨hd,?_⟩
        rcases d with ⟨l,v,t⟩
        simp only at hhalt
        simp [TM2.step,hhalt]
      rw [hM] at hmem
      obtain ⟨out,hout,he⟩ := (Part.mem_map_iff _).mp hmem
      exact ⟨out,hout,Part.mem_unique (complete out hout) hz⟩
  · rintro ⟨out,hout,rfl⟩
    exact complete out hout

omit [DecidableEq S] in
 theorem eval_pre {w : List S} {f : List S →. List S}
    (hB : ∀ s : S, (trNat (Encodable.encode s + 1)).length ≤ B)
    (hM : StateTransition.eval (TM2.step M) (baseCfg (some start) (trList (numbers w))) =
      (f w).map (fun out => baseCfg none (trList (numbers out)))) :
    StateTransition.eval (TM2.step (machine B M start)) (preCfg w.reverse []) =
      (f w).map (fun out => haltCfg out.reverse) := by
  have hp := pre_complete B M start w.reverse []
  simp only [List.reverse_reverse,List.append_nil] at hp
  rw [StateTransition.reaches_eval hp]
  exact eval_run B M start hB hM

end FiniteAlgebraicEnvelopes.MachineRealization.RawTM

/- Actual finite-state extraction from the Mathlib evaluator.  This is a
   dependency of the compiler realization, not a realization assumption. -/
namespace FiniteAlgebraicEnvelopes.MachineRealization
open Turing Relation

namespace FiniteTM2
variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq Λ]

 def restrictStmt (S : Finset Λ) (q : TM2.Stmt Γ Λ σ) (h : TM2.SupportsStmt S q) :
    TM2.Stmt Γ {l // l ∈ S} σ :=
  match q with
  | .push k f q => .push k f (restrictStmt S q h)
  | .peek k f q => .peek k f (restrictStmt S q h)
  | .pop k f q => .pop k f (restrictStmt S q h)
  | .load f q => .load f (restrictStmt S q h)
  | .branch f p q => .branch f (restrictStmt S p h.1) (restrictStmt S q h.2)
  | .goto f => .goto (fun v => ⟨f v,h v⟩)
  | .halt => .halt

 def embedCfg (S : Finset Λ) (c : TM2.Cfg Γ {l // l ∈ S} σ) : TM2.Cfg Γ Λ σ :=
  ⟨c.l.map Subtype.val,c.var,c.stk⟩

 variable [DecidableEq K]
omit [DecidableEq Λ] in
 theorem embed_stepAux (S : Finset Λ) (q : TM2.Stmt Γ Λ σ) (h : TM2.SupportsStmt S q)
    (v : σ) (t : ∀ k, List (Γ k)) :
    embedCfg S (TM2.stepAux (restrictStmt S q h) v t) = TM2.stepAux q v t := by
  induction q generalizing v t with
  | push k f q ih | peek k f q ih | pop k f q ih | load f q ih =>
      exact ih h _ _
  | branch f p q ihp ihq =>
      cases hv : f v <;> simp only [restrictStmt,TM2.stepAux,hv,Bool.cond_false,Bool.cond_true]
      · exact ihq h.2 _ _
      · exact ihp h.1 _ _
  | goto f => rfl
  | halt => rfl

 variable [Inhabited Λ] (M : Λ → TM2.Stmt Γ Λ σ) (S : Finset Λ) (h : TM2.Supports M S)
 def machine (l : {l // l ∈ S}) : TM2.Stmt Γ {l // l ∈ S} σ :=
  restrictStmt S (M l.val) (h.2 _ l.property)

omit [DecidableEq Λ] in
 theorem embed_step (c : TM2.Cfg Γ {l // l ∈ S} σ) :
    (TM2.step (machine M S h) c).map (embedCfg S) = TM2.step M (embedCfg S c) := by
  rcases c with ⟨l,v,t⟩
  cases l with
  | none => rfl
  | some l => simpa only [TM2.step,embedCfg,Option.map_some,machine] using
      congrArg some (embed_stepAux S (M l.val) (h.2 _ l.property) v t)

omit [DecidableEq Λ] in
 theorem respects : StateTransition.Respects (TM2.step (machine M S h)) (TM2.step M)
    (fun a b => embedCfg S a = b) := by
  apply StateTransition.fun_respects.mpr
  intro a
  have hh := embed_step M S h a
  cases hc : TM2.step (machine M S h) a with
  | none =>
      change TM2.step M (embedCfg S a) = none
      simpa only [hc,Option.map_none] using hh.symm
  | some b =>
      apply TransGen.single
      change TM2.step M (embedCfg S a) = some (embedCfg S b)
      simpa only [hc,Option.map_some] using hh.symm

omit [DecidableEq Λ] in
 theorem eval_embed (c : TM2.Cfg Γ {l // l ∈ S} σ) :
    StateTransition.eval (TM2.step M) (embedCfg S c) =
      (StateTransition.eval (TM2.step (machine M S h)) c).map (embedCfg S) :=
  StateTransition.tr_eval' _ _ _ (respects M S h) c

 variable [Inhabited σ]
 def initial (k : K) (w : List (Γ k)) : TM2.Cfg Γ {l // l ∈ S} σ :=
  ⟨some ⟨default,h.1⟩,default,Function.update (fun _ => []) k w⟩

omit [DecidableEq Λ] in
 @[simp] theorem embed_initial (k : K) (w : List (Γ k)) :
    embedCfg S (initial M S h k w) = TM2.init k w := rfl

omit [DecidableEq Λ] in
 theorem eval_initial (k : K) (w : List (Γ k)) :
    TM2.eval M k w =
      (StateTransition.eval (TM2.step (machine M S h)) (initial M S h k w)).map
        (fun c => c.stk k) := by
  unfold TM2.eval
  rw [←embed_initial M S h k w,eval_embed]
  simp only [Part.map_map]
  rfl

end FiniteTM2

end FiniteAlgebraicEnvelopes.MachineRealization
namespace FiniteAlgebraicEnvelopes.MachineRealization.ListCode
open Turing.ToPartrec Encodable

private theorem eval_comp (f g : Code) (v : List ℕ) :
    (Code.comp f g).eval v = (g.eval v).bind (fun w => f.eval w) := rfl

attribute [local simp] eval_comp

private theorem fix_eval_fwd (c : Code) (w w' : List ℕ)
    (h : Sum.inr w' ∈ Part.map
      (fun v : List ℕ => if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail) (c.eval w)) :
    (Code.fix c).eval w = (Code.fix c).eval w' :=
  PFun.fix_fwd_eq (α := List ℕ) (β := List ℕ)
    (f := fun v : List ℕ => Part.map
      (fun v : List ℕ => if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail) (c.eval v))
    (a := w) (a' := w') h

 def prefix₂ : Code := .cons .head (.cons (.comp .head .tail) .nil)
 @[simp] theorem prefix₂_eval (a b : ℕ) (l : List ℕ) :
    prefix₂.eval (a::b::l) = Part.some [a,b] := by simp [prefix₂]

 theorem binary_code {f : ℕ → ℕ → ℕ} (hf : Computable₂ f) :
    ∃ c : Code, ∀ a b l, c.eval (a::b::l) = Part.some [f a b] := by
  obtain ⟨c,hc⟩ := Code.exists_code (Nat.Partrec'.part_iff₂.mpr hf.partrec₂)
  refine ⟨.comp c prefix₂,fun a b l => ?_⟩
  simp only [eval_comp,prefix₂_eval,Part.bind_some]
  have he := hc ⟨[a,b],rfl⟩
  exact he

 def test (t p q : Code) : Code := .comp (.case p (.comp q .tail)) (.cons t .id)
 theorem test_eval (t p q : Code) (w : List ℕ) {n : ℕ}
    (ht : t.eval w = Part.some [n]) :
    (test t p q).eval w = if n = 0 then p.eval w else q.eval w := by
  simp only [test,eval_comp,Code.cons_eval,Code.id_eval,ht]
  cases n <;> simp [List.headI]

 def one : Code := .comp .succ .zero
 @[simp] theorem one_eval (w : List ℕ) : one.eval w = Part.some [1] := by simp [one]

 def encodeStep (c : Code) : Code :=
  test (.comp .head .tail) (.cons .zero .head)
    (.cons one (.cons c (.comp .tail .tail)))
 def encoder (c : Code) : Code := .comp (.fix (encodeStep c)) .zero'

 theorem encodeStep_nil (c : Code) (a : ℕ) :
    (encodeStep c).eval [a] = Part.some [0,a] := by
  rw [encodeStep,test_eval _ _ _ _ (n := 0) (by simp)]
  simp
 theorem encodeStep_cons (c : Code)
    (hc : ∀ a b l, c.eval (a::b::l) = Part.some [Nat.pair (b-1) a + 1])
    (a b : ℕ) (l : List ℕ) :
    (encodeStep c).eval (a::(b+1)::l) = Part.some (1::(Nat.pair b a + 1)::l) := by
  rw [encodeStep,test_eval _ _ _ _ (n := b+1) (by simp)]
  simp [hc]

 theorem encode_loop (c : Code)
    (hc : ∀ a b l, c.eval (a::b::l) = Part.some [Nat.pair (b-1) a + 1])
    (w acc : List ℕ) :
    (Code.fix (encodeStep c)).eval (encode acc :: w.map Nat.succ) =
      Part.some [encode (w.reverse ++ acc)] := by
  induction w generalizing acc with
  | nil =>
      apply Part.eq_some_iff.mpr
      rw [Code.fix_eval]
      apply PFun.fix_stop
      simp [encodeStep_nil]
  | cons b l ih =>
      rw [List.map_cons]
      have hs : Sum.inr (encode (b::acc)::l.map Nat.succ) ∈
          ((encodeStep c).eval (encode acc::(b+1)::l.map Nat.succ)).map
            (fun v => if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail) := by
        rw [encodeStep_cons c hc]
        simp [encode_list_cons]
      rw [fix_eval_fwd _ _ _ hs,ih]
      simp [List.reverse_cons,List.append_assoc]

 theorem encoder_eval (c : Code)
    (hc : ∀ a b l, c.eval (a::b::l) = Part.some [Nat.pair (b-1) a + 1]) (w : List ℕ) :
    (encoder c).eval (w.map Nat.succ) = Part.some [encode w.reverse] := by
  simp only [encoder,eval_comp,Code.zero'_eval]
  simpa using encode_loop c hc w []

 def decodeStep (h t : Code) : Code :=
  test .head (.cons .zero .tail)
    (.cons one (.cons t (.cons h .tail)))
 def decoder (h t : Code) : Code := .fix (decodeStep h t)
 theorem decodeStep_zero (h t : Code) (l : List ℕ) :
    (decodeStep h t).eval (0::l) = Part.some (0::l) := by
  rw [decodeStep,test_eval _ _ _ _ (n := 0) (by simp)]
  simp
 theorem decodeStep_cons (h t : Code)
    (hh : ∀ n l, h.eval (n::l) = Part.some [(n-1).unpair.1+1])
    (ht : ∀ n l, t.eval (n::l) = Part.some [(n-1).unpair.2])
    (b : ℕ) (w l : List ℕ) :
    (decodeStep h t).eval (encode (b::w)::l) = Part.some (1::encode w::(b+1)::l) := by
  rw [decodeStep,test_eval _ _ _ _ (n := encode (b::w)) (by simp)]
  simp [encode_list_cons,hh,ht]

 theorem decoder_eval (h t : Code)
    (hh : ∀ n l, h.eval (n::l) = Part.some [(n-1).unpair.1+1])
    (ht : ∀ n l, t.eval (n::l) = Part.some [(n-1).unpair.2])
    (w acc : List ℕ) :
    (decoder h t).eval (encode w::acc) = Part.some (w.reverse.map Nat.succ ++ acc) := by
  induction w generalizing acc with
  | nil =>
      apply Part.eq_some_iff.mpr
      rw [decoder,Code.fix_eval]
      apply PFun.fix_stop
      simp [decodeStep_zero]
  | cons b w ih =>
      rw [decoder]
      have hs : Sum.inr (encode w::(b+1)::acc) ∈
          ((decodeStep h t).eval (encode (b::w)::acc)).map
            (fun v => if v.headI = 0 then Sum.inl v.tail else Sum.inr v.tail) := by
        rw [decodeStep_cons h t hh ht]
        simp
      rw [fix_eval_fwd _ _ _ hs]
      change (decoder h t).eval _ = _
      rw [ih]
      simp [List.reverse_cons,List.map_append,List.append_assoc]

 theorem unary_code {f : ℕ → ℕ} (hf : Computable f) :
    ∃ c : Code, ∀ n l, c.eval (n::l) = Part.some [f n] := by
  obtain ⟨c,hc⟩ := Code.exists_code (Nat.Partrec'.part_iff₁.mpr hf.partrec)
  refine ⟨.comp c .head,fun n l => ?_⟩
  simp only [eval_comp,Code.head_eval,List.headI_cons]
  rw [show (pure [n] : Part (List ℕ)) = Part.some [n] from rfl,Part.bind_some]
  have he := hc ⟨[n],rfl⟩
  exact he

 theorem exists_wordCode {f : List ℕ →. List ℕ} (hf : Partrec f) :
    ∃ c : Code, ∀ w, c.eval (w.map Nat.succ) = (f w).map (List.map Nat.succ) := by
  obtain ⟨ce,hce⟩ := binary_code
    ((Computable.succ.comp (Primrec₂.natPair.to_comp.comp
      (Primrec.nat_sub.to_comp.comp Computable.snd (Computable.const 1)) Computable.fst)).to₂)
  obtain ⟨ch,hch⟩ := unary_code
    (Computable.succ.comp (Computable.fst.comp (Primrec.unpair.to_comp.comp
      (Primrec.nat_sub.to_comp.comp Computable.id (Computable.const 1)))))
  obtain ⟨ct,hct⟩ := unary_code
    (Computable.snd.comp (Primrec.unpair.to_comp.comp
      (Primrec.nat_sub.to_comp.comp Computable.id (Computable.const 1))))
  let g : ℕ →. ℕ := fun n => (f (Denumerable.ofNat (List ℕ) n).reverse).map
    (fun l => encode l.reverse)
  have hg : Partrec g :=
    (hf.comp (Computable.list_reverse.comp (Computable.ofNat (List ℕ)))).map
      ((Computable.encode.comp Computable.list_reverse).comp Computable.snd).to₂
  obtain ⟨cf,hcf⟩ := Code.exists_code (Nat.Partrec'.part_iff₁.mpr hg)
  refine ⟨.comp (decoder ch ct) (.comp cf (encoder ce)),fun w => ?_⟩
  simp only [eval_comp,encoder_eval ce hce,Part.bind_some]
  rw [hcf ⟨[encode w.reverse],rfl⟩]
  change ((g (encode w.reverse)).map (fun n => [n])).bind (fun v => (decoder ch ct).eval v) = _
  simp only [g,Denumerable.ofNat_encode,List.reverse_reverse]
  apply Part.ext
  intro out
  simp only [Part.mem_bind_iff,Part.mem_map_iff]
  constructor
  · rintro ⟨_,⟨n,⟨l,hl,rfl⟩,rfl⟩,hd⟩
    have he := decoder_eval ch ct hch hct l.reverse []
    simp only [List.reverse_reverse,List.append_nil] at he
    rw [he,Part.mem_some_iff] at hd
    exact ⟨l,hl,hd.symm⟩
  · rintro ⟨l,hl,rfl⟩
    refine ⟨[encode l.reverse],⟨encode l.reverse,⟨l,hl,rfl⟩,rfl⟩,?_⟩
    rw [decoder_eval ch ct hch hct l.reverse []]
    simp

end FiniteAlgebraicEnvelopes.MachineRealization.ListCode

namespace FiniteAlgebraicEnvelopes.MachineRealization

section
open Turing Turing.ToPartrec Turing.PartrecToTM2
open RawTM

namespace FiniteTM2
variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq Λ]
omit [DecidableEq Λ] in
 theorem embedCfg_injective (A : Finset Λ) : Function.Injective (embedCfg (Γ := Γ) (σ := σ) A) := by
  rintro ⟨l,v,t⟩ ⟨l',v',t'⟩ h
  have hl := congrArg TM2.Cfg.l h
  have hv := congrArg TM2.Cfg.var h
  have ht := congrArg TM2.Cfg.stk h
  dsimp only [embedCfg] at hl hv ht
  have he := Option.map_injective Subtype.val_injective hl
  cases he
  cases hv
  cases ht
  rfl
end FiniteTM2

 theorem part_map_injective {A B : Type*} {g : A → B} (hg : Function.Injective g) :
    Function.Injective (Part.map g) := by
  intro p q h
  apply Part.ext
  intro a
  constructor <;> intro ha
  · have hh : g a ∈ p.map g := Part.mem_map _ ha
    rw [h] at hh
    obtain ⟨b,hb,he⟩ := (Part.mem_map_iff _).mp hh
    exact (hg he) ▸ hb
  · have hh : g a ∈ q.map g := Part.mem_map _ ha
    rw [←h] at hh
    obtain ⟨b,hb,he⟩ := (Part.mem_map_iff _).mp hh
    exact (hg he) ▸ hb

namespace WordEvaluator
variable {S : Type} [Primcodable S]

 theorem exists_code {f : List S →. List S} (hf : Partrec f) :
    ∃ c : Code, ∀ w, c.eval (numbers w) = (f w).map numbers := by
  let g : List ℕ →. List ℕ := fun ns =>
    (f (ns.filterMap Encodable.decode)).map (List.map Encodable.encode)
  have hg : Partrec g :=
    (hf.comp (Primrec.listFilterMap Primrec.id (Primrec.decode.comp Primrec.snd).to₂).to_comp).map
      ((Primrec.list_map Primrec.id (Primrec.encode.comp Primrec.snd).to₂).to_comp.comp Computable.snd).to₂
  obtain ⟨c,hc⟩ := ListCode.exists_wordCode hg
  refine ⟨c,fun w => ?_⟩
  have hcc := hc (w.map Encodable.encode)
  have hlist : (w.map Encodable.encode).filterMap Encodable.decode = w := by
    induction w <;> simp_all
  change c.eval (w.map (fun s => Encodable.encode s + 1)) =
    (f w).map (fun out => out.map (fun s => Encodable.encode s + 1))
  simpa only [g,hlist,Part.map_map,List.map_map,Function.comp_def,Nat.succ_eq_add_one] using hcc

 theorem exists_finite {f : List S →. List S} (hf : Partrec f) :
    ∃ (Λ : Type) (_ : Fintype Λ) (start : Λ)
      (M : Λ → TM2.Stmt (fun _ : K' => Γ') Λ (Option Γ')),
      ∀ w, StateTransition.eval (TM2.step M) (baseCfg (some start) (trList (numbers w))) =
        (f w).map (fun out => baseCfg none (trList (numbers out))) := by
  obtain ⟨c,hc⟩ := exists_code hf
  let A := codeSupp c Cont'.halt
  let : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  have hs : TM2.Supports tr A := tr_supports c Cont'.halt
  let start : {l // l ∈ A} := ⟨trNormal c Cont'.halt,hs.1⟩
  let M := FiniteTM2.machine tr A hs
  refine ⟨{l // l ∈ A},inferInstance,start,M,fun w => ?_⟩
  apply part_map_injective (FiniteTM2.embedCfg_injective A)
  rw [←FiniteTM2.eval_embed tr A hs]
  change StateTransition.eval (TM2.step tr) (init c (numbers w)) = _
  rw [tr_eval,hc]
  simp only [Part.map_eq_map,Part.map_map]
  rfl

variable [Fintype S]
 noncomputable def bound : ℕ := Finset.univ.sup fun s : S => (trNat (Encodable.encode s + 1)).length
 theorem le_bound (s : S) : (trNat (Encodable.encode s + 1)).length ≤ bound (S := S) :=
  Finset.le_sup (f := fun s : S => (trNat (Encodable.encode s + 1)).length) (Finset.mem_univ s)

 theorem exists_raw {f : List S →. List S} (hf : Partrec f) :
    ∃ (Λ : Type) (_ : Fintype Λ) (M : Λ → TM2.Stmt (fun _ : K' => StackLift.Symbol S) Λ (StackLift.Store S))
      (start : Λ), ∀ w,
      StateTransition.eval (TM2.step M)
        ⟨some start,none,tracks w.reverse []⟩ =
          (f w).map (fun out => ⟨none,none,tracks out.reverse []⟩) := by
  classical
  obtain ⟨Λ,hΛ,start,M,hM⟩ := exists_finite hf
  let : Fintype Λ := hΛ
  refine ⟨StackLift.Label S Λ,inferInstance,machine (bound (S := S)) M start,.pre,fun w => ?_⟩
  exact eval_pre (bound (S := S)) M start le_bound (hM w)

end WordEvaluator
end

open Turing Relation
namespace FiniteTM0
variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] [DecidableEq Λ]
variable (M : TM0.Machine Γ Λ) (A : Finset Λ) (h : TM0.Supports M (A : Set Λ))
variable [Inhabited {l // l ∈ A}]

def machine : TM0.Machine Γ {l // l ∈ A} := fun q a =>
  (M q.val a).pmap (fun p hp => (⟨p.1,h.2 hp q.property⟩,p.2)) (fun _ hp => hp)

def embed (c : TM0.Cfg Γ {l // l ∈ A}) : TM0.Cfg Γ Λ := ⟨c.q.val,c.Tape⟩

omit [Inhabited Λ] [DecidableEq Λ] [Inhabited {l // l ∈ A}] in
theorem embed_injective : Function.Injective (embed (Γ := Γ) A) := by
  rintro ⟨q,t⟩ ⟨q',t'⟩ he
  have hq : q = q' := Subtype.ext (congrArg TM0.Cfg.q he)
  have ht := congrArg TM0.Cfg.Tape he
  cases hq
  cases ht
  rfl

omit [DecidableEq Λ] in
theorem embed_step (c : TM0.Cfg Γ {l // l ∈ A}) :
    (TM0.step (machine M A h) c).map (embed A) = TM0.step M (embed A c) := by
  rcases c with ⟨q,t⟩
  cases hc : M q.val t.head with
  | none => simp [TM0.step,machine,embed,hc]
  | some p => rcases p with ⟨q',s⟩; cases s <;> simp [TM0.step,machine,embed,hc]

omit [DecidableEq Λ] in
theorem respects : StateTransition.Respects (TM0.step (machine M A h)) (TM0.step M)
    (fun a b => embed A a = b) := by
  apply StateTransition.fun_respects.mpr
  intro a
  have hh := embed_step M A h a
  cases hc : TM0.step (machine M A h) a with
  | none =>
      change TM0.step M (embed A a) = none
      simpa only [hc,Option.map_none] using hh.symm
  | some b =>
      apply TransGen.single
      change TM0.step M (embed A a) = some (embed A b)
      simpa only [hc,Option.map_some] using hh.symm

omit [DecidableEq Λ] in
theorem eval_embed (c : TM0.Cfg Γ {l // l ∈ A}) :
    StateTransition.eval (TM0.step M) (embed A c) =
      (StateTransition.eval (TM0.step (machine M A h)) c).map (embed A) :=
  StateTransition.tr_eval' _ _ _ (respects M A h) c
end FiniteTM0

namespace StackTape
open Turing.PartrecToTM2 StackLift RawTM
variable {S Λ : Type} [Fintype S] [Fintype Λ] [Inhabited Λ]

 def slice (a : S) : ∀ _ : K', Option (Symbol S) := Function.update (fun _ => none) .main (some (.inr a))
 def stackList (w : List S) : ListBlank (∀ _ : K', Option (Symbol S)) := ListBlank.mk (w.map slice)
 def tape (w : List S) : Turing.Tape (TM2to1.Γ' K' (fun _ => Symbol S)) :=
   Turing.Tape.mk' ∅ (TM2to1.addBottom (stackList w))

omit [Fintype S] in
 theorem tracks_proj (w : List S) (k : K') :
   (stackList w).map (Turing.proj k) = ListBlank.mk (((tracks w.reverse [] k).map some).reverse) := by
  cases k <;> simp [stackList,slice,tracks,Turing.proj,ListBlank.map_mk,List.map_reverse,List.map_map,
    Function.comp_def] <;> exact Quotient.sound (Or.inr ⟨w.length,rfl⟩)

omit [Fintype S] [Fintype Λ] [Inhabited Λ] in
 theorem trCfg (w : List S) (l : Option Λ) (v : Store S) :
   TM2to1.TrCfg (⟨l,v,tracks w.reverse []⟩ : TM2.Cfg (fun _ : K' => Symbol S) Λ (Store S))
     ⟨l.map .normal,v,tape w⟩ := .mk (stackList w) (tracks_proj w)

omit [Fintype S] in
 theorem stackList_unique (w : List S) (L : ListBlank (∀ _ : K', Option (Symbol S)))
    (hL : ∀ k, L.map (Turing.proj k) = ListBlank.mk (((tracks w.reverse [] k).map some).reverse)) :
    L = stackList w := by
  apply ListBlank.ext
  intro n
  funext k
  have he := congrArg (fun l => ListBlank.nth l n) ((hL k).trans (tracks_proj w k).symm)
  simpa only [ListBlank.nth_map,Turing.proj,PointedMap.mk_val] using he

omit [Fintype S] [Fintype Λ] [Inhabited Λ] in
 theorem trCfg_unique (w : List S) (l : Option Λ) (v : Store S)
    {c : TM1.Cfg (TM2to1.Γ' K' (fun _ => Symbol S)) (TM2to1.Λ' K' (fun _ => Symbol S) Λ (Store S)) (Store S)}
    (hc : TM2to1.TrCfg (⟨l,v,tracks w.reverse []⟩ : TM2.Cfg (fun _ : K' => Symbol S) Λ (Store S)) c) :
    c = ⟨l.map .normal,v,tape w⟩ := by
  cases hc with
  | mk L hL => rw [stackList_unique w L hL]; rfl

 variable (M : Λ → TM2.Stmt (fun _ : K' => Symbol S) Λ (Store S))
omit [Fintype S] [Fintype Λ] [Inhabited Λ] in
 theorem eval_tape {f : List S →. List S} (start : Λ)
   (hM : ∀ w, StateTransition.eval (TM2.step M) ⟨some start,none,tracks w.reverse []⟩ =
      (f w).map (fun out => ⟨none,none,tracks out.reverse []⟩)) (w : List S) :
   StateTransition.eval (TM1.step (TM2to1.tr M)) ⟨some (.normal start),none,tape w⟩ =
     (f w).map (fun out => ⟨none,none,tape out⟩) := by
  apply Part.ext
  intro c
  constructor
  · intro hc
    obtain ⟨b,hbc,hb⟩ := StateTransition.tr_eval_rev (TM2to1.tr_respects M) (trCfg w (some start) none) hc
    rw [hM] at hb
    obtain ⟨out,hout,rfl⟩ := (Part.mem_map_iff _).mp hb
    rw [trCfg_unique out none none hbc]
    exact Part.mem_map _ hout
  · intro hc
    obtain ⟨out,hout,rfl⟩ := (Part.mem_map_iff _).mp hc
    have hb : (⟨none,none,tracks out.reverse []⟩ : TM2.Cfg (fun _ : K' => Symbol S) Λ (Store S)) ∈
       StateTransition.eval (TM2.step M) ⟨some start,none,tracks w.reverse []⟩ := by
      rw [hM]; exact Part.mem_map _ hout
    obtain ⟨b,hb,hbe⟩ := StateTransition.tr_eval (TM2to1.tr_respects M) (trCfg w (some start) none) hb
    simpa only [trCfg_unique out none none hb,Option.map_none,Option.map_some] using hbe

omit [Fintype S] [Fintype Λ] in
 theorem eval_post {f : List S →. List S} (start : Λ)
   (hM : ∀ w, StateTransition.eval (TM2.step M) ⟨some start,none,tracks w.reverse []⟩ =
      (f w).map (fun out => ⟨none,none,tracks out.reverse []⟩)) (w : List S) :
   StateTransition.eval (TM0.step (TM1to0.tr (TM2to1.tr M)))
     (TM1to0.trCfg (TM2to1.tr M) ⟨some (.normal start),none,tape w⟩) =
     (f w).map (fun out => (⟨(none,none),tape out⟩ : TM0.Cfg _ _)) := by
   rw [StateTransition.tr_eval' _ _ _ (TM1to0.tr_respects (TM2to1.tr M)),eval_tape M start hM]
   simp only [Part.map_eq_map,Part.map_map]
   rfl

end StackTape

end FiniteAlgebraicEnvelopes.MachineRealization
end OAI

namespace OAI

/-!
Safe tapes, literal folding, and uniform code-machine realization.
-/

namespace FiniteAlgebraicEnvelopes.MachineRealization.OneSided
open Compiler.Simulator Turing Relation
variable {Γ Q : Type*}

structure Cfg (Γ Q : Type*) where
  state : Q
  pos : ℕ
  cell : ℕ → Γ

def step (M : Machine Q Γ) (c : Cfg Γ Q) : Option (Cfg Γ Q) :=
  (M.transition c.state (c.cell c.pos)).map fun cmd =>
    ⟨cmd.state,(match cmd.move with | .stay => c.pos | .left => c.pos-1 | .right => c.pos+1),
      Function.update c.cell c.pos cmd.write⟩

end FiniteAlgebraicEnvelopes.MachineRealization.OneSided

namespace FiniteAlgebraicEnvelopes.MachineRealization.TapeFold
open Turing Relation Compiler.Simulator
variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

inductive Side | pos | neg deriving DecidableEq
instance : Fintype Side := ⟨{.pos,.neg},by intro x; cases x <;> simp⟩
structure Cell (Γ : Type*) where
  origin : Bool
  pos : Γ
  neg : Γ
  deriving DecidableEq, Fintype

def position : Side → ℕ → ℤ
  | .pos,n => n
  | .neg,n => -(n+1 : ℤ)

def read (d : Side) (a : Cell Γ) : Γ := match d with | .pos => a.pos | .neg => a.neg

def command (d : Side) (q : Λ) (a : Cell Γ) : TM0.Stmt Γ → Command (Side × Λ) (Cell Γ)
  | .write b => ⟨(d,q),(match d with | .pos => {a with pos := b} | .neg => {a with neg := b}),.stay⟩
  | .move dr => match d,dr with
    | .pos,.right => ⟨(.pos,q),a,.right⟩
    | .pos,.left => if a.origin then ⟨(.neg,q),a,.stay⟩ else ⟨(.pos,q),a,.left⟩
    | .neg,.left => ⟨(.neg,q),a,.right⟩
    | .neg,.right => if a.origin then ⟨(.pos,q),a,.stay⟩ else ⟨(.neg,q),a,.left⟩

def machine (M : TM0.Machine Γ Λ) (start : Λ) : Machine (Side × Λ) (Cell Γ) :=
  ⟨(.pos,start),fun q a => (M q.2 (read q.1 a)).map fun cmd => command q.1 cmd.1 a cmd.2⟩

/-- The two halves of the integer tape share one physical cell. The immutable
origin flag makes crossing the fold a finite-control, zero-movement operation. -/
def Rel (c : TM0.Cfg Γ Λ) (s : OneSided.Cfg (Cell Γ) (Side × Λ)) : Prop :=
  s.state.2 = c.q ∧ ∀ n,
    (s.cell n).origin = decide (n = 0) ∧
    (s.cell n).pos = c.Tape.nth ((n:ℤ) - position s.state.1 s.pos) ∧
    (s.cell n).neg = c.Tape.nth (-(n+1:ℤ) - position s.state.1 s.pos)

omit [Inhabited Λ] in
theorem read_head {c : TM0.Cfg Γ Λ} {s : OneSided.Cfg (Cell Γ) (Side × Λ)} (h : Rel c s) :
    read s.state.1 (s.cell s.pos) = c.Tape.head := by
  obtain ⟨_,hs⟩ := h
  obtain ⟨_,hp,hn⟩ := hs s.pos
  cases hd : s.state.1 <;> simp only [read,hd,position,sub_self,Tape.nth_zero] at * <;> assumption

omit [Inhabited Γ] [Inhabited Λ] in
 theorem move_position (d : Side) (dr : Dir) (q : Λ) (a : Cell Γ) (p : ℕ)
    (ha : a.origin = decide (p = 0)) :
    let cmd := command d q a (.move dr)
    position cmd.state.1 (match cmd.move with | .stay => p | .left => p-1 | .right => p+1) =
      position d p + (match dr with | .left => -1 | .right => 1) := by
  cases d <;> cases dr <;> simp only [command,ha] <;>
    (try split_ifs) <;> simp_all [position] <;> omega

omit [Inhabited Γ] [Inhabited Λ] in
 theorem move_write (d : Side) (dr : Dir) (q : Λ) (a : Cell Γ) :
    (command d q a (.move dr)).write = a := by
  cases d <;> cases dr <;> simp only [command] <;> (try split_ifs) <;> rfl

omit [Inhabited Γ] [Inhabited Λ] in
 theorem command_state (d : Side) (q : Λ) (a : Cell Γ) (stmt : TM0.Stmt Γ) :
    (command d q a stmt).state.2 = q := by
  cases stmt with
  | write b => cases d <;> rfl
  | move dr => cases d <;> cases dr <;> simp only [command] <;> (try split_ifs) <;> rfl

 theorem step_rel (M : TM0.Machine Γ Λ) (start : Λ)
    {c : TM0.Cfg Γ Λ} {s : OneSided.Cfg (Cell Γ) (Side × Λ)} (hs : Rel c s)
    {cmd : Λ × TM0.Stmt Γ} (hc : M c.q c.Tape.head = some cmd) :
    ∃ t, Rel (⟨cmd.1,match cmd.2 with | .move d => c.Tape.move d | .write b => c.Tape.write b⟩) t ∧
      OneSided.step (machine M start) s = some t := by
  let ins := command s.state.1 cmd.1 (s.cell s.pos) cmd.2
  let t : OneSided.Cfg (Cell Γ) (Side × Λ) :=
    ⟨ins.state,(match ins.move with | .stay => s.pos | .left => s.pos-1 | .right => s.pos+1),
      Function.update s.cell s.pos ins.write⟩
  refine ⟨t,?_,?_⟩
  · refine ⟨command_state _ _ _ _,fun n => ?_⟩
    obtain ⟨hor,hpo,hne⟩ := hs.2 n
    obtain ⟨hop,_,_⟩ := hs.2 s.pos
    cases hcmd : cmd.2 with
    | move d =>
      have hw : ins.write = s.cell s.pos := by dsimp [ins]; rw [hcmd,move_write]
      have hp := move_position s.state.1 d cmd.1 (s.cell s.pos) s.pos hop
      change _ = _ at hp
      have hcelt : t.cell = s.cell := by dsimp [t]; rw [hw,Function.update_eq_self]
      have hpos : position t.state.1 t.pos = position s.state.1 s.pos +
          (match d with | .left => -1 | .right => 1) := by cases d <;> simpa only [t,ins,hcmd] using hp
      change (t.cell n).origin = _ ∧ (t.cell n).pos = _ ∧ (t.cell n).neg = _
      rw [hcelt]
      refine ⟨hor,?_,?_⟩
      · rw [hpos]
        cases d <;> simp only [Tape.move_left_nth,Tape.move_right_nth] <;>
          convert hpo using 1 <;> congr 1 <;> omega
      · rw [hpos]
        cases d <;> simp only [Tape.move_left_nth,Tape.move_right_nth] <;>
          convert hne using 1 <;> congr 1 <;> omega
    | write b =>
      cases hd : s.state.1 <;>
        simp only [t,ins,hcmd,command,hd,position]
      · by_cases hn : n = s.pos
        · subst n
          simp only [Function.update_self]
          refine ⟨hop,?_,?_⟩
          · simp [Tape.write]
          · rw [Tape.write_nth,ite_eq_right (by omega)]
            simpa only [hd,position] using hne
        · rw [Function.update_of_ne hn]
          refine ⟨hor,?_,?_⟩
          · rw [Tape.write_nth,ite_eq_right (by omega)]
            simpa only [hd,position] using hpo
          · rw [Tape.write_nth,ite_eq_right (by omega)]
            simpa only [hd,position] using hne
      · by_cases hn : n = s.pos
        · subst n
          simp only [Function.update_self]
          refine ⟨hop,?_,?_⟩
          · rw [Tape.write_nth,ite_eq_right (by omega)]
            simpa only [hd,position] using hpo
          · simp [Tape.write]
        · rw [Function.update_of_ne hn]
          refine ⟨hor,?_,?_⟩
          · rw [Tape.write_nth,ite_eq_right (by omega)]
            simpa only [hd,position] using hpo
          · rw [Tape.write_nth,ite_eq_right (by omega)]
            simpa only [hd,position] using hne
  · simp only [OneSided.step,machine,hs.1,read_head hs,hc,Option.map_some]
    rfl

 theorem respects (M : TM0.Machine Γ Λ) (start : Λ) :
    StateTransition.Respects (TM0.step M) (OneSided.step (machine M start)) Rel := by
  intro c s hs
  cases hc : M c.q c.Tape.head with
  | none => simp only [TM0.step,hc,Option.map_none,OneSided.step,machine,hs.1,read_head hs]
  | some cmd =>
    simp only [TM0.step,hc,Option.map_some]
    obtain ⟨t,ht,hst⟩ := step_rel M start hs hc
    exact ⟨t,ht,TransGen.single hst⟩

end FiniteAlgebraicEnvelopes.MachineRealization.TapeFold

namespace FiniteAlgebraicEnvelopes.MachineRealization.TapeSafety
open Turing
variable {K : Type} {Γ : K → Type} {Λ σ : Type}

/-- Every writing subinstruction preserves the bottom track. -/
def Safe : TM1.Stmt (TM2to1.Γ' K Γ) Λ σ → Prop
  | .move _ q => Safe q
  | .write f q => (∀ a v, (f a v).1 = a.1) ∧ Safe q
  | .load _ q => Safe q
  | .branch _ q r => Safe q ∧ Safe r
  | .goto _ => True
  | .halt => True

theorem safe_stAct [DecidableEq K] {k : K}
    {q : TM1.Stmt (TM2to1.Γ' K Γ) (TM2to1.Λ' K Γ Λ σ) σ} (hq : Safe q)
    (a : TM2to1.StAct K Γ σ k) : Safe (TM2to1.trStAct q a) := by
  cases a <;> simp [TM2to1.trStAct,Safe,hq]

theorem safe_normal (q : TM2.Stmt Γ Λ σ) : Safe (TM2to1.trNormal q) := by
  induction q <;> simp_all [TM2to1.trNormal,Safe]

theorem safe_tr [DecidableEq K] (M : Λ → TM2.Stmt Γ Λ σ) (q : TM2to1.Λ' K Γ Λ σ) :
    Safe (TM2to1.tr M q) := by
  cases q with
  | normal q => exact safe_normal _
  | go k a q =>
      change Safe (TM2to1.trStAct (.goto fun _ _ => .ret q) a) ∧ True
      exact ⟨safe_stAct (q := .goto fun _ _ => .ret q) trivial a,trivial⟩
  | ret q => simp [TM2to1.tr,Safe,safe_normal]

theorem safe_sub {q r : TM1.Stmt (TM2to1.Γ' K Γ) Λ σ}
    (h : q ∈ TM1.stmts₁ r) (hr : Safe r) : Safe q := by
  classical
  induction r with
    simp only [TM1.stmts₁,Safe,Finset.mem_insert,Finset.mem_union,Finset.mem_singleton] at h hr
  | move d r ih => rcases h with rfl | h; exact hr; exact ih h hr
  | write f r ih => rcases h with rfl | h; exact hr; exact ih h hr.2
  | load f r ih => rcases h with rfl | h; exact hr; exact ih h hr
  | branch p r s ihr ihs => rcases h with rfl | h | h; exact hr; exact ihr h hr.1; exact ihs h hr.2
  | goto l => subst q; trivial
  | halt => subst q; trivial

theorem safe_stmts (M : Λ → TM1.Stmt (TM2to1.Γ' K Γ) Λ σ) (B : Finset Λ)
    (hm : ∀ q, Safe (M q)) {q : TM1.Stmt (TM2to1.Γ' K Γ) Λ σ}
    (hq : some q ∈ TM1.stmts M B) : Safe q := by
  classical
  simp only [TM1.stmts,Finset.mem_insertNone,Option.mem_def,Option.some.injEq,forall_eq',Finset.mem_biUnion] at hq
  obtain ⟨l,_,hl⟩ := hq
  exact safe_sub hl (hm l)

theorem trAux_write (M : Λ → TM1.Stmt (TM2to1.Γ' K Γ) Λ σ)
    (a : TM2to1.Γ' K Γ) (q : TM1.Stmt (TM2to1.Γ' K Γ) Λ σ) (v : σ)
    (hq : Safe q) (b : TM2to1.Γ' K Γ)
    (he : (TM1to0.trAux M a q v).2 = .write b) : b.1 = a.1 := by
  induction q generalizing v with
  | move d q ih => cases he
  | write f q ih => cases he; exact hq.1 a v
  | load f q ih => exact ih _ hq he
  | branch p q r ihq ihr =>
      cases hp : p a v <;> simp only [TM1to0.trAux,hp,Bool.cond_false,Bool.cond_true] at he
      · exact ihr _ hq.2 he
      · exact ihq _ hq.1 he
  | goto l => cases he; rfl
  | halt => cases he; rfl

/-- A machine preserves the distinguished bottom marker on every write. -/
def Preserves {L : Type*} [Inhabited L] (M : TM0.Machine (TM2to1.Γ' K Γ) L) : Prop :=
  ∀ q a q' b, M q a = some (q',.write b) → b.1 = a.1

theorem finite_preserves [Inhabited Λ] [Inhabited σ] [Fintype σ]
    (M : Λ → TM1.Stmt (TM2to1.Γ' K Γ) Λ σ) (B : Finset Λ)
    (hB : TM1.Supports M B) (hm : ∀ q, Safe (M q))
    [Inhabited {l // l ∈ TM1to0.trStmts M B}] :
    Preserves (FiniteTM0.machine (TM1to0.tr M) (TM1to0.trStmts M B) (TM1to0.tr_supports M hB)) := by
  classical
  intro q a q' b he
  have hq := q.property
  rcases q with ⟨⟨q,v⟩,hq'⟩
  cases q with
  | none => simp [FiniteTM0.machine,TM1to0.tr] at he
  | some q =>
    have hqm : some q ∈ TM1.stmts M B := (Finset.mem_product.mp hq').1
    have hs := safe_stmts M B hm hqm
    have hx : (TM1to0.trAux M a q v).2 = .write b := by
      have := congrArg (Option.map (fun (x : {l // l ∈ TM1to0.trStmts M B} × TM0.Stmt _) => x.2)) he
      simpa [FiniteTM0.machine,TM1to0.tr] using this
    exact trAux_write M a q v hs b hx

end FiniteAlgebraicEnvelopes.MachineRealization.TapeSafety

namespace FiniteAlgebraicEnvelopes.MachineRealization
open Turing
namespace WordEvaluator
open Turing.PartrecToTM2 StackLift RawTM StackTape
variable {S : Type} [Fintype S] [Primcodable S]
 theorem exists_safe_tape {f : List S →. List S} (hf : Partrec f) :
   ∃ (Λ : Type) (_ : Fintype Λ) (_ : Inhabited Λ)
     (M : TM0.Machine (TM2to1.Γ' K' (fun _ => Symbol S)) Λ) (start stop : Λ),
     TapeSafety.Preserves M ∧ ∀ w, StateTransition.eval (TM0.step M) ⟨start,tape w⟩ =
       (f w).map (fun out => ⟨stop,tape out⟩) := by
  classical
  obtain ⟨Λ,hΛ,M,start,hM⟩ := exists_raw hf
  let : Fintype Λ := hΛ
  let : Inhabited Λ := ⟨start⟩
  let N := TM2to1.tr M
  let P := TM1to0.tr N
  let B := TM2to1.trSupp M Finset.univ
  have hU : TM2.Supports M Finset.univ := by
    refine ⟨Finset.mem_univ _,fun q _ => ?_⟩
    induction M q <;> simp_all [TM2.SupportsStmt]
  have hB : TM1.Supports N B := TM2to1.tr_supports M hU
  let C := TM1to0.trStmts N B
  have hC : TM0.Supports P (C : Set _) := TM1to0.tr_supports N hB
  let : Inhabited {l // l ∈ C} := ⟨⟨default,hC.1⟩⟩
  have hs : (none,none) ∈ C := by
    change (none,none) ∈ (TM1.stmts N B) ×ˢ (Finset.univ : Finset (Store S))
    exact Finset.mem_product.mpr ⟨Finset.none_mem_insertNone,Finset.mem_univ _⟩
  refine ⟨{l // l ∈ C},inferInstance,inferInstance,FiniteTM0.machine P C hC,default,⟨(none,none),hs⟩,TapeSafety.finite_preserves N B hB (TapeSafety.safe_tr M),fun w => ?_⟩
  apply part_map_injective (FiniteTM0.embed_injective C)
  rw [←FiniteTM0.eval_embed P C hC]
  change StateTransition.eval (TM0.step P) (TM1to0.trCfg N ⟨some (.normal start),none,tape w⟩) = _
  rw [eval_post M start hM]
  simp only [Part.map_map]
  rfl

end WordEvaluator
end FiniteAlgebraicEnvelopes.MachineRealization

namespace FiniteAlgebraicEnvelopes.MachineRealization.TapeFold
open Turing Relation Compiler.Simulator
variable {K : Type} {Γ : K → Type} {Λ : Type} [Inhabited Λ]

 def Marked (s : OneSided.Cfg (Cell (TM2to1.Γ' K Γ)) (Side × Λ)) : Prop :=
  ∀ n, (s.cell n).pos.1 = decide (n=0) ∧ (s.cell n).neg.1 = false

 theorem marked_step (M : TM0.Machine (TM2to1.Γ' K Γ) Λ) (start : Λ)
    (hM : TapeSafety.Preserves M) {s t : OneSided.Cfg (Cell (TM2to1.Γ' K Γ)) (Side × Λ)}
    (hs : Marked s) (hst : OneSided.step (machine M start) s = some t) : Marked t := by
  unfold OneSided.step machine at hst
  cases hc : M s.state.2 (read s.state.1 (s.cell s.pos)) with
  | none => simp only [hc,Option.map_none] at hst; cases hst
  | some cmd =>
    simp only [hc,Option.map_some,Option.some.injEq] at hst
    subst t
    intro n
    dsimp only [OneSided.Cfg.cell]
    by_cases hn : n = s.pos
    · subst n
      rw [Function.update_self]
      cases hd : cmd.2 with
      | move d => simpa only [move_write] using hs s.pos
      | write b =>
        have hp := hM s.state.2 (read s.state.1 (s.cell s.pos)) cmd.1 b (by rw [←hd]; exact hc)
        cases he : s.state.1 <;> simp only [he,read] at hp
        · exact ⟨hp.trans (hs s.pos).1,(hs s.pos).2⟩
        · exact ⟨(hs s.pos).1,hp.trans (hs s.pos).2⟩
    · rw [Function.update_of_ne hn]
      exact hs n

 theorem marked_run (M : TM0.Machine (TM2to1.Γ' K Γ) Λ) (start : Λ)
    (hM : TapeSafety.Preserves M) {s t : OneSided.Cfg (Cell (TM2to1.Γ' K Γ)) (Side × Λ)}
    (hs : Marked s) (hst : ReflTransGen (fun a b => OneSided.step (machine M start) a = some b) s t) : Marked t := by
  induction hst with
  | refl => exact hs
  | tail _ h ih => exact marked_step M start hM ih h

end FiniteAlgebraicEnvelopes.MachineRealization.TapeFold

namespace FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral

section
open Turing Relation Compiler.Simulator TapeFold Turing.PartrecToTM2 StackLift RawTM StackTape
variable {S : Type} {Λ : Type} [Inhabited Λ]
abbrev Gamma (S : Type) := Cell (TM2to1.Γ' K' (fun _ => Symbol S))

theorem cell_ext (a b : Cell (TM2to1.Γ' K' (fun _ => Symbol S)))
    (ho : a.origin=b.origin) (hp : a.pos=b.pos) (hn : a.neg=b.neg) : a=b := by
  cases a; cases b; cases ho; cases hp; cases hn; rfl

def blank : Gamma S := ⟨false,default,default⟩
def input (a : S) : Gamma S := ⟨false,(false,slice a),default⟩
def raw (w : List S) : ℕ → Gamma S := Stream'.appendStream' (w.map input) (Stream'.const blank)
def canon (q : Λ) (w : List S) : OneSided.Cfg (Gamma S) (Side × Λ) :=
  ⟨(.pos,q),0,fun n => ⟨decide (n=0),(tape w).nth n,(tape w).nth (-(n+1:ℤ))⟩⟩

omit [Inhabited Λ] in
theorem canon_rel (q : Λ) (w : List S) : Rel (⟨q,tape w⟩ : TM0.Cfg _ _) (canon q w) := by
  refine ⟨rfl,fun n => ?_⟩
  simp [canon,position]

theorem tape_neg (w : List S) (n : ℕ) : (tape w).nth (-(n+1:ℤ)) = default := by
  change ListBlank.nth (∅ : ListBlank _) n = default
  rfl

theorem tape_fst (w : List S) (n : ℕ) : ((tape w).nth n).1 = decide (n=0) := by
  rw [tape,Tape.mk'_nth_nat]
  cases n with
  | zero => simpa only [ListBlank.nth_zero,decide_true] using TM2to1.addBottom_head_fst (stackList w)
  | succ n => exact TM2to1.addBottom_nth_succ_fst _ n

omit [Inhabited Λ] in
theorem canon_marked (q : Λ) (w : List S) : Marked (canon q w) := by
  intro n
  exact ⟨tape_fst w n,congrArg Prod.fst (tape_neg w n)⟩

theorem raw_cell (w : List S) (n : ℕ) : raw w n = ⟨false,(false,(stackList w).nth n),default⟩ := by
  induction w generalizing n with
  | nil => simp [raw,blank,stackList,ListBlank.nth_mk]; rfl
  | cons a w ih =>
    cases n with
    | zero => rfl
    | succ n => simpa only [raw,List.map_cons,Stream'.appendStream',Stream'.cons,stackList,ListBlank.nth_mk,List.getI_cons_succ] using ih n

def mark (c : Gamma S) : Gamma S := ⟨true,(true,c.pos.2),c.neg⟩
def clear (c : Gamma S) : Gamma S := ⟨false,(false,c.pos.2),c.neg⟩

omit [Inhabited Λ] in
theorem canon_cells (q : Λ) (w : List S) : (canon q w).cell = Function.update (raw w) 0 (mark (raw w 0)) := by
  funext n
  have hh : (canon q w).cell n = ⟨decide (n=0),(decide (n=0),(stackList w).nth n),default⟩ := by
    apply cell_ext
    · rfl
    · exact Prod.ext (tape_fst w n) (by
        change ((tape w).nth (n:ℤ)).2 = _
        rw [tape,Tape.mk'_nth_nat]
        exact TM2to1.addBottom_nth_snd (stackList w) n)
    · exact tape_neg w n
  rw [hh]
  by_cases hn : n=0
  · subst n
    rw [Function.update_self,raw_cell]
    rfl
  · rw [Function.update_of_ne hn,raw_cell]
    simp only [hn,decide_false]

omit [Inhabited Λ] in
theorem canon_clear (q : Λ) (w : List S) :
    Function.update (canon q w).cell 0 (clear ((canon q w).cell 0)) = raw w := by
  rw [canon_cells]
  simp only [Function.update_self]
  have hh : clear (mark (raw w 0)) = raw w 0 := by rw [raw_cell]; rfl
  rw [hh,Function.update_idem,Function.update_eq_self]

omit [Inhabited Λ] in
theorem rel_canon_unique {s : OneSided.Cfg (Gamma S) (Side × Λ)}
    (q : Λ) (w : List S) (hr : Rel (⟨q,tape w⟩ : TM0.Cfg _ _) s) (hm : Marked s) : s = canon q w := by
  have hh := congrArg Prod.fst (read_head hr)
  have hb : (tape w).head.1 = true := TM2to1.addBottom_head_fst _
  rw [hb] at hh
  have hp : s.state.1 = .pos ∧ s.pos = 0 := by
    cases hd : s.state.1 with
    | pos =>
      simp only [hd,TapeFold.read] at hh
      rw [(hm s.pos).1] at hh
      exact ⟨rfl,of_decide_eq_true hh⟩
    | neg => simp only [hd,TapeFold.read,(hm s.pos).2] at hh; cases hh
  rcases s with ⟨⟨d,l⟩,p,c⟩
  obtain ⟨rfl,rfl⟩ := hp
  obtain ⟨rfl,hc⟩ := hr
  congr 1
  funext n
  obtain ⟨ho,hp,hn⟩ := hc n
  apply cell_ext
  · exact ho
  · simpa only [canon,position,Int.natCast_zero,sub_zero] using hp
  · simpa only [canon,position,Int.natCast_zero,sub_zero] using hn

end

open Turing Relation Compiler.Simulator TapeFold Turing.PartrecToTM2 StackLift RawTM StackTape
variable {S Λ : Type} [Inhabited Λ]

theorem folded_eval (M : TM0.Machine (TM2to1.Γ' K' (fun _ => Symbol S)) Λ)
    (start stop : Λ) (hm : TapeSafety.Preserves M) {f : List S →. List S}
    (hM : ∀ w, StateTransition.eval (TM0.step M) ⟨start,tape w⟩ =
      (f w).map (fun out => ⟨stop,tape out⟩)) (w : List S) :
    StateTransition.eval (OneSided.step (TapeFold.machine M start)) (canon start w) =
      (f w).map (canon stop) := by
  apply Part.ext
  intro s
  constructor
  · intro hs
    obtain ⟨c,hc,hce⟩ := StateTransition.tr_eval_rev (TapeFold.respects M start) (canon_rel start w) hs
    rw [hM] at hce
    obtain ⟨out,hout,rfl⟩ := (Part.mem_map_iff _).mp hce
    have hmarked := marked_run M start hm (canon_marked start w) (StateTransition.mem_eval.mp hs).1
    rw [rel_canon_unique stop out hc hmarked]
    exact Part.mem_map _ hout
  · intro hs
    obtain ⟨out,hout,rfl⟩ := (Part.mem_map_iff _).mp hs
    have hb : (⟨stop,tape out⟩ : TM0.Cfg _ _) ∈ StateTransition.eval (TM0.step M) ⟨start,tape w⟩ := by
      rw [hM]; exact Part.mem_map _ hout
    obtain ⟨s,hs,hse⟩ := StateTransition.tr_eval (TapeFold.respects M start) (canon_rel start w) hb
    have hmarked := marked_run M start hm (canon_marked start w) (StateTransition.mem_eval.mp hse).1
    exact rel_canon_unique stop out hs hmarked ▸ hse

end FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral

namespace FiniteAlgebraicEnvelopes.MachineRealization.After
open Relation StateTransition
variable {α β : Type*} (f : α → Option α) (g : β → Option β) (lift finish : α → β)
variable (hs : ∀ a, g (lift a) = (f a).elim (some (finish a)) (fun b => some (lift b)))
variable (hf : ∀ a, g (finish a) = none)
include hs hf

theorem path_cases {a : α} {z : β} (h : Reaches g (lift a) z) :
    (∃ b, Reaches f a b ∧ z=lift b) ∨ (∃ b, b ∈ eval f a ∧ z=finish b) := by
  induction h with
  | refl => exact Or.inl ⟨a,.refl,rfl⟩
  | @tail z z' _ hz ih =>
    change g z = some z' at hz
    rcases ih with ⟨b,hb,rfl⟩ | ⟨b,hb,rfl⟩
    · rw [hs] at hz
      cases hc : f b with
      | none =>
        simp only [hc,Option.elim_none,Option.some.injEq] at hz
        exact Or.inr ⟨b,mem_eval.mpr ⟨hb,hc⟩,hz.symm⟩
      | some c =>
        simp only [hc,Option.elim_some,Option.some.injEq] at hz
        exact Or.inl ⟨c,hb.tail hc,hz.symm⟩
    · rw [hf] at hz; cases hz

omit hf in
theorem lift_reaches {a b : α} (h : Reaches f a b) : Reaches g (lift a) (lift b) := by
  induction h with
  | refl => exact .refl
  | tail _ hc ih => exact ih.tail (by rw [hs,hc]; rfl)

theorem eval_lift (a : α) : eval g (lift a) = (eval f a).map finish := by
  apply Part.ext
  intro z
  constructor
  · intro hz
    obtain ⟨hp,hz⟩ := mem_eval.mp hz
    rcases path_cases f g lift finish hs hf hp with ⟨b,_,rfl⟩ | ⟨b,hb,rfl⟩
    · rw [hs] at hz
      cases hc : f b <;> simp [hc] at hz
    · exact Part.mem_map _ hb
  · intro hz
    obtain ⟨b,hb,rfl⟩ := (Part.mem_map_iff _).mp hz
    obtain ⟨hr,hb⟩ := mem_eval.mp hb
    apply mem_eval.mpr
    exact ⟨(lift_reaches f g lift finish hs hr).tail (by rw [hs,hb]; rfl),hf b⟩

end FiniteAlgebraicEnvelopes.MachineRealization.After

namespace FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral

section
open Turing Relation Compiler.Simulator TapeFold Turing.PartrecToTM2 StackLift RawTM StackTape
variable {S Λ : Type} [Inhabited Λ]
abbrev State (Λ : Type) := Option (Option (Side × Λ))

def wrapper (M : TM0.Machine (TM2to1.Γ' K' (fun _ => Symbol S)) Λ) (start : Λ) :
    Machine (State Λ) (Gamma S) :=
  ⟨none,fun q a => match q with
    | none => some ⟨some (some (.pos,start)),mark a,.stay⟩
    | some none => none
    | some (some q) => match (TapeFold.machine M start).transition q a with
      | none => some ⟨some none,clear a,.stay⟩
      | some c => some ⟨some (some c.state),c.write,c.move⟩⟩

def lift (s : OneSided.Cfg (Gamma S) (Side × Λ)) : OneSided.Cfg (Gamma S) (State Λ) :=
  ⟨some (some s.state),s.pos,s.cell⟩
def finish (s : OneSided.Cfg (Gamma S) (Side × Λ)) : OneSided.Cfg (Gamma S) (State Λ) :=
  ⟨some none,s.pos,Function.update s.cell s.pos (clear (s.cell s.pos))⟩
def initial (w : List S) : OneSided.Cfg (Gamma S) (State Λ) := ⟨none,0,raw w⟩
def final (w : List S) : OneSided.Cfg (Gamma S) (State Λ) := ⟨some none,0,raw w⟩

variable (M : TM0.Machine (TM2to1.Γ' K' (fun _ => Symbol S)) Λ) (start : Λ)
theorem wrapper_lift (s : OneSided.Cfg (Gamma S) (Side × Λ)) :
    OneSided.step (wrapper M start) (lift s) =
      (OneSided.step (TapeFold.machine M start) s).elim (some (finish s)) (fun t => some (lift t)) := by
  simp only [OneSided.step,lift,wrapper]
  cases hc : (TapeFold.machine M start).transition s.state (s.cell s.pos) with
  | none => rfl
  | some cmd => cases cmd.move <;> rfl

theorem wrapper_finish (s : OneSided.Cfg (Gamma S) (Side × Λ)) :
    OneSided.step (wrapper M start) (finish s) = none := rfl

theorem wrapper_initial (w : List S) : OneSided.step (wrapper M start) (initial w) = some (lift (canon start w)) := by
  simp only [OneSided.step,wrapper,initial,Option.map_some,lift,canon]
  congr 2
  exact (canon_cells start w).symm

omit [Inhabited Λ] in
theorem finish_canon (q : Λ) (w : List S) : finish (canon q w) = final (Λ := Λ) w := by
  simp only [finish,canon,final]
  congr 1
  exact canon_clear q w

theorem wrapper_eval (stop : Λ) (hm : TapeSafety.Preserves M) {f : List S →. List S}
    (hM : ∀ w, StateTransition.eval (TM0.step M) ⟨start,tape w⟩ =
      (f w).map (fun out => ⟨stop,tape out⟩)) (w : List S) :
    StateTransition.eval (OneSided.step (wrapper M start)) (initial w) = (f w).map (final (Λ := Λ)) := by
  rw [StateTransition.reaches_eval (ReflTransGen.single (wrapper_initial M start w)),
    After.eval_lift (OneSided.step (TapeFold.machine M start)) (OneSided.step (wrapper M start)) lift finish
      (wrapper_lift M start) (wrapper_finish M start),folded_eval M start stop hm hM]
  simp only [Part.map_map,Function.comp_def,finish_canon]

end

open Turing Compiler.Simulator Turing.PartrecToTM2 StackLift StackTape
variable {S : Type} [DecidableEq S]

instance : Fintype K' := ⟨{.main,.rev,.aux,.stack},by intro k; cases k <;> simp⟩


end FiniteAlgebraicEnvelopes.MachineRealization.FoldLiteral
end OAI
