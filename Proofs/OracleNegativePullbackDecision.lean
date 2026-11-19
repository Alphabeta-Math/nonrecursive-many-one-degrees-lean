import Mathlib

import Proofs.RelativeComputabilityAndEnumerability

set_option maxHeartbeats 2000000

/-
Selected declarations adapted from openai/math at 4eaee87548250b2682affda7d05d947c05554bae,
licensed under Apache-2.0. This port collects the needed declarations from
Simulator.lean, Machines.lean and TapeFolding.lean under a local namespace.
It omits the other compiler phases and the general first-blank interface.
https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Computability/FiniteCompiler/Simulator.lean
https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Computability/FiniteCompiler/Machines.lean
https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Computability/FiniteCompiler/TapeFolding.lean
https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/LICENSE

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/

namespace OracleTapeSupplier

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

end OracleTapeSupplier

noncomputable section

namespace OracleNegativePullback
open Relation
open OracleTapeSupplier.OAI.FiniteAlgebraicEnvelopes.Compiler.Simulator (Machine Command Move)
open OracleTapeSupplier.OAI.FiniteAlgebraicEnvelopes.MachineRealization

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
def program : Program (states Q) b := by
  classical
  let : Nonempty Q := ⟨M.initial⟩
  let : Nonempty Γ := ⟨blank⟩
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
  let : Nonempty Q := ⟨M.initial⟩
  simp [program, Function.leftInverse_invFun stateCode_injective (q, true)]

theorem program_query :
    program M stop blank enc (stateCode (stop, false)) = .inr (2, 1) := by
  let : Nonempty Q := ⟨M.initial⟩
  simp [program, Function.leftInverse_invFun stateCode_injective (stop, false)]

theorem program_run {q : Q} (hq : q ≠ stop) (he : Function.Injective enc) {a : Γ}
    {cmd : Command Q Γ} (hcmd : M.transition q a = some cmd) :
    ∃ instr, program M stop blank enc (stateCode (q, false)) = .inl instr ∧
      instr (enc a) = (stateCode (cmd.state, decide (cmd.move = Move.stay)), enc cmd.write, decide (cmd.move ≠ Move.left)) := by
  classical
  let : Nonempty Q := ⟨M.initial⟩
  let : Nonempty Γ := ⟨blank⟩
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
      · rfl
    | right =>
      refine ⟨(stateCode (cmd.state, false), head + 1, tape'), .single ?_, ⟨rfl, ?_, hw⟩⟩
      · simpa [move] using hfirst
      · rfl
    | stay =>
      -- A right move followed by a preserving left move implements stay.
      let tape'' := write (2 : Fin (b + 4)) tape' (head + 1) (tape'.getD (head + 1) 2)
      have hb : step X (program M stop blank enc) (stateCode (cmd.state, true), head + 1, tape')
          (stateCode (cmd.state, false), head, tape'') := by
        refine ⟨stateCode_nonhalting _, ?_⟩
        simp [program_back, tape'']
      refine ⟨(stateCode (cmd.state, false), head, tape''), (ReflTransGen.single ?_).tail hb, ⟨rfl, ?_, ?_⟩⟩
      · simpa [move] using hfirst
      · rfl
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
  simp [symbolCode, symbolIndex]
  rw [Nat.mod_eq_of_lt (by omega)]

@[simp] theorem symbolCode_input (a : Letter) : symbolCode e (FoldLiteral.input a) = letterCode a := by
  apply Fin.ext
  simp only [symbolCode, symbolIndex, input_ne_blank, ite_false, input_injective.eq_iff, letterCode]
  fin_cases a <;> simp
  rw [Nat.mod_eq_of_lt (by omega)]

theorem symbolCode_injective : Function.Injective (symbolCode e) := by
  intro a b h
  have hv := congrArg Fin.val h
  dsimp only [symbolCode, symbolIndex] at hv
  split_ifs at hv <;>
    first
    | omega
    | subst_vars; rfl
    | exact e.injective (Fin.ext (Nat.add_right_cancel hv))

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
    simp [List.getD_eq_getElem?_getD]
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


theorem OracleNegativePullbackDecision : (∀ (X : Set Nat) (f : Nat → Nat), Computable f →
  (RelativeComputabilityAndEnumerability X).1 {n | f n ∉ X}) :=
(by
  open OracleNegativePullback OracleTapeSupplier.OAI.FiniteAlgebraicEnvelopes.MachineRealization in
  -- Alphabeta Math, An oracle computation has a finite query witness, steps
  -- 1.1 and 2.1. Here the run is constructed from total computability, so the
  -- finite query set is the singleton {f n}. simulate_run uses induction over
  -- the finite ordinary run, and decide_with adds its only query.
  -- https://alphabetamath.cc/item/lem-oracle-computation-has-a-finite-query-witness
  --
  -- Cintioli, arXiv:2609.00419 v1, §4, uses a halting-oracle answer to decide
  -- whether a given row ever changes after the specified stage. This lemma
  -- implements the negative branch for any total computable query map.
  -- The article omits the tape implementation. The preprocessor takes the
  -- reviewed delimiter-free input and appends the delimiter only to its
  -- output. The query evaluates the canonical numeral at the origin.
  -- https://arxiv.org/pdf/2609.00419
  --
  -- The reviewed predicate is the Shared Math Library definition. Its
  -- linked ordinary transition relation uses a clamped left move. In the
  -- simulation, a supplier stay uses a preserving right-and-left detour.
  -- https://alphabetamath.cc/item/def-relative-computability-and-enumerability
  -- https://alphabetamath.cc/item/def-one-step-configuration-relation
  --
  -- The article-specific Alphabeta collection and defect report both
  -- returned HTTP 404. The applicable shared proof steps are cited above.
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects
  intro X f hf
  classical
  let g : List Letter →. List Letter := fun w => Part.some (out (f (parse w)))
  have hg : Partrec g := (comp_preprocess hf).partrec
  -- The coordinator's WordEvaluator.exists_machine candidate gives a
  -- first-blank readout. Its underlying exact-configuration lemmas give
  -- the head position and all tape cells needed by the reviewed query.
  obtain ⟨Λ, fintypeΛ, inhabitedΛ, M, start, stop, safe, eval⟩ := WordEvaluator.exists_safe_tape hg
  let : Fintype Λ := fintypeΛ
  let : Inhabited Λ := inhabitedΛ
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
  exact Part.mem_some _)
