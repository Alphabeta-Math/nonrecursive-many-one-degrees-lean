import Proofs.ManyOneReducibilityOnNat
import Proofs.ComputablyEnumerableSet
import Proofs.HaltingSigmaOneCompleteness
import Proofs.PriorityRequirements

namespace MaslovaRestrictedTraceCheck
open HaltingSigmaOneCompleteness

theorem re_of_degree_has_ce (A : Set ℕ) :
    let encode (n : ℕ) := List.replicate n false
    let decode (w : List Bool) :=
      if w = encode (List.length w) then some (List.length w) else none
    let ce : Set ℕ → Prop :=
      ComputablyEnumerableSet encode decode (List.replicate_left_injective false)
        (fun n => by simp [decode, encode])
        (fun w hw => ite_eq_right (fun h => hw ⟨List.length w, h.symm⟩))
    let d : Set (Set ℕ) :=
      {X | ManyOneReducibilityOnNat X A ∧ ManyOneReducibilityOnNat A X}
    (∃ X ∈ d, ce X) → REPred (fun n : ℕ => n ∈ A) := by
  intro encode decode ce d hce
  obtain ⟨X, ⟨_, hAX⟩, hX⟩ := hce
  have hXre : REPred (fun x : ℕ => x ∈ X) :=
    (ComputablyEnumerableSet.nat_rePred_iff false X).2 hX
  obtain ⟨f, hf, hmem⟩ := hAX
  have hp : REPred (fun x : ℕ => f x ∈ X) := Partrec.comp hXre hf
  exact hp.of_eq fun x => (hmem x).symm

theorem complementRecursiveIn (A : Set ℕ) (hA : REPred (fun x : ℕ => x ∈ A)) :
    Nat.RecursiveIn
      {(by classical exact fun n : ℕ => Part.some (if n ∈ PriorityRequirements.haltingOracle canonicalNumbering then 1 else 0))}
      (fun x : ℕ => Part.some (@ite ℕ (x ∈ Aᶜ) (Classical.propDecidable _) 1 0)) := by
  classical
  obtain ⟨c, hc⟩ := (ComputablyEnumerableSet.nat_rePred_iff_exists_code A).1 hA
  let e : ℕ := Encodable.encode c
  let K := PriorityRequirements.haltingOracle canonicalNumbering
  let answer (n : ℕ) : Part ℕ := Part.some (if n ∈ K then 1 else 0)
  change Nat.RecursiveIn {answer} _
  have hquery (x : ℕ) : Nat.pair e x ∈ K ↔ x ∈ A := by
    rw [PriorityRequirements.pair_mem_haltingOracle]
    simpa only [canonicalNumbering, e, Denumerable.ofNat_encode] using hc x
  have hpair : Nat.RecursiveIn {answer} (fun x => Part.some (Nat.pair e x)) :=
    RecursiveIn.iff_nat.mp
      ((Primrec₂.natPair.comp (Primrec.const e) Primrec.id).to_comp.computableIn)
  have hanswer : Nat.RecursiveIn {answer} answer :=
    Nat.RecursiveIn.oracle answer (Set.mem_singleton _)
  have hswap : Nat.RecursiveIn {answer} (fun b => Part.some (1 - b)) :=
    RecursiveIn.iff_nat.mp
      ((Primrec.nat_sub.comp (Primrec.const 1) Primrec.id).to_comp.computableIn)
  refine (hswap.comp (hanswer.comp hpair)).of_eq fun x => ?_
  by_cases hx : x ∈ A
  · have hyes := (hquery x).2 hx
    simp [answer, hyes, hx]
  · have hno := (hquery x).not.2 hx
    simp [answer, hno, hx]

theorem existsRestrictedTrace (A : Set ℕ) (hA : REPred (fun x : ℕ => x ∈ A)) :
    ∃ T : PriorityRequirements.VerificationTrace canonicalNumbering rowAt Aᶜ,
      (RelativeComputabilityAndEnumerability
        (PriorityRequirements.haltingOracle canonicalNumbering)).2.1 T.output ∧
      {xs : Fin 1 → ℕ | xs 0 ∈ T.output} ∈
        (ArithmeticalHierarchyLevels 2 1 (Nat.le_succ 1)).1 ∧
      {xs : Fin 1 → ℕ | xs 0 ∈ T.outputᶜ} ∈
        (ArithmeticalHierarchyLevels 2 1 (Nat.le_succ 1)).2.1 := by
  let before (q r : ℕ × ℕ) : Prop := Nat.pair q.1 q.2 < Nat.pair r.1 r.2
  have horder : IsStrictTotalOrder (ℕ × ℕ) before :=
    Nat.pairEquiv.injective.isStrictTotalOrder_onFun (· < ·)
  have hpairCode : Primrec (fun q : ℕ × ℕ => Nat.pair q.1 q.2) :=
    Primrec₂.natPair.comp Primrec.fst Primrec.snd
  have hbefore : ComputablePred (fun p : (ℕ × ℕ) × (ℕ × ℕ) => before p.1 p.2) :=
    (Primrec.nat_lt.comp (hpairCode.comp Primrec.fst)
      (hpairCode.comp Primrec.snd)).computablePred
  obtain ⟨_, hsurj, hφ, _⟩ := canonicalNumbering_acceptable
  obtain ⟨T, hce, hsigma⟩ :=
    PriorityRequirements.existsEffectiveTrace canonicalNumbering rowAt Aᶜ before
      hφ hsurj computable_rowAt_code horder hbefore (complementRecursiveIn A hA)
  refine ⟨T, hce, hsigma, ?_⟩
  change ({xs : Fin 1 → ℕ | xs 0 ∈ T.output}ᶜᶜ : Set (Fin 1 → ℕ)) ∈
    (ArithmeticalHierarchyLevels 2 1 (Nat.le_succ 1)).1
  simpa using hsigma

#print axioms re_of_degree_has_ce
#print axioms complementRecursiveIn
#print axioms existsRestrictedTrace
end MaslovaRestrictedTraceCheck
