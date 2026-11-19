by
  intro φ V stage hφ hsurj hV _ hstage hmono hunion K
  -- Cintioli, arXiv:2609.00419v1, §4, pp. 8–10.
  -- https://arxiv.org/pdf/2609.00419v1#page=8
  -- Use the fixed computable order by pair codes and allow every number as
  -- a marker. The trace is selected before the hypotheses on A are used.
  -- Family coverage is used when applying these requirements to a newly
  -- constructed family. This endpoint verifies each family in the given list.
  let before (q r : ℕ × ℕ) : Prop := Nat.pair q.1 q.2 < Nat.pair r.1 r.2
  have horder : IsStrictTotalOrder (ℕ × ℕ) before :=
    Nat.pairEquiv.injective.isStrictTotalOrder_onFun (· < ·)
  have hpairCode : Primrec (fun q : ℕ × ℕ => Nat.pair q.1 q.2) :=
    Primrec₂.natPair.comp Primrec.fst Primrec.snd
  have hbefore : ComputablePred (fun p : (ℕ × ℕ) × (ℕ × ℕ) => before p.1 p.2) :=
    (Primrec.nat_lt.comp (hpairCode.comp Primrec.fst) (hpairCode.comp Primrec.snd)).computablePred
  have hM : Nat.RecursiveIn
      {(by classical exact fun n => Part.some (if n ∈ PriorityRequirements.haltingOracle φ then 1 else 0))}
      (fun m : ℕ => Part.some (@ite ℕ (m ∈ (Set.univ : Set ℕ)) (Classical.propDecidable _) 1 0)) := by
    have hconst : Nat.RecursiveIn
        {(by classical exact fun n => Part.some (if n ∈ PriorityRequirements.haltingOracle φ then 1 else 0))}
        (fun _ => Part.some 1) :=
      RecursiveIn.iff_nat.mp (Computable.const 1).computableIn
    refine hconst.of_eq fun m => ?_
    simp
  obtain ⟨T, hce, hsigma⟩ :=
    PriorityRequirements.existsEffectiveTrace φ stage Set.univ before
      hφ hsurj hstage horder hbefore hM
  exact PriorityRequirements.finish φ V stage hφ hV hmono hunion T hce hsigma
