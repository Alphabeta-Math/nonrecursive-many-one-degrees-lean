import Proofs.PriorityRequirements

open PriorityCodedTrace

example (row : Rows) (U : UpperSearch) (L : LowerSearch) (s e m : Nat) :
    (Finset.equivBitIndices.symm (restraints row U L s e)).testBit m = true ↔
      m ∈ {a : Nat | ∃ j, 2 * j + 1 < 2 * e ∧ marker row U L s (2 * e) j = some a} := by
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, ← Finset.equivBitIndices_apply,
    Equiv.apply_symm_apply]
  exact memMarkerSet _ _ _

#check Option.isSome_iff_exists
#check Nat.mem_bitIndices
#check Set.mem_ofPred_eq
