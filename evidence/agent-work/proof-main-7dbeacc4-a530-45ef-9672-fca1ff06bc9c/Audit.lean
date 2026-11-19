import Compile

#print axioms ComputablyEnumerableSet
#print axioms ComputablyEnumerableSet.computable_replicate
#print axioms ComputablyEnumerableSet.nat_rePred_range
#print axioms ComputablyEnumerableSet.nat_rePred_iff_exists_code
#print axioms ComputablyEnumerableSet.nat_exists_computable_range
#print axioms ComputablyEnumerableSet.nat_rePred_iff

example (A : Set ℕ) :
    let encode (n : Nat) := List.replicate n false
    let decode (w : List Bool) :=
      if w = encode w.length then some w.length else none
    REPred (fun n => n ∈ A) ↔
      ComputablyEnumerableSet encode decode (List.replicate_left_injective false)
        (fun n => by simp [decode, encode])
        (fun w hw => ite_eq_right (fun h => hw ⟨w.length, h.symm⟩)) A :=
  ComputablyEnumerableSet.nat_rePred_iff false A

example (A : Set ℕ) :
    let encode (n : Nat) := List.replicate n true
    let decode (w : List Bool) :=
      if encode w.length = w then some w.length else none
    REPred (fun n => n ∈ A) ↔
      ComputablyEnumerableSet encode decode (List.replicate_left_injective true)
        (fun n => by simp [decode, encode])
        (fun w hw => ite_eq_right (fun h => hw ⟨w.length, h⟩)) A :=
  ComputablyEnumerableSet.nat_rePred_iff true A
