import Mathlib



set_option maxHeartbeats 2000000

/- Alphabeta Math, def-sigma-n-pi-n-and-delta-n-sets, Definition. The
   source gives a definition, so it has no numbered proof steps. Fin.elim0
   supplies the empty bound-variable tuple. Fin.cons fixes the next
   coordinate, and the flag changes at each recursive step, beginning
   existentially. PrimrecRel checks primitive recursiveness on the product of
   the free- and bound-variable tuples. The Π class uses set complement on
   that same tuple carrier, and the Δ class uses intersection. The first two
   unfoldings are ∃a and ∃a ∀b, respectively. The article-specific Research
   Portal and its defect report both returned HTTP 404. The shared-library
   definition is available at https://alphabetamath.cc/item/def-sigma-n-pi-n-and-delta-n-sets. -/

noncomputable def ArithmeticalHierarchyLevels : ((n k : Nat) → 1 ≤ n →
  Set (Set (Fin k → Nat)) × Set (Set (Fin k → Nat)) × Set (Set (Fin k → Nat))) :=
(fun n k _ =>
  let quantify : (m : Nat) → Bool → ((Fin m → Nat) → Prop) → Prop :=
    Nat.rec (motive := fun m => Bool → ((Fin m → Nat) → Prop) → Prop)
      (fun _ matrix => matrix Fin.elim0)
      (fun _ ih existential matrix =>
        if existential then
          ∃ y : Nat, ih false (fun ys => matrix (Fin.cons y ys))
        else
          ∀ y : Nat, ih true (fun ys => matrix (Fin.cons y ys)))
  let sigma : Set (Set (Fin k → Nat)) :=
    {A | ∃ R : (Fin k → Nat) → (Fin n → Nat) → Prop,
      PrimrecRel R ∧ ∀ xs : Fin k → Nat, xs ∈ A ↔ quantify n true (R xs)}
  let pi : Set (Set (Fin k → Nat)) := {A | Aᶜ ∈ sigma}
  (sigma, pi, sigma ∩ pi))
