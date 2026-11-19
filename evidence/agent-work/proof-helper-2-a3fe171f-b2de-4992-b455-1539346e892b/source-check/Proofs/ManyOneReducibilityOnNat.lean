import Mathlib



set_option maxHeartbeats 2000000

/- Alphabeta Math, def-computable-many-one-reducibility-interface, ordinary
   natural-number clause, and Cintioli, arXiv:2609.00419v1, §2, p. 2.
   Use each set's membership predicate as an argument to ManyOneReducible.
   At Nat its witness is a total computable function Nat → Nat, and the
   pointwise equivalence has the source membership on the left.
   Verification step 1.1 checks reflexivity and composition of the relation.
   Step 2.1 concerns the bridge to string reductions. The selected endpoint
   is the definition itself, whose unfolding gives the witness and equivalence.
   The shared-library item is available. The article-specific Research Portal
   and its defect report both returned HTTP 404. -/

noncomputable def ManyOneReducibilityOnNat : (_root_.Set _root_.Nat → _root_.Set _root_.Nat → Prop) :=
(fun A B => _root_.ManyOneReducible (fun n : _root_.Nat => n ∈ A) (fun n : _root_.Nat => n ∈ B))
