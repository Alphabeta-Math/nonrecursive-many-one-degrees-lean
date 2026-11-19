∀ (φ : Nat → Nat → Part Nat)
    (rowAt : Nat → Nat → Nat → Finset Nat)
    (pairBefore : (Nat × Nat) → (Nat × Nat) → Prop)
    (query : Nat → Nat) (M : Set Nat),
  let K : Set Nat := {n | (φ n.unpair.1 n.unpair.2).Dom}
  let oracle : Set (Nat →. Nat) :=
    {(by classical exact fun n => Part.some (if n ∈ K then 1 else 0))}
  Computable (fun p : Nat × Nat × Nat =>
    Finset.equivBitIndices.symm (rowAt p.1 p.2.1 p.2.2)) →
  IsStrictTotalOrder (Nat × Nat) pairBefore →
  ComputablePred (fun p : (Nat × Nat) × (Nat × Nat) => pairBefore p.1 p.2) →
  Computable query →
  (∀ e x t, query (Nat.pair e (Nat.pair x t)) ∉ K ↔
    ∀ r, t ≤ r → rowAt e x r = rowAt e x t) →
  Nat.RecursiveIn oracle (by classical exact fun m => Part.some (if m ∈ M then 1 else 0)) →
  let upperCandidate (e s : Nat) (Z : Finset Nat) (q : Nat × Nat) : Prop :=
    q.1 ≤ s ∧ q.2 ≤ s ∧
    (∀ m ∈ rowAt e q.1 q.2, m ≤ s ∧ m ∉ Z) ∧
    ∀ r, q.2 ≤ r → rowAt e q.1 r = rowAt e q.1 q.2
  let lowerCandidate (e s : Nat) (content active : Finset Nat) (m : Nat) : Prop :=
    m ≤ s ∧ m ∈ M ∧ ¬ (φ e m).Dom ∧ m ∉ content ∧ m ∉ active
  ∃ (upperSearch : Nat → Nat → Finset Nat → Option (Nat × Nat))
    (lowerSearch : Nat → Nat → Finset Nat → Finset Nat → Option Nat),
    Nat.RecursiveIn oracle (fun n =>
      let (e, args) := n.unpair
      let (s, z) := args.unpair
      Part.some (match upperSearch e s (Finset.equivBitIndices z) with
        | none => 0
        | some (x, t) => (Nat.pair x t).succ)) ∧
    Nat.RecursiveIn oracle (fun n =>
      let (e, args) := n.unpair
      let (s, sets) := args.unpair
      let (content, active) := sets.unpair
      Part.some (match lowerSearch e s (Finset.equivBitIndices content)
          (Finset.equivBitIndices active) with
        | none => 0
        | some m => m.succ)) ∧
    (∀ e s Z,
      match upperSearch e s Z with
      | none => ∀ q, ¬ upperCandidate e s Z q
      | some q => upperCandidate e s Z q ∧
          ∀ p, upperCandidate e s Z p → ¬ pairBefore p q) ∧
    (∀ e s content active,
      match lowerSearch e s content active with
      | none => ∀ m, ¬ lowerCandidate e s content active m
      | some m => lowerCandidate e s content active m ∧
          ∀ n, lowerCandidate e s content active n → m ≤ n)
