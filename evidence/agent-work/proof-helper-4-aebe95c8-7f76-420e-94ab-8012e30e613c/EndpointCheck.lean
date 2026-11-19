import PriorityRequirementsDraft

example : (∀ (φ : _root_.Nat → _root_.Nat → _root_.Part _root_.Nat)
    (V : _root_.Nat → _root_.Nat → _root_.Set _root_.Nat)
    (stage : _root_.Nat → _root_.Nat → _root_.Nat → _root_.Finset _root_.Nat),
  _root_.Partrec₂ φ →
  (∀ f : _root_.Nat → _root_.Part _root_.Nat,
    _root_.Partrec f → ∃ e : _root_.Nat, φ e = f) →
  _root_.REPred (fun p : _root_.Nat × _root_.Nat × _root_.Nat =>
    p.2.2 ∈ V p.1 p.2.1) →
  (∀ i : _root_.Nat, ∃ e : _root_.Nat, ∀ x y : _root_.Nat,
    y ∈ V e x ↔ _root_.Part.Dom (φ i (_root_.Nat.pair x y))) →
  _root_.Computable (fun p : _root_.Nat × _root_.Nat × _root_.Nat =>
    (_root_.Equiv.symm _root_.Finset.equivBitIndices) (stage p.1 p.2.1 p.2.2)) →
  (∀ e x : _root_.Nat, _root_.Monotone (stage e x)) →
  (∀ e x y : _root_.Nat, y ∈ V e x ↔ ∃ s : _root_.Nat, y ∈ stage e x s) →
  let K : _root_.Set _root_.Nat := {n |
    let (e, x) := _root_.Nat.unpair n
    _root_.Part.Dom (φ e x)}
  let levelTwo := _root_.ArithmeticalHierarchyLevels 2 1 (_root_.Nat.le_succ 1)
  let unary (B : _root_.Set _root_.Nat) : _root_.Set (_root_.Fin 1 → _root_.Nat) :=
    {xs | xs 0 ∈ B}
  let encode (n : _root_.Nat) := _root_.List.replicate n _root_.Bool.true
  let decode (w : _root_.List _root_.Bool) : _root_.Option _root_.Nat :=
    if encode (_root_.List.length w) = w then _root_.Option.some (_root_.List.length w)
    else _root_.Option.none
  let ce : _root_.Set _root_.Nat → Prop :=
    _root_.ComputablyEnumerableSet encode decode
      (_root_.List.replicate_left_injective _root_.Bool.true)
      (fun n => by simp [decode, encode])
      (fun w hw => _root_.ite_eq_right (fun h => hw ⟨_root_.List.length w, h⟩))
  ∃ N : _root_.Set _root_.Nat,
    let P : _root_.Set _root_.Nat := Nᶜ
    (_root_.RelativeComputabilityAndEnumerability K).2.1 N ∧
    unary N ∈ levelTwo.1 ∧
    unary P ∈ levelTwo.2.1 ∧
    ∀ A : _root_.Set _root_.Nat,
      let cyl : _root_.Set _root_.Nat :=
        {z | ∃ x n : _root_.Nat, x ∈ A ∧ z = _root_.Nat.pair x n}
      ¬ _root_.ComputablePred (fun x : _root_.Nat => x ∈ A) →
      ¬ (_root_.OneOneReducible (fun x : _root_.Nat => x ∈ A) (fun x : _root_.Nat => x ∈ cyl) ∧
         _root_.OneOneReducible (fun x : _root_.Nat => x ∈ cyl) (fun x : _root_.Nat => x ∈ A)) →
      ¬ ce A →
      ¬ ce (Aᶜ) →
      let upper (e : _root_.Nat) : Prop :=
        (∀ x y : _root_.Nat, y ∈ V e x → (y ∈ A ↔ x ∈ A)) →
          ∃ x : _root_.Nat, _root_.Set.Finite (V e x) ∧ V e x ⊆ N
      let lower (e : _root_.Nat) : Prop :=
        (∀ x y : _root_.Nat, y ∈ φ e x → x < y ∧ (y ∈ A ↔ x ∈ A)) →
          ∃ m : _root_.Nat, m ∉ N ∪ {x : _root_.Nat | _root_.Part.Dom (φ e x)}
      ∀ p : _root_.Nat, if p % 2 = 0 then upper (p / 2) else lower (p / 2)) :=
  PriorityRequirements

#print axioms PriorityRequirements
