import Mathlib
import Proofs.ManyOneReducibilityOnNat
import Proofs.ComputablyEnumerableSet

#check (
let rigid := fun A : _root_.Set _root_.Nat =>
  ∀ f : _root_.Nat → _root_.Nat, _root_.Computable f →
    (∀ n : _root_.Nat, n ∈ A ↔ f n ∈ A) →
    ∃ N : _root_.Nat, ∀ n : _root_.Nat, N ≤ n → f n = n
let finiteOne := fun A B : _root_.Set _root_.Nat =>
  ∃ f : _root_.Nat → _root_.Nat, _root_.Computable f ∧
    (∀ n : _root_.Nat, n ∈ A ↔ f n ∈ B) ∧
    (∀ y : _root_.Nat, _root_.Set.Finite {n : _root_.Nat | f n = y})
let hasAntichain := fun A : _root_.Set _root_.Nat =>
  ∃ B : _root_.Nat → _root_.Set _root_.Nat,
    (∀ i : _root_.Nat,
      _root_.ManyOneReducibilityOnNat (B i) A ∧ _root_.ManyOneReducibilityOnNat A (B i)) ∧
    _root_.Pairwise (fun i j => ¬ finiteOne (B i) (B j) ∧ ¬ finiteOne (B j) (B i))
let asSet := fun a : _root_.Nat → _root_.Bool => {n : _root_.Nat | a n = _root_.Bool.true}
let fairCoin := _root_.MeasureTheory.Measure.infinitePi
  (fun _ : _root_.Nat =>
    _root_.MeasureTheory.Measure.uniformOfFinset (_root_.Finset.univ : _root_.Finset _root_.Bool))
(∀ A : _root_.Set _root_.Nat, rigid A → hasAntichain A) ∧
  fairCoin {a | rigid (asSet a)} = 1 ∧
  _root_.Filter.Eventually (fun a => rigid (asSet a)) (_root_.residual (_root_.Nat → _root_.Bool)) ∧
  _root_.Filter.Eventually (fun a => hasAntichain (asSet a)) (_root_.MeasureTheory.ae fairCoin) ∧
  _root_.Filter.Eventually (fun a => hasAntichain (asSet a)) (_root_.residual (_root_.Nat → _root_.Bool))
)
