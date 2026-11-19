import Mathlib



set_option maxHeartbeats 2000000

theorem ComputableInjectiveSection : (∀ (p : _root_.Nat → _root_.Nat),
  _root_.Computable p → _root_.Function.Surjective p →
    ∃ s : _root_.Nat → _root_.Nat,
      _root_.Computable s ∧ _root_.Function.Injective s ∧
      (∀ y : _root_.Nat, p (s y) = y) ∧
      (∀ y n : _root_.Nat, p n = y → s y ≤ n)) :=
(by
  -- The article-specific Alphabeta Math portal and defect report return HTTP 404.
  -- There is no verified numbered proof to cite. We follow the unnumbered
  -- proof of Lemma 1 on p. 4 of arXiv:2609.00419v1.
  intro p hp hsurj
  -- For each target y, surjectivity supplies a witness to p n = y.
  have hpreimage : ∀ y : Nat, ∃ n : Nat, p n = y := hsurj
  let s (y : Nat) : Nat := Nat.find (hpreimage y)
  -- Computable.find formalizes the article's μ-search. Its test is
  -- computable by composing Nat equality with p and the pair projections.
  have htest : ComputablePred (fun q : Nat × Nat => p q.2 = q.1) :=
    (Primrec.eq.decide.to_comp.comp (hp.comp Computable.snd) Computable.fst).computablePred
  have hs : Computable s :=
    Computable.find (P := fun y n => p n = y) htest hpreimage
  have hsection (y : Nat) : p (s y) = y := Nat.find_spec (hpreimage y)
  refine ⟨s, hs, ?_, hsection, ?_⟩
  · intro y z hyz
    exact (hsection y).symm.trans ((congrArg p hyz).trans (hsection z))
  · -- The translation makes the least-witness convention of μ explicit.
    intro y n hn
    exact Nat.find_min' (hpreimage y) hn)
