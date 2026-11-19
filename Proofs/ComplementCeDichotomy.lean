import Mathlib

import Proofs.MaslovaCeDichotomy
import Proofs.ComplementationOrderIsomorphism
import Proofs.ComputablyEnumerableSet

set_option maxHeartbeats 2000000

theorem ComplementCeDichotomy : (let finiteOneReducible (X Y : _root_.Set _root_.Nat) : Prop :=
  ∃ f : _root_.Nat → _root_.Nat, _root_.Computable f ∧
    (∀ y : _root_.Nat, _root_.Set.Finite (_root_.Set.preimage f ({y} : _root_.Set _root_.Nat))) ∧
    (∀ x : _root_.Nat, x ∈ X ↔ f x ∈ Y)
let finiteOneDegree (X : _root_.Set _root_.Nat) : _root_.Set (_root_.Set _root_.Nat) :=
  {Y | finiteOneReducible Y X ∧ finiteOneReducible X Y}
∀ d : _root_.ManyOneDegree,
  let representatives : _root_.Set (_root_.Set _root_.Nat) :=
    {X | _root_.ManyOneDegree.of X = d}
  (¬ ∃ X ∈ representatives, _root_.ComputablePred (fun n : _root_.Nat => n ∈ X)) →
  (∃ X ∈ representatives, _root_.REPred (fun n : _root_.Nat => n ∈ Xᶜ)) →
  let finiteOneDegrees := _root_.Set.image finiteOneDegree representatives
  _root_.ExistsUnique (fun D => D ∈ finiteOneDegrees) ∨ _root_.Set.Infinite finiteOneDegrees) :=
(by
  -- Cintioli, arXiv:2609.00419v1, §1 p. 1 and Corollary 7 p. 14, pass
  -- to the complementary degree. The paper excludes a finite cardinality
  -- greater than one. Here the two disjuncts transfer directly along Φ.
  -- https://arxiv.org/pdf/2609.00419v1#page=1
  -- https://arxiv.org/pdf/2609.00419v1#page=14
  -- The article-specific portal and its defect report returned HTTP 404.
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419
  -- https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects
  intro finiteOneReducible finiteOneDegree d representatives hnonrec hcoce finiteOneDegrees
  obtain ⟨A, hAd, hAcoce⟩ := hcoce
  change ManyOneDegree.of A = d at hAd
  subst d
  let F (e : ManyOneDegree) := Set.image finiteOneDegree {X | ManyOneDegree.of X = e}
  change (∃! D, D ∈ F (ManyOneDegree.of A)) ∨ (F (ManyOneDegree.of A)).Infinite

  -- Alphabeta Math's many-one interface, verification Step 1.1, uses
  -- total computable maps and membership equivalences on Nat. Here the
  -- second reduction from quotient equality lets us precompose a total
  -- decision procedure for Y with a reduction from Aᶜ to Y. Negating the
  -- resulting test decides A, contradicting nonrecursiveness of its degree.
  -- https://alphabetamath.cc/item/def-computable-many-one-reducibility-interface
  have hComplementNonrecursive :
      ¬ ∃ Y : Set Nat, ManyOneDegree.of Y = ManyOneDegree.of Aᶜ ∧
        ComputablePred (fun n : Nat => n ∈ Y) := by
    rintro ⟨Y, hY, hYcomp⟩
    have hComplComp : ComputablePred (fun n : Nat => n ∈ Aᶜ) :=
      ComputablePred.computable_of_manyOneReducible
        (ManyOneDegree.of_eq_of.mp hY).2 hYcomp
    have hAcomp : ComputablePred (fun n : Nat => n ∈ A) := by
      simpa only [Set.mem_compl_iff, not_not] using hComplComp.not
    exact hnonrec ⟨A, rfl, hAcomp⟩

  -- The two Nat reductions in the Maslova supplier characterize precisely
  -- the quotient fibre of Aᶜ. Its finite-one class map agrees definitionally
  -- with the one in this endpoint.
  let complementRepresentatives : Set (Set Nat) :=
    {Y | ManyOneReducibilityOnNat Y Aᶜ ∧ ManyOneReducibilityOnNat Aᶜ Y}
  have hFibre (Y : Set Nat) :
      Y ∈ complementRepresentatives ↔ ManyOneDegree.of Y = ManyOneDegree.of Aᶜ :=
    ManyOneDegree.of_eq_of.symm
  have hRepresentatives :
      complementRepresentatives = {Y | ManyOneDegree.of Y = ManyOneDegree.of Aᶜ} :=
    Set.ext hFibre
  have hMaslova := MaslovaCeDichotomy Aᶜ
    (fun ⟨Y, hY, hYcomp⟩ => hComplementNonrecursive ⟨Y, (hFibre Y).mp hY, hYcomp⟩)
    ⟨Aᶜ, (hFibre Aᶜ).mpr rfl,
      -- Recognizability equivalence, Steps 1.2, 2.1 and 3.1, uses binary
      -- words and handles the empty language separately. The compiled
      -- bridge gives the corresponding Nat enumeration for n false bits.
      -- The supplied REPred proves the encoded c.e. premise for Aᶜ itself.
      -- https://alphabetamath.cc/item/thm-recognizable-iff-enumerable
      (ComputablyEnumerableSet.nat_rePred_iff false Aᶜ).mp hAcoce⟩
  change (∃! D, D ∈ Set.image finiteOneDegree complementRepresentatives) ∨
    (Set.image finiteOneDegree complementRepresentatives).Infinite at hMaslova
  rw [hRepresentatives] at hMaslova

  -- The order-isomorphism supplier takes the same co-c.e. hypothesis and
  -- identifies the subtypes of these very class images. Only its underlying
  -- equivalence is needed to transport cardinality.
  obtain ⟨Φ, _⟩ := ComplementationOrderIsomorphism A hAcoce
  have e : F (ManyOneDegree.of A) ≃ F (ManyOneDegree.of Aᶜ) := Φ.toEquiv
  rcases hMaslova with hUnique | hInfinite
  · exact Or.inl (e.existsUnique_subtype_congr.mpr hUnique)
  · exact Or.inr (Set.infinite_coe_iff.mp
      (e.infinite_iff.mpr (Set.infinite_coe_iff.mpr hInfinite))))
