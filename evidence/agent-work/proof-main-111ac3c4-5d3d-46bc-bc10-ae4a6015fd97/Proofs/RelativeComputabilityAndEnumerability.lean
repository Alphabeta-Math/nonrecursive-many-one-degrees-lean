import Mathlib



set_option maxHeartbeats 2000000

/-
Alphabeta Math, def-relative-computability-and-enumerability, Definition
(https://alphabetamath.cc/item/def-relative-computability-and-enumerability).
This definition has no numbered proof steps. For ordinary instructions it
uses the linked one-step configuration relation
(https://alphabetamath.cc/item/def-one-step-configuration-relation).
States 0, 1 and 2 designate start, accept and reject. Missing tape cells
are blank, and subtraction on Nat implements the clamped left move. A
query reads a canonical numeral starting at the head with an explicit
right delimiter. A malformed query selects the negative successor and
neither branch changes the tape or the head. Reflexive-transitive closure
describes finite runs, with the final-state predicate requiring a halt.
The three components test a total decision, acceptance, and a halt with
delimited output at cell zero, respectively.

At the pinned mathlib revision, Nat.RecursiveIn and ComputableIn give the
partial and total recursion interfaces. Turing.PartrecToTM2.tr_eval is a
correctness theorem for ordinary TM2 evaluation on encoded list inputs.
TauCeti.Oracle.Single.Code.exists_code gives singleton-oracle adequacy for
TauCeti's own code evaluator. The reviewed definition uses the concrete
binary tape semantics directly. Its installation uses none of these
suppliers. Their use in FixedStageRowStability requires a machine bridge
that preserves queries and halting and produces the reviewed output format.

The article-specific Alphabeta collection and its defect-report URL both
returned HTTP 404. The shared-library Definition above is the source for
this endpoint.
-/

noncomputable def RelativeComputabilityAndEnumerability : (Set Nat → (Set Nat → Prop) × (Set Nat → Prop) × ((Nat → Nat) → Prop)) :=
(fun X =>
  let Program (states symbols : Nat) :=
    Fin (states + 3) →
      Sum (Fin (symbols + 4) → Fin (states + 3) × Fin (symbols + 4) × Bool)
        (Fin (states + 3) × Fin (states + 3))
  let Configuration (states symbols : Nat) :=
    Fin (states + 3) × Nat × List (Fin (symbols + 4))
  let numeral (symbols n : Nat) : List (Fin (symbols + 4)) :=
    List.map (fun digit => if digit = '0' then 0 else 1) (Nat.toDigits 2 n)
  let readNumeral (symbols : Nat) (tape : List (Fin (symbols + 4))) (start : Nat) :
      Option Nat :=
    let tail := List.drop start tape
    let word := List.takeWhile (fun digit => digit != 3) tail
    let n := List.foldl (fun acc digit => 2 * acc + Fin.val digit) 0 word
    if List.getD tail (List.length word) 2 = 3 ∧ word = numeral symbols n then
      Option.some n
    else
      Option.none
  let halting (states : Nat) (state : Fin (states + 3)) : Bool :=
    state == 1 || state == 2
  let step (states symbols : Nat) (program : Program states symbols)
      (config nextConfig : Configuration states symbols) : Prop :=
    let (state, head, tape) := config
    halting states state = false ∧
      match program state with
      | Sum.inl ordinary =>
        let (next, symbol, right) := ordinary (List.getD tape head 2)
        let padded := tape ++ List.replicate (head + 1 - List.length tape) 2
        nextConfig = (next, if right then head + 1 else head - 1, List.set padded head symbol)
      | Sum.inr (yes, no) =>
        match readNumeral symbols tape head with
        | Option.none => nextConfig = (no, head, tape)
        | Option.some q =>
          (q ∈ X ∧ nextConfig = (yes, head, tape)) ∨
          (q ∉ X ∧ nextConfig = (no, head, tape))
  let haltsWith (states symbols : Nat) (program : Program states symbols) (input : Nat)
      (post : Fin (states + 3) → List (Fin (symbols + 4)) → Prop) : Prop :=
    ∃ (state : Fin (states + 3)) (head : Nat) (tape : List (Fin (symbols + 4))),
      Relation.ReflTransGen (step states symbols program)
        (0, 0, numeral symbols input) (state, head, tape) ∧
      halting states state = true ∧ post state tape
  ( (fun A =>
      ∃ (states symbols : Nat) (program : Program states symbols),
        ∀ n : Nat, haltsWith states symbols program n (fun _ _ => True) ∧
          (haltsWith states symbols program n (fun state _ => state = 1) ↔ n ∈ A)),
    (fun A =>
      ∃ (states symbols : Nat) (program : Program states symbols),
        ∀ n : Nat, haltsWith states symbols program n (fun state _ => state = 1) ↔ n ∈ A),
    (fun f =>
      ∃ (states symbols : Nat) (program : Program states symbols),
        ∀ n : Nat, haltsWith states symbols program n
          (fun _ tape => readNumeral symbols tape 0 = Option.some (f n))) ))
