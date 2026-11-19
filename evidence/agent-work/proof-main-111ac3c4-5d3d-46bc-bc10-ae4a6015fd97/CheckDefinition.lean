import Mathlib

def RelativeComputabilityAndEnumerability : Set Nat → (Set Nat → Prop) × (Set Nat → Prop) × ((Nat → Nat) → Prop) := fun X =>
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
          (fun _ tape => readNumeral symbols tape 0 = Option.some (f n))) )

#print axioms RelativeComputabilityAndEnumerability
