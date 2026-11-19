import Mathlib



set_option maxHeartbeats 2000000

/--
The two-entry sequence code used by the reviewed acceptability predicate
is total computable.

Alphabeta Math's `lem-finite-tuples-admit-effective-prefix-free-encodings`,
step 1.1, supplies the layout of each block. If the canonical binary numeral
has length `ℓ = Nat.log2 entry + 1`, then `2^ℓ - 1` is the `ℓ`-bit
all-ones suffix and multiplication by `2 * 2^ℓ` leaves room for the separator
and the numeral. This length is one for zero, as required by the linked
`def-natural-number-coding-of-finite-sequences`. Step 2.1 applies with
`k = 2 ≥ 1`. The sequence definition prepends its additional leading one,
giving the initial word `0b1110`. Here the task is computability of the
forward map, so the Lean proof implements these appends by arithmetic.

The coordinator's bounded scan is furnished by `Primrec.nat_findGreatest`.
Its power test uses `Nat.Primrec.pow`, which implements powers by primitive
recursion. For a downstream application of `Nat.Partrec.Code.smn`, compose
the forward map with `Nat.unpair` to preprocess the `Nat.pair` input in the
supplier’s evaluation identity.
-/
theorem AcceptableNumbering.computable₂_sequenceCode :
    let appendEntry (initialWord entry : Nat) : Nat :=
      let place := 2 ^ (Nat.log2 entry + 1)
      let withLength := initialWord * place + (place - 1)
      withLength * (2 * place) + entry
    Computable₂ (fun a x => appendEntry (appendEntry 0b1110 a) x) := by
  intro appendEntry
  have power : Primrec₂ ((· ^ ·) : Nat → Nat → Nat) :=
    Primrec₂.unpaired'.1 Nat.Primrec.pow
  have powerTwo : Primrec (fun k : Nat => 2 ^ k) :=
    power.comp (Primrec.const 2) Primrec.id
  have logTwo : Primrec Nat.log2 := by
    have powerTest : PrimrecRel (fun n k : Nat => 2 ^ k ≤ n) :=
      Primrec.nat_le.comp (powerTwo.comp Primrec.snd) Primrec.fst
    refine (Primrec.nat_findGreatest Primrec.id powerTest).of_eq ?_
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rfl
    -- The exponent lies in the scan range and no larger exponent passes.
    exact Nat.findGreatest_eq_iff.2
      ⟨Nat.log2_le_self n, fun _ => Nat.log2_self_le hn,
        fun _ hk _ => not_le_of_gt ((Nat.log2_lt hn).1 hk)⟩
  have place : Primrec (fun entry : Nat => 2 ^ (entry.log2 + 1)) :=
    powerTwo.comp (Primrec.succ.comp logTwo)
  have append : Primrec₂ appendEntry := by
    change Primrec (fun p : Nat × Nat => appendEntry p.1 p.2)
    have p := place.comp (Primrec.snd : Primrec (Prod.snd : Nat × Nat → Nat))
    have withLength := Primrec.nat_add.comp (Primrec.nat_mul.comp Primrec.fst p)
      (Primrec.nat_sub.comp p (Primrec.const 1))
    exact Primrec.nat_add.comp
      (Primrec.nat_mul.comp withLength (Primrec.nat_mul.comp (Primrec.const 2) p)) Primrec.snd
  exact (append.comp (append.comp (Primrec.const 0b1110) Primrec.fst) Primrec.snd).to₂.to_comp

/-
The reviewed endpoint is the Shared Math Library definition. The numbered
steps above come from the encoding lemma linked by the sequence definition.
The article-specific portal and defect report both returned HTTP 404.
https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419
https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects
-/

noncomputable def AcceptableNumbering : ((_root_.Nat → _root_.Nat → _root_.Part _root_.Nat) → Prop) :=
(fun φ =>
  let universal := _root_.Partrec₂ φ
  let appendEntry (initialWord entry : _root_.Nat) : _root_.Nat :=
    let place := 2 ^ (_root_.Nat.log2 entry + 1)
    let withLength := initialWord * place + (place - 1)
    withLength * (2 * place) + entry
  (∀ e : _root_.Nat, _root_.Partrec (φ e)) ∧
    (∀ f : _root_.Nat → _root_.Part _root_.Nat, _root_.Partrec f → ∃ e : _root_.Nat, φ e = f) ∧
    universal ∧
    ∃ s : _root_.Nat → _root_.Nat → _root_.Nat, _root_.Computable₂ s ∧
      ∀ e a x : _root_.Nat, φ (s e a) x = φ e (appendEntry (appendEntry 0b1110 a) x))
