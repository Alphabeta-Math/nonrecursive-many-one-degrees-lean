# Project

## ManyOneReducibilityOnNat: Computable many one reducibility interface

Prerequisite; compiled and axiom-checked.

### Article

No original article statement.

### Alphabeta Math

For $A,B\subseteq\mathbb N$, write $A\le_m B$ if a total computable $f:\mathbb N\to\mathbb N$ satisfies

$$\forall n\in\mathbb N\quad(n\in A\ \Longleftrightarrow\ f(n)\in B).$$

[Shared Math Library, def-computable-many-one-reducibility-interface, Definition (ordinary many-one reducibility on natural numbers)](https://alphabetamath.cc/item/def-computable-many-one-reducibility-interface)

### Lean statement

Translation source: portal. The plan selects the ordinary natural-number clause of Alphabeta Math’s def-computable-many-one-reducibility-interface as this standalone prerequisite and supplies no article endpoint for the item. The clause agrees with the convention on page 2 of arXiv:2609.00419v1. The article-specific Research Portal and defect-report URLs both returned HTTP 404, so no correction could be verified there. https://alphabetamath.cc/item/def-computable-many-one-reducibility-interface [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
def ManyOneReducibilityOnNat : _root_.Set _root_.Nat → _root_.Set _root_.Nat → Prop := fun A B => _root_.ManyOneReducible (fun n : _root_.Nat => n ∈ A) (fun n : _root_.Nat => n ∈ B)
```

Immediate internal dependencies: none.

Existing repository dependencies: none.

Immediate external dependencies: ManyOneRelation (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/ManyOneReducibilityOnNat.json), [proof](Proofs/ManyOneReducibilityOnNat.lean), [compilation evidence](evidence/ManyOneReducibilityOnNat-compile.json).

## ComputablyEnumerableSet: Computably enumerable sets and languages

Prerequisite; compiled and axiom-checked.

### Article

No original article statement.

### Alphabeta Math

Fix an effectively encoded set $X$.

A subset $A\subseteq X$ is **computably enumerable** when either $A=\varnothing$
or there exists a total computable function

$$ e:\mathbb N\to X $$

whose range is exactly $A$.

If $L\subseteq\Sigma^{\ast}$ is a language over an alphabet $\Sigma$, then $L$ is
**computably enumerable** when it is c.e. as a subset of $\Sigma^{\ast}$ under the
chosen effective word encoding.

[Shared Math Library, def-computably-enumerable-set, Definition](https://alphabetamath.cc/item/def-computably-enumerable-set)

### Lean statement

Translation source: portal. The article uses computable enumerability without defining it, so the endpoint comes from Alphabeta Math’s shared-library item def-computably-enumerable-set. The definition keeps the chosen binary encoder and total decoder explicit and applies computability to the enumerator’s binary outputs. For languages, instantiate α with List σ and supply the chosen word encoder and decoder. The article-specific Research Portal and defect report both returned HTTP 404, so no correction could be verified. https://alphabetamath.cc/item/def-computably-enumerable-set [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
def ComputablyEnumerableSet : ∀ {α : Type*} (encode : α → _root_.List _root_.Bool) (decode : _root_.List _root_.Bool → _root_.Option α), _root_.Function.Injective encode → (∀ x, decode (encode x) = _root_.Option.some x) → (∀ w, w ∉ _root_.Set.range encode → decode w = _root_.Option.none) → _root_.Set α → Prop := fun {α} encode _ _ _ _ A => A = ∅ ∨ ∃ e : _root_.Nat → α, _root_.Computable (fun n : _root_.Nat => encode (e n)) ∧ _root_.Set.range e = A
```

Immediate internal dependencies: none.

Existing repository dependencies: none.

Immediate external dependencies: RecEnumerablePredicate, EffectiveRangeEnumeration, ComputableRangeCE, PartialComputableSearch, PartialSearchDomain, PartialCodeSurjectivity, PrimitiveRecursiveBoundedCodeEvaluation, BoundedCodeEvaluationCompleteness (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/ComputablyEnumerableSet.json), [proof](Proofs/ComputablyEnumerableSet.lean), [compilation evidence](evidence/ComputablyEnumerableSet-compile.json).

## InfiniteCEInjectiveEnumeration: Infinite computably enumerable sets have computable injective enumerations

Prerequisite; compiled and axiom-checked.

### Article

No original article statement.

### Alphabeta Math

Every infinite computably enumerable subset of an effectively encoded set $X$ is
the range of a total computable injective function $\mathbb N\to X$.

[Shared Math Library, thm-infinite-ce-sets-have-computable-injective-enumerations, Statement](https://alphabetamath.cc/item/thm-infinite-ce-sets-have-computable-injective-enumerations)

### Lean statement

Translation source: portal. Alphabeta Math’s shared-library item thm-infinite-ce-sets-have-computable-injective-enumerations states the theorem for arbitrary effectively encoded sets. Page 4 of arXiv:2609.00419v1 uses the natural-number instance. The translation uses the same binary encoding and decoding convention as ComputablyEnumerableSet. The article-specific Research Portal and designated defect report both returned HTTP 404, so any correction remains unverified. https://alphabetamath.cc/item/thm-infinite-ce-sets-have-computable-injective-enumerations [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
theorem InfiniteCEInjectiveEnumeration : ∀ {α : Type*} (encode : α → _root_.List _root_.Bool)
    (decode : _root_.List _root_.Bool → _root_.Option α)
    (hInjective : _root_.Function.Injective encode)
    (hDecode : ∀ x : α, decode (encode x) = _root_.Option.some x)
    (hInvalid : ∀ w : _root_.List _root_.Bool,
      w ∉ _root_.Set.range encode → decode w = _root_.Option.none)
    (A : _root_.Set α),
    _root_.ComputablyEnumerableSet encode decode hInjective hDecode hInvalid A →
    _root_.Set.Infinite A →
    ∃ f : _root_.Nat → α,
      _root_.Computable (fun n : _root_.Nat => encode (f n)) ∧
      _root_.Function.Injective f ∧ _root_.Set.range f = A
```

Immediate internal dependencies: ComputablyEnumerableSet.

Existing repository dependencies: none.

Immediate external dependencies: InjectiveCEEnumeration, LeastComputableWitness, ComputableRecursion, PrimitiveRecursiveListMembership, InjectiveComputableRange (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/InfiniteCEInjectiveEnumeration.json), [proof](Proofs/InfiniteCEInjectiveEnumeration.lean), [compilation evidence](evidence/InfiniteCEInjectiveEnumeration-compile.json).

## ArithmeticalHierarchyLevels: The classes $\Sigma_n^0$, $\Pi_n^0$, and $\Delta_n^0$

Prerequisite; compiled and axiom-checked.

### Article

No original article statement.

### Alphabeta Math

For $n\ge1$, a set $A\subseteq\mathbb N^k$ is **$\Sigma_n^0$** when, for a
primitive-recursive predicate $R$, membership has a formula

$$ \vec x\in A\iff \exists y_1\forall y_2\cdots Qy_n\ R(\vec x,\vec y), $$

where the quantifiers alternate and $Q$ is existential for odd $n$. It is
**$\Pi_n^0$** when its complement is $\Sigma_n^0$, equivalently when the
display begins universally. Put

$$ \Delta_n^0:=\Sigma_n^0\cap\Pi_n^0. $$

Bounded quantifiers in $R$ are allowed under the convention of
[[def-bounded-arithmetic-formula]].

[Shared Math Library, def-sigma-n-pi-n-and-delta-n-sets, Definition](https://alphabetamath.cc/item/def-sigma-n-pi-n-and-delta-n-sets)

### Lean statement

Translation source: portal. The general definition is supplied only by the Alphabeta Math Shared Math Library item def-sigma-n-pi-n-and-delta-n-sets (https://alphabetamath.cc/item/def-sigma-n-pi-n-and-delta-n-sets). The article-specific Research Portal and the supplied defect report (https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects) both returned HTTP 404. PrimrecRel represents the primitive-recursive matrix, including the permitted bounded quantifiers. [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
def ArithmeticalHierarchyLevels : (n k : Nat) → 1 ≤ n →
  Set (Set (Fin k → Nat)) × Set (Set (Fin k → Nat)) × Set (Set (Fin k → Nat)) := fun n k _ =>
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
  (sigma, pi, sigma ∩ pi)
```

Immediate internal dependencies: none.

Existing repository dependencies: none.

Immediate external dependencies: none declared (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/ArithmeticalHierarchyLevels.json), [proof](Proofs/ArithmeticalHierarchyLevels.lean), [compilation evidence](evidence/ArithmeticalHierarchyLevels-compile.json).

## RelativeComputabilityAndEnumerability: Relative computability and relative enumerability

Prerequisite; compiled and axiom-checked.

### Article

No original article statement.

### Alphabeta Math

Fix the canonical binary numeral for each natural number (with zero encoded
as $0$). For an oracle $X\subseteq\mathbb N$, an oracle program is a finite
deterministic machine program with ordinary transitions as in
[[def-one-step-configuration-relation]], together with query instructions.
A query instruction reads a finite binary numeral $q$ delimited on the tape
and selects one of two specified successor states according as $q\in X$ or
$q\notin X$; it leaves the tape and head unchanged. Malformed queries select
the negative successor. On input $n$, start in the initial state with its
numeral at the left end of an otherwise blank tape and the head at position
zero. Iterate these transitions until an accepting or rejecting state is
entered, if that ever happens.

A set $A\subseteq\mathbb N$ is **$X$-computable** when some such program
halts on every numeral input and accepts exactly the members of $A$.
It is **$X$-c.e.** when some such program accepts exactly the members of $A$;
on nonmembers it may reject or run forever. Write $A\le_T X$ for
$X$-computability. A function $f:\mathbb N\to\mathbb N$ is **total
$X$-computable** when some such oracle program halts on every numeral input
$n$ with the numeral of $f(n)$ as its delimited output.

An oracle program still makes finitely many transitions on any halting run;
it does not read an infinite oracle at once.

[Shared Math Library, def-relative-computability-and-enumerability, Definition](https://alphabetamath.cc/item/def-relative-computability-and-enumerability)

### Lean statement

Translation source: portal. Only the Alphabeta Shared Math Library item https://alphabetamath.cc/item/def-relative-computability-and-enumerability states this definition. The article uses relative enumerability without a separate definition. The article-specific portal and the defect report both returned HTTP 404. No correction was available from the report at https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects. The three components express X-computability (Turing reducibility to X), being c.e. in X, and total X-computability. The tape encoding uses a right delimiter, with query numerals beginning at the head and output numerals beginning at cell zero. [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
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
```

Immediate internal dependencies: none.

Existing repository dependencies: none.

Immediate external dependencies: RelativizedTotalComputability, OracleCodeExistence (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/RelativeComputabilityAndEnumerability.json), [proof](Proofs/RelativeComputabilityAndEnumerability.lean), [compilation evidence](evidence/RelativeComputabilityAndEnumerability-compile.json).

## AcceptableNumbering: Universal and acceptable numberings

Prerequisite; compiled and axiom-checked.

### Article

No original article statement.

### Alphabeta Math

Let $(\varphi_e)_{e\in\mathbb N}$ be a numbering of the partial computable
functions.

The numbering is **universal** when the binary partial function

$$ U(e,x)\simeq\varphi_e(x) $$

is itself partial computable.

The numbering is **acceptable** when it is universal and there exists a total
computable function

$$ s:\mathbb N^2\to\mathbb N $$

such that for all $e,a,x\in\mathbb N$ one has

$$ \varphi_{s(e,a)}(x)\simeq\varphi_e(\ulcorner a,x\urcorner_{\mathrm{seq}}), $$

where $\ulcorner a,x\urcorner_{\mathrm{seq}}$ is the chosen code of the
two-term sequence $(a,x)$.

[Shared Math Library, def-universal-and-acceptable-numbering, Definition](https://alphabetamath.cc/item/def-universal-and-acceptable-numbering)

### Lean statement

Translation source: portal. Alphabeta Math’s def-universal-and-acceptable-numbering supplies the standalone definition. The article has no standalone endpoint for this item. The Lean definition uses the binary sequence word specified by the linked def-natural-number-coding-of-finite-sequences. The article-specific Research Portal and defect report both returned HTTP 404, so no correction could be verified. https://alphabetamath.cc/item/def-universal-and-acceptable-numbering https://alphabetamath.cc/item/def-natural-number-coding-of-finite-sequences [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
def AcceptableNumbering : (_root_.Nat → _root_.Nat → _root_.Part _root_.Nat) → Prop := fun φ =>
  let universal := _root_.Partrec₂ φ
  let appendEntry (initialWord entry : _root_.Nat) : _root_.Nat :=
    let place := 2 ^ (_root_.Nat.log2 entry + 1)
    let withLength := initialWord * place + (place - 1)
    withLength * (2 * place) + entry
  (∀ e : _root_.Nat, _root_.Partrec (φ e)) ∧
    (∀ f : _root_.Nat → _root_.Part _root_.Nat, _root_.Partrec f → ∃ e : _root_.Nat, φ e = f) ∧
    universal ∧
    ∃ s : _root_.Nat → _root_.Nat → _root_.Nat, _root_.Computable₂ s ∧
      ∀ e a x : _root_.Nat, φ (s e a) x = φ e (appendEntry (appendEntry 0b1110 a) x)
```

Immediate internal dependencies: none.

Existing repository dependencies: none.

Immediate external dependencies: UniversalEvaluator, PartialCodeSurjectivity, ParameterTheorem, PrimitiveRecursiveBoundedGreatest (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/AcceptableNumbering.json), [proof](Proofs/AcceptableNumbering.lean), [compilation evidence](evidence/AcceptableNumbering-compile.json).

## HaltingSigmaOneCompleteness: The halting set is $\Sigma_1^0$-complete

Prerequisite; compiled and axiom-checked.

### Article

No original article statement.

### Alphabeta Math

For a fixed acceptable numbering, $K=\{\langle e,x\rangle:\varphi_e(x)\downarrow\}$
is $\Sigma_1^0$-complete.

[Shared Math Library, thm-halting-is-sigma-one-complete, Statement](https://alphabetamath.cc/item/thm-halting-is-sigma-one-complete)

### Lean statement

Translation source: portal. Only Alphabeta Math’s shared-library item thm-halting-is-sigma-one-complete states this endpoint. The translation uses Nat.pair as the fixed computable bijective pairing, decoded by Nat.unpair. The linked definition of completeness requires Sigma-1 membership and a total computable many-one reduction from each Sigma-1 set. The article-specific Research Portal and defect report both returned HTTP 404, so no correction could be verified. https://alphabetamath.cc/item/thm-halting-is-sigma-one-complete https://alphabetamath.cc/item/def-arithmetical-level-completeness https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
theorem HaltingSigmaOneCompleteness : ∀ φ : _root_.Nat → _root_.Nat → _root_.Part _root_.Nat,
  _root_.AcceptableNumbering φ →
  let K : _root_.Set _root_.Nat := {n |
    let p := _root_.Nat.unpair n
    _root_.Part.Dom (φ (_root_.Prod.fst p) (_root_.Prod.snd p))}
  let sigmaOne : _root_.Set _root_.Nat → Prop := fun A =>
    _root_.Set.preimage (fun xs : _root_.Fin 1 → _root_.Nat => xs 0) A ∈
      _root_.Prod.fst (_root_.ArithmeticalHierarchyLevels 1 1 (_root_.Nat.le_refl 1))
  sigmaOne K ∧
    ∀ A : _root_.Set _root_.Nat, sigmaOne A →
      ∃ f : _root_.Nat → _root_.Nat, _root_.Computable f ∧
        ∀ n : _root_.Nat, n ∈ A ↔ f n ∈ K
```

Immediate internal dependencies: AcceptableNumbering, ArithmeticalHierarchyLevels.

Existing repository dependencies: none.

Immediate external dependencies: CEAsCodeDomain, ExistentialComputableCE, UniversalEvaluator, PartialCodeSurjectivity, PrimitiveRecursiveBoundedCodeEvaluation, BoundedCodeEvaluationCompleteness, PartialComputableSearch, PartialSearchDomain, ParameterTheorem, BoundedCodeEvaluationMonotonicity (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/HaltingSigmaOneCompleteness.json), [proof](Proofs/HaltingSigmaOneCompleteness.lean), [compilation evidence](evidence/HaltingSigmaOneCompleteness-compile.json).

## ReducibilityImplications: One-one, finite-one, and many-one reducibility

Main result; compiled and axiom-checked.

### Article

Finite-one reducibility is the restriction of many-one reducibility in which every fibre of the reducing function is finite. Thus, for all sets $X,Y$,

$$X\leq_1 Y \Longrightarrow X\leq_{\mathrm{fo}}Y\ \Longrightarrow X\leq_{\mathrm{m}}Y.$$

[§1, p. 1 (unnumbered)](https://arxiv.org/pdf/2609.00419v1#page=1)

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Translation source: article. The two implications occur in §1, p. 1 of arXiv:2609.00419v1 and use the conventions stated in §2, p. 2. The article-specific Alphabeta Math portal and the supplied defect-report URL both returned HTTP 404. No correction for this result could be verified. [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
theorem ReducibilityImplications : ∀ X Y : _root_.Set _root_.Nat,
  let finiteOneReducible : Prop :=
    ∃ f : _root_.Nat → _root_.Nat, _root_.Computable f ∧
      (∀ y : _root_.Nat, _root_.Set.Finite (_root_.Set.preimage f ({y} : _root_.Set _root_.Nat))) ∧
      (∀ x : _root_.Nat, x ∈ X ↔ f x ∈ Y)
  (_root_.OneOneReducible (fun x : _root_.Nat => x ∈ X) (fun y : _root_.Nat => y ∈ Y) → finiteOneReducible) ∧
  (finiteOneReducible → _root_.ManyOneReducibilityOnNat X Y)
```

Immediate internal dependencies: ManyOneReducibilityOnNat.

Existing repository dependencies: none.

Immediate external dependencies: OneOneRelation, InjectiveFinitePreimage, FiniteFibresFinitePreimage (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/ReducibilityImplications.json), [proof](Proofs/ReducibilityImplications.lean), [compilation evidence](evidence/ReducibilityImplications-compile.json).

## RigidDegreeAntichain: Infinite antichains in many-one degrees of m-rigid sets

Main result; compiled and axiom-checked.

### Article

Earlier work established that, for almost every $A\subseteq\mathbb{N}$ with respect to the standard product measure on $2^\mathbb{N}$, the degree $[A]_{\mathrm{m}}$ contains an infinite antichain of finite-one degrees [1].

Earlier work established that the many-one degree of every $m$-rigid set contains an infinite antichain of finite-one degrees [1]. Since the class of $m$-rigid sets has Lebesgue measure $1$ and is comeager, this gave an almost-sure and comeager negative answer to the question.

[Abstract and §1, p. 1 (prior result [1])](https://arxiv.org/pdf/2609.00419v1#page=1)

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Translation source: article. The abstract and §1 of arXiv:2609.00419v1 state the antichain result and its measure and Baire category assertions. Definition 2.3 of the cited reference [1] specifies m-rigidity as eventual identity of every total computable self-reduction. The article-specific Alphabeta Research Portal and the supplied defect report both returned HTTP 404. No correction was available. https://arxiv.org/pdf/2609.00419v1#page=1 https://arxiv.org/pdf/2603.02600v2 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
theorem RigidDegreeAntichain : let rigid := fun A : _root_.Set _root_.Nat =>
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
```

Immediate internal dependencies: ManyOneReducibilityOnNat, ComputablyEnumerableSet.

Existing repository dependencies: none.

Immediate external dependencies: ComputablePairing, ComputableUnpairing, LeastComputableWitness, PartialCodeSurjectivity, RigidAntichainPrefixCylinderBasis, RigidAntichainDenseOpenResidual, RigidAntichainProductCoordinateMap, RigidAntichainUniformSingleton (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/RigidDegreeAntichain.json), [proof](Proofs/RigidDegreeAntichain.lean), [compilation evidence](evidence/RigidDegreeAntichain-compile.json).

## CylinderGreatestFiniteOneDegree: The cylinder gives the greatest finite-one degree

Main result; compiled and axiom-checked.

### Article

For every set $A$, the cylinder

$$\mathrm{Cyl}(A)=\{\langle x,n\rangle:x\in A, n\in\mathbb{N}\}$$

belongs to the same many-one degree as $A$, and $[\mathrm{Cyl}(A)]_{\mathrm{fo}}$ is the greatest finite-one degree in that many-one degree.

[§1, p. 1 (unnumbered). See also §2, pp. 2–3, for the pairing and degree conventions.](https://arxiv.org/pdf/2609.00419v1#page=1)

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Translation source: article. The endpoint is the unnumbered statement in §1, p. 1 of arXiv:2609.00419v1. The translation uses Nat.pair for the fixed computable pairing and expresses the finite-one degree order on representatives, following §2, pp. 2–3. The article-specific Alphabeta Math portal and the supplied defect-report URL both returned HTTP 404, so no correction for this result could be verified. https://arxiv.org/pdf/2609.00419v1#page=1 [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
theorem CylinderGreatestFiniteOneDegree : ∀ A : _root_.Set _root_.Nat,
  let cyl : _root_.Set _root_.Nat :=
    {z | ∃ x n : _root_.Nat, x ∈ A ∧ z = _root_.Nat.pair x n}
  let finiteOneReducible (X Y : _root_.Set _root_.Nat) : Prop :=
    ∃ f : _root_.Nat → _root_.Nat, _root_.Computable f ∧
      (∀ y : _root_.Nat, _root_.Set.Finite (_root_.Set.preimage f ({y} : _root_.Set _root_.Nat))) ∧
      (∀ x : _root_.Nat, x ∈ X ↔ f x ∈ Y)
  _root_.ManyOneDegree.of cyl = _root_.ManyOneDegree.of A ∧
    (∀ B : _root_.Set _root_.Nat,
      _root_.ManyOneDegree.of B = _root_.ManyOneDegree.of A → finiteOneReducible B cyl)
```

Immediate internal dependencies: ReducibilityImplications.

Existing repository dependencies: none.

Immediate external dependencies: ComputablePairing, ComputableUnpairing, PairingEquivalence, ManyOneDegreeEquality, PreorderQuotient, PreorderQuotientOrder, FiniteFibresFinitePreimage (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/CylinderGreatestFiniteOneDegree.json), [proof](Proofs/CylinderGreatestFiniteOneDegree.lean), [compilation evidence](evidence/CylinderGreatestFiniteOneDegree-compile.json).

## ComplementCeDichotomy: Dichotomy for a nonrecursive degree with a co-c.e. representative

Main result; compiled and axiom-checked.

### Article

Maslova proved that every nonrecursive computably enumerable (c.e.) many-one degree contains either exactly one or infinitely many finite-one degrees [2]. We shall also use the same conclusion when the complement of a representative is c.e., by passing to the complementary many-one degree and using complementation.

[§1, p. 1 (unnumbered); applied in the proof of Corollary 7, p. 14](https://arxiv.org/pdf/2609.00419v1#page=1)

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Translation source: article. The unnumbered statement in §1, p. 1 of arXiv:2609.00419v1 extends the one-or-infinity dichotomy to nonrecursive many-one degrees with a co-c.e. representative. The article applies this case in the proof of Corollary 7 on p. 14. The type uses mathlib’s many-one degree quotient and REPred for computable enumerability on ℕ. The article-specific Alphabeta Math Research Portal and designated defect report both returned HTTP 404. No matching local report or correction for this endpoint could be verified. https://arxiv.org/pdf/2609.00419v1#page=1 https://arxiv.org/pdf/2609.00419v1#page=14 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
theorem ComplementCeDichotomy : let finiteOneReducible (X Y : _root_.Set _root_.Nat) : Prop :=
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
  _root_.ExistsUnique (fun D => D ∈ finiteOneDegrees) ∨ _root_.Set.Infinite finiteOneDegrees
```

Immediate internal dependencies: MaslovaCeDichotomy, ComplementationOrderIsomorphism, ComputablyEnumerableSet.

Existing repository dependencies: none.

Immediate external dependencies: ComputablePredComplement, RecursivePullsBack, ManyOneDegreeEquality (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/ComplementCeDichotomy.json), [proof](Proofs/ComplementCeDichotomy.lean), [compilation evidence](evidence/ComplementCeDichotomy-compile.json).

## ProfileRealization: Profile realization

Main result; compiled and axiom-checked.

### Article

If $p:\mathbb{N}\to\mathbb{N}$ is total computable, define its infinite-fibre profile by

$$I_p=\{y:|p^{-1}(y)|=\infty\}.$$

A section of a map $p:\mathbb{N}\to\mathbb{N}$ is a map $s:\mathbb{N}\to\mathbb{N}$ such that

$$p(s(y))=y \qquad\text{for every }y\in\mathbb{N}.$$

Thus a section is a right inverse of $p$.

For every $P\in\Pi^0_2$ there is a total computable surjection $p:\mathbb{N}\to\mathbb{N}$ such that

$$I_p=P.$$

Moreover, $p$ has a computable section.

[§2, Lemma 1, p. 3](https://arxiv.org/pdf/2609.00419v1#page=3)

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Translation source: article. Lemma 1 in §2, p. 3 of arXiv:2609.00419v1 states this endpoint. The unary Π⁰₂ hypothesis uses the Π component of ArithmeticalHierarchyLevels at level 2 and arity 1. The article-specific Alphabeta Math Research Portal and the designated defect report both returned HTTP 404. No local counterpart or correction could be verified. https://arxiv.org/pdf/2609.00419v1#page=3 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
theorem ProfileRealization : ∀ P : _root_.Set _root_.Nat,
  {xs : _root_.Fin 1 → _root_.Nat | xs 0 ∈ P} ∈
      (_root_.ArithmeticalHierarchyLevels 2 1 (_root_.Nat.le_succ 1)).2.1 →
    ∃ p : _root_.Nat → _root_.Nat,
      _root_.Computable p ∧ _root_.Function.Surjective p ∧
      {y : _root_.Nat | _root_.Set.Infinite (_root_.Set.preimage p ({y} : _root_.Set _root_.Nat))} = P ∧
      (∃ s : _root_.Nat → _root_.Nat,
        _root_.Computable s ∧ _root_.Function.RightInverse s p)
```

Immediate internal dependencies: PiTwoDescendingCePresentation, ComputableInjectiveSection, InfiniteCEInjectiveEnumeration, ArithmeticalHierarchyLevels, ComputablyEnumerableSet.

Existing repository dependencies: none.

Immediate external dependencies: ComputablePairing, ComputableUnpairing, PairingEquivalence, BoundedSearchComputable, ExistentialComputableCE (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/ProfileRealization.json), [proof](Proofs/ProfileRealization.lean), [compilation evidence](evidence/ProfileRealization-compile.json).

## PiTwoDescendingCePresentation: Descending uniformly c.e. presentation of the profile

Main result; compiled and axiom-checked.

### Article

Choose a computable predicate $Q$ such that

$$y\in P \iff \forall j\,\exists s\,Q(y,j,s).$$

For each $k\in\mathbb{N}$, let

$$H_k= \{y:\forall j\lt k\,\exists s\,Q(y,j,s)\}.$$

The sequence $(H_k)_{k\in\mathbb{N}}$ is uniformly c.e., and

$$\mathbb{N}=H_0\supseteq H_1\supseteq H_2\supseteq\cdots.$$

Moreover,

$$P=\bigcap_{k\in\mathbb{N}}H_k.$$

[§2, proof of Lemma 1, p. 3 (unnumbered, under the Π⁰₂ hypothesis of Lemma 1)](https://arxiv.org/pdf/2609.00419v1#page=3)

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Translation source: article. The endpoint is the unnumbered descending presentation in §2, p. 3 of arXiv:2609.00419v1, under the Π⁰₂ hypothesis of Lemma 1. The translation uses Nat.pair as the fixed computable pairing and Nat.unpair to read each code. Uniform c.e. membership is computable enumerability of the single set of coded pairs (k, y) with y in Hₖ. The natural-number word encoding sends n to the word of n false bits. The article-specific Alphabeta portal and designated defect report returned HTTP 404. No local report or correction could be verified for this endpoint. https://arxiv.org/pdf/2609.00419v1#page=3 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
theorem PiTwoDescendingCePresentation : ∀ P : _root_.Set _root_.Nat,
  {xs : _root_.Fin 1 → _root_.Nat | xs 0 ∈ P} ∈
      (_root_.ArithmeticalHierarchyLevels 2 1 (_root_.Nat.le_succ 1)).2.1 →
  ∃ Q : _root_.Nat → _root_.Nat → _root_.Nat → Prop,
    _root_.ComputablePred (fun t : _root_.Nat × _root_.Nat × _root_.Nat =>
      Q t.1 t.2.1 t.2.2) ∧
    (∀ y : _root_.Nat, y ∈ P ↔ ∀ j : _root_.Nat, ∃ s : _root_.Nat, Q y j s) ∧
    (let H (k : _root_.Nat) : _root_.Set _root_.Nat :=
      {y | ∀ j : _root_.Nat, j < k → ∃ s : _root_.Nat, Q y j s}
     let encode (n : _root_.Nat) := _root_.List.replicate n false
     let decode (w : _root_.List _root_.Bool) :=
       if w = encode (_root_.List.length w) then _root_.Option.some (_root_.List.length w)
       else _root_.Option.none
     _root_.ComputablyEnumerableSet encode decode
       (_root_.List.replicate_left_injective false)
       (fun n => by simp [decode, encode])
       (fun w hw => _root_.ite_eq_right (fun h => hw ⟨_root_.List.length w, h.symm⟩))
       {z : _root_.Nat | (_root_.Nat.unpair z).2 ∈ H (_root_.Nat.unpair z).1} ∧
     H 0 = _root_.Set.univ ∧ _root_.Antitone H ∧ P = _root_.Set.iInter H)
```

Immediate internal dependencies: ArithmeticalHierarchyLevels, ComputablyEnumerableSet.

Existing repository dependencies: none.

Immediate external dependencies: BoundedSearchComputable, ExistentialComputableCE (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/PiTwoDescendingCePresentation.json), [proof](Proofs/PiTwoDescendingCePresentation.lean), [compilation evidence](evidence/PiTwoDescendingCePresentation-compile.json).

## ComputableInjectiveSection: Computable injective section of a computable surjection

Main result; compiled and axiom-checked.

### Article

Finally, define

$$s(y)=\mu n\,[p(n)=y].$$

The function $s$ is total computable because $p$ is computable and surjective, and

$$p(s(y))=y$$

for every $y$. Thus $s$ is a computable section of $p$.

Moreover, if $s(y)=s(z)$, then

$$y=p(s(y))=p(s(z))=z.$$

Thus $s$ is injective.

[§2, proof of Lemma 1, p. 4 (unnumbered)](https://arxiv.org/pdf/2609.00419v1#page=4)

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Translation source: article. The endpoint is the unnumbered computable injective section result in §2, p. 4 of arXiv:2609.00419v1. The last conjunct preserves the article’s least-preimage convention for s. The article-specific Alphabeta Math portal and the supplied defect report both returned HTTP 404, and no local counterpart was found, so any correction for this result remains unverified. https://arxiv.org/pdf/2609.00419v1#page=4 [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
theorem ComputableInjectiveSection : ∀ (p : _root_.Nat → _root_.Nat),
  _root_.Computable p → _root_.Function.Surjective p →
    ∃ s : _root_.Nat → _root_.Nat,
      _root_.Computable s ∧ _root_.Function.Injective s ∧
      (∀ y : _root_.Nat, p (s y) = y) ∧
      (∀ y n : _root_.Nat, p n = y → s y ≤ n)
```

Immediate internal dependencies: none.

Existing repository dependencies: none.

Immediate external dependencies: LeastComputableWitness (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/ComputableInjectiveSection.json), [proof](Proofs/ComputableInjectiveSection.lean), [compilation evidence](evidence/ComputableInjectiveSection-compile.json).

## FiniteMarkerAvoidance: Finite-marker avoidance

Main result; compiled and axiom-checked.

### Article

A uniformly c.e. family $(V_x)_{x\in\mathbb{N}}$ is called $A$-homogeneous if

$$z\in V_x \Longrightarrow A(z)=A(x).$$

Assume that $A$ is not a cylinder and that neither $A$ nor $\overline A$ is c.e. If $(V_x)_{x\in\mathbb{N}}$ is a uniformly c.e. $A$-homogeneous family, then for every finite $Z\subseteq\mathbb{N}$ there is $x$ such that

$$V_x \text{ is finite} \qquad\text{and}\qquad V_x\cap Z=\varnothing.$$

[§3, Lemma 2, p. 4](https://arxiv.org/pdf/2609.00419v1#page=4)

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Translation source: article. The endpoint is §3, Lemma 2, p. 4 of arXiv:2609.00419v1. It uses the §2 definition of a cylinder as one-one equivalence with the coded cylinder. Nat.pair instantiates the fixed computable pairing. Uniform computable enumerability is expressed by applying ComputablyEnumerableSet to the set of paired row memberships, using the same unary binary-word encoding as InfiniteHomogeneousRows. The article-specific Alphabeta Math Research Portal and designated defect report both returned HTTP 404. No matching local portal entry or report was found, so any statement correction remains unverified. https://arxiv.org/pdf/2609.00419v1#page=4 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
theorem FiniteMarkerAvoidance : ∀ (A : _root_.Set _root_.Nat) (V : _root_.Nat → _root_.Set _root_.Nat),
  let cyl : _root_.Set _root_.Nat :=
    {z | ∃ x n : _root_.Nat, x ∈ A ∧ z = _root_.Nat.pair x n}
  let encode : _root_.Nat → _root_.List _root_.Bool :=
    fun n => _root_.List.replicate n _root_.Bool.true
  let decode : _root_.List _root_.Bool → _root_.Option _root_.Nat :=
    fun w => if encode (_root_.List.length w) = w then
      _root_.Option.some (_root_.List.length w) else _root_.Option.none
  let ce : _root_.Set _root_.Nat → Prop :=
    _root_.ComputablyEnumerableSet encode decode
      (_root_.Function.LeftInverse.injective
        (show _root_.Function.LeftInverse _root_.List.length encode from
          fun _ => _root_.List.length_replicate))
      (by
        intro n
        simp [decode, encode])
      (fun w hw => _root_.ite_eq_right (fun h => hw ⟨_root_.List.length w, h⟩))
  ¬ (_root_.OneOneReducible (fun x : _root_.Nat => x ∈ A) (fun x : _root_.Nat => x ∈ cyl) ∧
    _root_.OneOneReducible (fun x : _root_.Nat => x ∈ cyl) (fun x : _root_.Nat => x ∈ A)) →
  ¬ ce A →
  ¬ ce (Aᶜ) →
  ce {z : _root_.Nat | ∃ x y : _root_.Nat, y ∈ V x ∧ z = _root_.Nat.pair x y} →
  (∀ x y : _root_.Nat, y ∈ V x → (y ∈ A ↔ x ∈ A)) →
  ∀ Z : _root_.Set _root_.Nat, _root_.Set.Finite Z →
    ∃ x : _root_.Nat, _root_.Set.Finite (V x) ∧ V x ∩ Z = ∅
```

Immediate internal dependencies: InfiniteHomogeneousRows, ComputablyEnumerableSet.

Existing repository dependencies: none.

Immediate external dependencies: CEAsCodeDomain, UniformFiniteStageCodes, MonotoneCodeStages, CodeStageLimit, BoundedSearchComputable, ExistentialComputableCE, PartialComputableSearch, PartialSearchDomain, PrimitiveRecursiveBoundedCodeEvaluation, BoundedCodeEvaluationCompleteness (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/FiniteMarkerAvoidance.json), [proof](Proofs/FiniteMarkerAvoidance.lean), [compilation evidence](evidence/FiniteMarkerAvoidance-compile.json).

## InfiniteHomogeneousRows: Infinite homogeneous rows give a one-one reduction from the cylinder

Main result; compiled and axiom-checked.

### Article

We first record a general observation that will be used twice in the proof. Suppose that $(W_x)_{x\in\mathbb{N}}$ is a uniformly c.e. $A$-homogeneous family and that every $W_x$ is infinite.

Fix a computable enumeration without repetitions

$$(x_0,n_0),(x_1,n_1),\ldots$$

of $\mathbb{N}^2$. We construct a function

$$G:\mathbb{N}^2\to\mathbb{N}$$

recursively along this enumeration. When treating $(x_i,n_i)$, wait for an element of $W_{x_i}$ which has not been used at any earlier step, and define $G(x_i,n_i)$ to be the first such element found.

Since $W_{x_i}$ is infinite and only finitely many values have been used before step $i$, this search terminates. Thus $G$ is a total computable injection satisfying

$$G(x,n)\in W_x$$

for all $x,n$. By the $A$-homogeneity of $(W_x)_{x\in\mathbb{N}}$,

$$A(G(x,n))=A(x).$$

Consequently, the map

$$\langle x,n\rangle\longmapsto G(x,n)$$

witnesses

$$\mathrm{Cyl}(A)\leq_1 A.$$

[§3, general observation in the proof of Lemma 2, pp. 4–5 (unnumbered)](https://arxiv.org/pdf/2609.00419v1#page=4)

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Translation source: article. This is the unnumbered observation in §3, pp. 4–5 of arXiv:2609.00419v1. Uniform computable enumerability is expressed by applying ComputablyEnumerableSet to the single set of Nat.pair codes for row membership, with natural numbers encoded as unary words over Bool. Nat.pair also supplies the fixed computable pairing in the definition of the cylinder. No matching local Alphabeta Math item or report was found. The article-specific portal and designated defect report returned HTTP 404, so any correction for this endpoint remains unverified. https://arxiv.org/pdf/2609.00419v1#page=4 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
theorem InfiniteHomogeneousRows : ∀ (A : _root_.Set _root_.Nat) (W : _root_.Nat → _root_.Set _root_.Nat),
  let encode : _root_.Nat → _root_.List _root_.Bool :=
    fun n => _root_.List.replicate n _root_.Bool.true
  let decode : _root_.List _root_.Bool → _root_.Option _root_.Nat :=
    fun w => if encode (_root_.List.length w) = w then
      _root_.Option.some (_root_.List.length w) else _root_.Option.none
  _root_.ComputablyEnumerableSet encode decode
    (_root_.Function.LeftInverse.injective
      (show _root_.Function.LeftInverse _root_.List.length encode from
        fun _ => _root_.List.length_replicate))
    (by
      intro n
      simp [decode, encode])
    (fun w hw => _root_.ite_eq_right (fun h => hw ⟨_root_.List.length w, h⟩))
    {z : _root_.Nat | ∃ x y : _root_.Nat, y ∈ W x ∧ z = _root_.Nat.pair x y} →
  (∀ x y : _root_.Nat, y ∈ W x → (y ∈ A ↔ x ∈ A)) →
  (∀ x : _root_.Nat, _root_.Set.Infinite (W x)) →
  _root_.OneOneReducible
    (fun z : _root_.Nat => ∃ x n : _root_.Nat, x ∈ A ∧ z = _root_.Nat.pair x n)
    (fun y : _root_.Nat => y ∈ A)
```

Immediate internal dependencies: ComputablyEnumerableSet.

Existing repository dependencies: none.

Immediate external dependencies: CEAsCodeDomain, UniformFiniteStageCodes, MonotoneCodeStages, CodeStageLimit, LeastComputableWitness, ComputableRecursion, ComputablePairing, ComputableUnpairing, PairingEquivalence, PrimitiveRecursiveBoundedCodeEvaluation, BoundedCodeEvaluationCompleteness (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/InfiniteHomogeneousRows.json), [proof](Proofs/InfiniteHomogeneousRows.lean), [compilation evidence](evidence/InfiniteHomogeneousRows-compile.json).

## CofiniteDomainLemma: Cofinite-domain lemma

Main result; compiled and axiom-checked.

### Article

A partial computable function $\varphi$ is a partial ascending self-reduction of $A$ if, for every $x\in\mathrm{dom}\,\varphi$,

$$\varphi(x)\gt x \qquad\text{and}\qquad A(\varphi(x))=A(x).$$

Assume that $A$ is nonrecursive and is not a cylinder. If $\varphi$ is a partial ascending self-reduction of $A$, then

$$\mathbb{N}\setminus\mathrm{dom}\,\varphi$$

is infinite.

[§3, Lemma 4, p. 6 (partial ascending self-reduction convention in Definition 3, p. 6)](https://arxiv.org/pdf/2609.00419v1#page=6)

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Translation source: article. Lemma 4 and Definition 3 in §3, p. 6 of arXiv:2609.00419v1 supply the endpoint. Nat.pair instantiates the fixed computable bijective pairing from §2. The Alphabeta Math article portal and its defect report returned HTTP 404. No local counterpart or correction for Lemma 4 was found. [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
theorem CofiniteDomainLemma : ∀ (A : _root_.Set _root_.Nat) (φ : _root_.Nat → _root_.Part _root_.Nat),
  let cyl : _root_.Set _root_.Nat :=
    {z | ∃ x n : _root_.Nat, x ∈ A ∧ z = _root_.Nat.pair x n}
  ¬ _root_.ComputablePred (fun x : _root_.Nat => x ∈ A) →
  ¬ (_root_.OneOneReducible (fun x : _root_.Nat => x ∈ A) (fun z : _root_.Nat => z ∈ cyl) ∧
     _root_.OneOneReducible (fun z : _root_.Nat => z ∈ cyl) (fun x : _root_.Nat => x ∈ A)) →
  _root_.Partrec φ →
  (∀ x y : _root_.Nat, y ∈ φ x → x < y ∧ (y ∈ A ↔ x ∈ A)) →
  _root_.Set.Infinite ({x : _root_.Nat | _root_.Part.Dom (φ x)}ᶜ)
```

Immediate internal dependencies: InfiniteHomogeneousRows, ComputablyEnumerableSet.

Existing repository dependencies: none.

Immediate external dependencies: UnboundedInfiniteNatSet, ComputablePredComplement, PartialComputableConditional, ComputableRecursion, ComputableRangeCE, ComputablePairing, PairingEquivalence, PrimitiveRecursiveListMembership, PartialComputableTotalization, PartialRecursiveBoundedRace (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/CofiniteDomainLemma.json), [proof](Proofs/CofiniteDomainLemma.lean), [compilation evidence](evidence/CofiniteDomainLemma-compile.json).

## LocalInterpolation: Local interpolation

Main result; compiled and axiom-checked.

### Article

Assume that $A$ is nonrecursive, is not a cylinder, and neither $A$ nor $\overline A$ is c.e. Then there is a set $C\equiv_{\mathrm{m}} A$ such that

$$[A]_{\mathrm{fo}}\lt [C]_{\mathrm{fo}}\lt [\mathrm{Cyl}(A)]_{\mathrm{fo}}.$$

[§4, Theorem 5, p. 8](https://arxiv.org/pdf/2609.00419v1#page=8)

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Translation source: article. The selected endpoint is Theorem 5 in §4, p. 8 of arXiv:2609.00419v1. Nat.pair instantiates the fixed computable bijective pairing, and each strict finite-one degree comparison is expressed by forward reducibility and failure of reverse reducibility, as specified in §2. Computable enumerability uses the same unary Boolean encoding as PriorityRequirements. The article-specific Alphabeta Math Research Portal and the designated defect report both returned HTTP 404. The local source search found no matching report or portal counterpart, so no statement correction could be verified. https://arxiv.org/pdf/2609.00419v1#page=8 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
theorem LocalInterpolation : ∀ A : _root_.Set _root_.Nat,
  let cyl : _root_.Set _root_.Nat :=
    {z | ∃ x n : _root_.Nat, x ∈ A ∧ z = _root_.Nat.pair x n}
  let encode (n : _root_.Nat) := _root_.List.replicate n _root_.Bool.true
  let decode (w : _root_.List _root_.Bool) : _root_.Option _root_.Nat :=
    if encode (_root_.List.length w) = w then _root_.Option.some (_root_.List.length w)
    else _root_.Option.none
  let ce : _root_.Set _root_.Nat → Prop :=
    _root_.ComputablyEnumerableSet encode decode
      (_root_.List.replicate_left_injective _root_.Bool.true)
      (fun n => by simp [decode, encode])
      (fun w hw => _root_.ite_eq_right (fun h => hw ⟨_root_.List.length w, h⟩))
  let finiteOneReducible (X Y : _root_.Set _root_.Nat) : Prop :=
    ∃ f : _root_.Nat → _root_.Nat, _root_.Computable f ∧
      (∀ y : _root_.Nat, _root_.Set.Finite (_root_.Set.preimage f ({y} : _root_.Set _root_.Nat))) ∧
      (∀ x : _root_.Nat, x ∈ X ↔ f x ∈ Y)
  let finiteOneStrict (X Y : _root_.Set _root_.Nat) : Prop :=
    finiteOneReducible X Y ∧ ¬ finiteOneReducible Y X
  ¬ _root_.ComputablePred (fun x : _root_.Nat => x ∈ A) →
  ¬ (_root_.OneOneReducible (fun x : _root_.Nat => x ∈ A) (fun x : _root_.Nat => x ∈ cyl) ∧
     _root_.OneOneReducible (fun x : _root_.Nat => x ∈ cyl) (fun x : _root_.Nat => x ∈ A)) →
  ¬ ce A →
  ¬ ce (Aᶜ) →
  ∃ C : _root_.Set _root_.Nat,
    _root_.ManyOneDegree.of C = _root_.ManyOneDegree.of A ∧
    finiteOneStrict A C ∧ finiteOneStrict C cyl
```

Immediate internal dependencies: PriorityRequirements, ProfileRealization, PullbackReductions, HomogeneousRowsFromCylinderReduction, AscendingSelfReductionFromPullbackReduction, CylinderGreatestFiniteOneDegree, ComputablyEnumerableSet, HaltingSigmaOneCompleteness.

Existing repository dependencies: none.

Immediate external dependencies: FiniteFibresFinitePreimage, PreorderQuotientOrder, ComputablePairing, PairingEquivalence, InfiniteRangeOfInjective (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/LocalInterpolation.json), [proof](Proofs/LocalInterpolation.lean), [compilation evidence](evidence/LocalInterpolation-compile.json).

## PriorityRequirements: A set c.e. in the halting problem meeting the upper and lower requirements

Main result; compiled and axiom-checked.

### Article

Assume that $A$ is nonrecursive, is not a cylinder, and neither $A$ nor $\overline A$ is c.e.

Fix an effective enumeration

$$\bigl((V_x^e)_{x\in\mathbb{N}}\bigr)_{e\in\mathbb{N}}$$

of all uniformly c.e. families, and an effective enumeration $(\varphi_e)_{e\in\mathbb{N}}$ of all partial computable functions.

Fix standard finite stage approximations

$$V^e_{x,0}\subseteq V^e_{x,1}\subseteq\cdots, \qquad V_x^e=\bigcup_s V^e_{x,s},$$

uniformly computable in $e,x,s$.

We construct a set $N$ which is c.e. in $0'$, satisfying the requirements

$$\mathcal U_e:\quad (V_x^e)_x\text{ is }A\text{-homogeneous} \Longrightarrow \exists x\, [V_x^e\text{ finite and }V_x^e\subseteq N],$$

and

$$\mathcal L_e:\quad \varphi_e\text{ is a partial ascending self-reduction of }A \Longrightarrow \exists m\, [m\notin N\cup\mathrm{dom}\,\varphi_e].$$

Use the priority ordering

$$\mathcal U_0\gt\mathcal L_0\gt \mathcal U_1\gt\mathcal L_1\gt\cdots.$$

The construction does not attempt to decide whether either antecedent in the requirements holds. Its actions are independent of $A$. The hypotheses involving $A$ are used only in the verification: Lemma 2 is used to verify the $\mathcal U_e$-requirements, while Lemma 4 is used to verify the $\mathcal L_e$-requirements.

Therefore every $\mathcal U_e$ is satisfied.

At each stage only finitely many requirements are visited, each strategy performs only finitely many $0'$-decidable tests, and only a finite set is enumerated into $N$. Thus the enumeration of $N$ is computable in $0'$.

Let

$$P=\mathbb{N}\setminus N.$$

Since $N$ is c.e. in $0'$, we have $N\in\Sigma^0_2$. Therefore $P=\mathbb N\setminus N$ belongs to $\Pi^0_2$.

[§4, proof of Theorem 5, pp. 8–10 (requirements on p. 8 and verification on pp. 9–10)](https://arxiv.org/pdf/2609.00419v1#page=8)

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Translation source: article. The endpoint is the priority-requirements result in §4, proof of Theorem 5, pp. 8–10 of arXiv:2609.00419v1. Nat.pair and Nat.unpair implement the fixed computable bijective pairing, and the paired domain of the effective partial-function enumeration supplies the halting oracle. The stage approximations use binary finite-set codes. Priority indices 2e and 2e+1 represent the upper and lower requirements in the stated order. The same N serves every A satisfying the hypotheses, as the construction is independent of A. The article-specific Alphabeta Math Research Portal and designated defect report both returned HTTP 404. No matching local entry or correction for this result was found. https://arxiv.org/pdf/2609.00419v1#page=8 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
theorem PriorityRequirements : ∀ (φ : _root_.Nat → _root_.Nat → _root_.Part _root_.Nat)
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
      ∀ p : _root_.Nat, if p % 2 = 0 then upper (p / 2) else lower (p / 2)
```

Immediate internal dependencies: FiniteMarkerAvoidance, CofiniteDomainLemma, FixedStageRowStability, FiniteInjuryAndStabilization, RelativeComputabilityAndEnumerability, ArithmeticalHierarchyLevels, AcceptableNumbering, ComputablyEnumerableSet, OracleNegativePullbackDecision, PriorityBoundedOracleSearches, PriorityCodedVisitTrace, SingletonOracleTapeCompilation, CETapeOracleSigmaTwo.

Existing repository dependencies: none.

Immediate external dependencies: PartialCodeSurjectivity, CEAsCodeDomain, UniformFiniteStageCodes, MonotoneCodeStages, CodeStageLimit, OracleComputableRecursion, OracleCodeExistence, OracleStageEvaluationPrimitiveRecursive, OracleStageEventuallyCorrect, PersistentOracleStageSound, OracleFiniteStageConvergence, UnboundedInfiniteNatSet, NativeRelativeMinimization, PartialComputableSearch, PartialSearchDomain, PriorityFiniteSetBitCodes, PriorityFiniteSetBitMembership, AlphabetaHaltingCompleteness, AlphabetaSigmaOneStageSearch, AlphabetaPostTheorem, AlphabetaRecognizableEnumerable (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/PriorityRequirements.json), [proof](Proofs/PriorityRequirements.lean), [compilation evidence](evidence/PriorityRequirements-compile.json).

## FixedStageRowStability: The halting problem decides row stability at a fixed stage

Main result; compiled and axiom-checked.

### Article

Let $Z_e$ be the finite set of markers currently carried by higher-priority $\mathcal L$-requirements. If $\mathcal U_e$ has not yet acted, search among pairs $x,t\leq s$ for one such that

$$V^e_{x,t}\cap Z_e=\varnothing, \qquad V^e_{x,t}\subseteq\{0,\ldots,s\},$$

and

$$\forall r\geq t\, [V^e_{x,r}=V^e_{x,t}].$$

The last condition is decidable in $0'$. Indeed, for fixed $e,x,t$, failure of the stability condition is the $\Sigma^0_1$ statement

$$\exists r\geq t\, [V^e_{x,r}\neq V^e_{x,t}].$$

Hence $0'$ decides whether the row receives any new element after the specified stage $t$. Notice that this does not amount to deciding, with $0'$, whether an arbitrary c.e. row is finite.

[§4, proof of Theorem 5, p. 8, Strategy for the upper requirement (unnumbered)](https://arxiv.org/pdf/2609.00419v1#page=8)

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Translation source: article. The endpoint is the fixed-stage oracle decision in the upper-requirement strategy of §4, p. 8, of arXiv:2609.00419v1. The stage sets are finite and increase to their row unions. The exhaustion hypothesis represents the enumeration of all uniformly c.e. families by their paired domains. Stage outputs use binary finite-set codes. The decision takes Nat.pair e (Nat.pair x t) as input and uses the paired halting set of the acceptable numbering as the oracle. The article-specific portal and defect report both returned HTTP 404, so no correction could be verified. https://arxiv.org/pdf/2609.00419v1#page=8 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
theorem FixedStageRowStability : ∀ φ : _root_.Nat → _root_.Nat → _root_.Part _root_.Nat,
  _root_.AcceptableNumbering φ →
  ∀ stage : _root_.Nat → _root_.Nat → _root_.Nat → _root_.Finset _root_.Nat,
    _root_.Computable (fun p : _root_.Nat × _root_.Nat × _root_.Nat =>
      (_root_.Equiv.symm _root_.Finset.equivBitIndices)
        (stage p.1 p.2.1 p.2.2)) →
    (∀ e x : _root_.Nat, _root_.Monotone (stage e x)) →
    let V : _root_.Nat → _root_.Nat → _root_.Set _root_.Nat :=
      fun e x => {y | ∃ s : _root_.Nat, y ∈ stage e x s}
    (∀ i : _root_.Nat, ∃ e : _root_.Nat, ∀ x y : _root_.Nat,
      y ∈ V e x ↔ _root_.Part.Dom (φ i (_root_.Nat.pair x y))) →
    let K : _root_.Set _root_.Nat := {n |
      let (i, z) := _root_.Nat.unpair n
      _root_.Part.Dom (φ i z)}
    (_root_.RelativeComputabilityAndEnumerability K).1 {n |
      let (e, p) := _root_.Nat.unpair n
      let (x, t) := _root_.Nat.unpair p
      ∀ r : _root_.Nat, t ≤ r → stage e x r = stage e x t}
```

Immediate internal dependencies: HaltingSigmaOneCompleteness, RelativeComputabilityAndEnumerability, AcceptableNumbering, OracleNegativePullbackDecision.

Existing repository dependencies: none.

Immediate external dependencies: UniformFiniteStageCodes, ExistentialComputableCE (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/FixedStageRowStability.json), [proof](Proofs/FixedStageRowStability.lean), [compilation evidence](evidence/FixedStageRowStability-compile.json).

## FiniteInjuryAndStabilization: Finite injury and stabilization of marker restraints

Main result; compiled and axiom-checked.

### Article

Observe that an active marker carried by an $\mathcal L_e$-strategy can be injured only by a higher-priority $\mathcal U$-strategy. Indeed, a lower-priority $\mathcal U$-strategy either had already acted when the marker was chosen, in which case its stabilized row was already contained in $N$ and hence could not contain the marker, or had not yet acted, in which case, as long as the marker remains active, it includes the marker among its restraints and therefore must choose a row disjoint from it.

By definition, once the $\mathcal U_i$-strategy acts, it declares $\mathcal U_i$ permanently satisfied and is never eligible to act again. Indeed, its chosen stabilized row is then entirely contained in $N$.

Thus every $\mathcal U_i$ acts at most once. Hence, for every $e$, there is a stage $s_e$ after which no $\mathcal U_i$ of higher priority than $\mathcal L_e$ acts. By the preceding observation, $\mathcal L_e$ cannot be injured after stage $s_e$.

If $\mathcal L_e$ carries a marker at the end of stage $s_e$, that marker is final. Otherwise, either it chooses a marker at some later visit, in which case that marker is final, or it remains permanently markerless. Thus every $\mathcal L_e$ eventually reaches a final state. Consequently, for every fixed requirement, the finite set of active markers carried by higher-priority $\mathcal L$-strategies eventually stabilizes.

[§4, proof of Theorem 5, p. 9, Verification (unnumbered)](https://arxiv.org/pdf/2609.00419v1#page=9)

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Translation source: article. The endpoint is the unnumbered Verification in §4 of arXiv:2609.00419v1, p. 9, with the construction conventions on pp. 8–9. The trace records the state after the first k visits at stage s, with priority indices 2i for upper requirements and 2e+1 for lower requirements. The upper strategy must choose the least eligible pair in a fixed computable ordering. The article leaves the ordering itself unspecified. A markerless lower strategy must choose the least eligible number. Uniformly c.e. families are expressed using paired domains, and their uniformly computable increasing stage approximations use binary finite-set codes. The lower strategy tests nonmembership in the domain of the partial function at its index in the effective enumeration. The article-specific Alphabeta Math portal and designated defect report returned HTTP 404 when checked. No local counterpart or correction for this endpoint was verified. https://arxiv.org/pdf/2609.00419v1#page=9 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
theorem FiniteInjuryAndStabilization : ∀ (φ : _root_.Nat → _root_.Nat → _root_.Part _root_.Nat)
  (V : _root_.Nat → _root_.Nat → _root_.Set _root_.Nat)
  (rowAt : _root_.Nat → _root_.Nat → _root_.Nat → _root_.Finset _root_.Nat)
  (pairBefore : (_root_.Nat × _root_.Nat) → (_root_.Nat × _root_.Nat) → Prop)
  (chosenPair : _root_.Nat → _root_.Nat → _root_.Option (_root_.Nat × _root_.Nat))
  (satisfied : _root_.Nat → _root_.Nat → Prop)
  (content : _root_.Nat → _root_.Nat → _root_.Finset _root_.Nat)
  (marker : _root_.Nat → _root_.Nat → _root_.Nat → _root_.Option _root_.Nat),
  let upper (i : _root_.Nat) := 2 * i
  let lower (e : _root_.Nat) := 2 * e + 1
  let acts (s i : _root_.Nat) : Prop :=
    ∃ q, chosenPair s i = _root_.Option.some q
  let injured (s k e : _root_.Nat) : Prop :=
    k < s ∧ (∃ m, marker s k e = _root_.Option.some m) ∧
      marker s (k + 1) e = _root_.Option.none
  let restraints (s k p : _root_.Nat) : _root_.Set _root_.Nat :=
    {m | ∃ e, lower e < p ∧ marker s k e = _root_.Option.some m}
  let upperCandidate (s i : _root_.Nat) (q : _root_.Nat × _root_.Nat) : Prop :=
    let F := rowAt i q.1 q.2
    q.1 ≤ s ∧ q.2 ≤ s ∧
      (∀ m ∈ F, m ≤ s ∧ m ∉ restraints s (upper i) (upper i)) ∧
      (∀ r, q.2 ≤ r → rowAt i q.1 r = F)
  let lowerCandidate (s e m : _root_.Nat) : Prop :=
    m ≤ s ∧ ¬ _root_.Part.Dom (φ e m) ∧ m ∉ content s (lower e) ∧
      (∀ j, marker s (lower e) j ≠ _root_.Option.some m)
  ∀ (_effectiveFunctions : _root_.Partrec₂ φ)
    (_allPartialComputable : ∀ f : _root_.Nat → _root_.Part _root_.Nat,
      _root_.Partrec f → ∃ e, φ e = f)
    (_effectiveFamilies : _root_.REPred
      (fun p : _root_.Nat × _root_.Nat × _root_.Nat => p.2.2 ∈ V p.1 p.2.1))
    (_allUniformCEFamilies : ∀ i : _root_.Nat, ∃ e : _root_.Nat, ∀ x y : _root_.Nat,
      y ∈ V e x ↔ _root_.Part.Dom (φ i (_root_.Nat.pair x y)))
    (_computableStages : _root_.Computable
      (fun p : _root_.Nat × _root_.Nat × _root_.Nat =>
        (_root_.Equiv.symm _root_.Finset.equivBitIndices) (rowAt p.1 p.2.1 p.2.2)))
    (_increasingStages : ∀ i x, _root_.Monotone (rowAt i x))
    (_stageUnions : ∀ i x y, y ∈ V i x ↔ ∃ r : _root_.Nat, y ∈ rowAt i x r)
    (_pairOrder : _root_.IsStrictTotalOrder (_root_.Nat × _root_.Nat) pairBefore)
    (_computablePairOrder : _root_.ComputablePred
      (fun p : (_root_.Nat × _root_.Nat) × (_root_.Nat × _root_.Nat) =>
        pairBefore p.1 p.2))
    (_initial : content 0 0 = ∅ ∧
      (∀ e, marker 0 0 e = _root_.Option.none) ∧ (∀ i, ¬ satisfied 0 i))
    (_nextStage : ∀ s, content (s + 1) 0 = content s s ∧
      (∀ e, marker (s + 1) 0 e = marker s s e))
    (_activeMarkers : ∀ s k e m, k ≤ s → marker s k e = _root_.Option.some m →
      m ∉ content s k ∧ (∀ j, marker s k j = _root_.Option.some m → j = e))
    (_eligible : ∀ s i, acts s i → upper i < s ∧ ¬ satisfied s i)
    (_permanent : ∀ s i, satisfied (s + 1) i ↔ satisfied s i ∨ acts s i)
    (_upperVisit : ∀ s i, upper i < s →
      let k := upper i
      match chosenPair s i with
      | _root_.Option.none =>
        (satisfied s i ∨ ∀ q, ¬ upperCandidate s i q) ∧
        content s (k + 1) = content s k ∧
        (∀ e, marker s (k + 1) e = marker s k e)
      | _root_.Option.some q =>
        let F := rowAt i q.1 q.2
        upperCandidate s i q ∧
        (∀ p, upperCandidate s i p → ¬ pairBefore p q) ∧
        content s (k + 1) = content s k ∪ F ∧
        (∀ e, marker s (k + 1) e =
          match marker s k e with
          | _root_.Option.none => _root_.Option.none
          | _root_.Option.some m =>
            if k < lower e ∧ m ∈ F then _root_.Option.none else _root_.Option.some m))
    (_lowerVisit : ∀ s e, lower e < s →
      let k := lower e
      content s (k + 1) = content s k ∧
      (∀ j, j ≠ e → marker s (k + 1) j = marker s k j) ∧
      (match marker s k e with
      | _root_.Option.some m => marker s (k + 1) e = _root_.Option.some m
      | _root_.Option.none =>
        match marker s (k + 1) e with
        | _root_.Option.none => ∀ m, ¬ lowerCandidate s e m
        | _root_.Option.some m =>
          lowerCandidate s e m ∧ (∀ n, lowerCandidate s e n → m ≤ n))),
    (∀ s k e, injured s k e →
      ∃ i q m, k = upper i ∧ upper i < lower e ∧
        chosenPair s i = _root_.Option.some q ∧
        marker s k e = _root_.Option.some m ∧ m ∈ rowAt i q.1 q.2) ∧
    (∀ i s t, acts s i → acts t i → s = t) ∧
    (∀ e, _root_.Set.Finite {event : _root_.Nat × _root_.Nat | injured event.1 event.2 e}) ∧
    (∀ e, ∃ s₀,
      (∀ s i, s₀ < s → upper i < lower e → ¬ acts s i) ∧
      (∀ s k, s₀ < s → ¬ injured s k e) ∧
      (∀ m s k, marker s₀ s₀ e = _root_.Option.some m →
        s₀ < s → k ≤ s → marker s k e = _root_.Option.some m)) ∧
    (∀ e, ∃ s₁ final, ∀ s k, s₁ ≤ s → k ≤ s → marker s k e = final) ∧
    (∀ p, ∃ (s₁ : _root_.Nat) (Z : _root_.Set _root_.Nat), _root_.Set.Finite Z ∧
      ∀ s k, s₁ ≤ s → k ≤ s → restraints s k p = Z)
```

Immediate internal dependencies: none.

Existing repository dependencies: none.

Immediate external dependencies: FiniteInjuryByCause, FiniteInjuryStops (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/FiniteInjuryAndStabilization.json), [proof](Proofs/FiniteInjuryAndStabilization.lean), [compilation evidence](evidence/FiniteInjuryAndStabilization-compile.json).

## PullbackReductions: Many-one equivalence and one-one reduction for the pullback

Main result; compiled and axiom-checked.

### Article

By Lemma 1, fix a total computable surjection $p$ with computable section such that

$$I_p=P,$$

and put

$$C=p^{-1}(A).$$

Let $s$ be a computable section of $p$. For every $y\in\mathbb{N}$,

$$y\in A \quad\Longleftrightarrow\quad p(s(y))\in A \quad\Longleftrightarrow\quad s(y)\in C.$$

Since $s$ is injective, it witnesses

$$A\leq_1 C,$$

and hence

$$A\leq_{\mathrm{fo}}C.$$

On the other hand, for every $u\in\mathbb{N}$,

$$u\in C \quad\Longleftrightarrow\quad p(u)\in A,$$

so $p$ witnesses

$$C\leq_{\mathrm{m}}A.$$

Since $A\leq_1C$ implies $A\leq_{\mathrm{m}}C$, it follows that

$$C\equiv_{\mathrm{m}}A.$$

[§4, proof of Theorem 5, p. 11 (unnumbered)](https://arxiv.org/pdf/2609.00419v1#page=11)

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Translation source: article. The selected endpoint is the pullback reduction in §4, proof of Theorem 5, p. 11 of arXiv:2609.00419v1. Many-one equivalence is expressed as equality of the corresponding many-one degrees. The article-specific Alphabeta Math Research Portal and the designated defect report both returned HTTP 404. No matching local entry or correction could be verified. https://arxiv.org/pdf/2609.00419v1#page=11 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
theorem PullbackReductions : ∀ (A P : _root_.Set _root_.Nat) (p s : _root_.Nat → _root_.Nat),
  _root_.Computable p →
  _root_.Function.Surjective p →
  {y : _root_.Nat | _root_.Set.Infinite (_root_.Set.preimage p ({y} : _root_.Set _root_.Nat))} = P →
  _root_.Computable s →
  _root_.Function.RightInverse s p →
  let C : _root_.Set _root_.Nat := _root_.Set.preimage p A
  let finiteOneReducible : Prop :=
    ∃ f : _root_.Nat → _root_.Nat, _root_.Computable f ∧
      (∀ y : _root_.Nat, _root_.Set.Finite (_root_.Set.preimage f ({y} : _root_.Set _root_.Nat))) ∧
      (∀ x : _root_.Nat, x ∈ A ↔ f x ∈ C)
  _root_.OneOneReducible (fun x : _root_.Nat => x ∈ A) (fun x : _root_.Nat => x ∈ C) ∧
    finiteOneReducible ∧ _root_.ManyOneReducibilityOnNat C A ∧
    _root_.ManyOneDegree.of C = _root_.ManyOneDegree.of A
```

Immediate internal dependencies: ProfileRealization, ReducibilityImplications, ManyOneReducibilityOnNat.

Existing repository dependencies: none.

Immediate external dependencies: ManyOneDegreeEquality (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/PullbackReductions.json), [proof](Proofs/PullbackReductions.lean), [compilation evidence](evidence/PullbackReductions-compile.json).

## HomogeneousRowsFromCylinderReduction: Homogeneous rows from a reduction of the cylinder

Main result; compiled and axiom-checked.

### Article

By Lemma 1, fix a total computable surjection $p$ with computable section such that

$$I_p=P,$$

and put

$$C=p^{-1}(A).$$

Suppose conversely that

$$h:\mathrm{Cyl}(A)\leq_{\mathrm{fo}} C.$$

For each $x$, define

$$V_x=\{p(h(\langle x,n\rangle)):n\in\mathbb{N}\}.$$

Although $p$ was chosen only after the construction of $N$, there is no circularity here. Once $p$ and the hypothetical reduction $h$ are fixed, $(V_x)_{x\in\mathbb{N}}$ is an ordinary uniformly c.e. family. Consequently, there is an index $e$ such that

$$V_x=V_x^e \qquad\text{for every }x.$$

This family is $A$-homogeneous. Indeed, if

$$y=p(h(\langle x,n\rangle)),$$

then

$$y\in A \iff h(\langle x,n\rangle)\in C \iff \langle x,n\rangle\in\mathrm{Cyl}(A) \iff x\in A.$$

[§4, proof of Theorem 5, p. 11 (unnumbered); C and p are defined earlier on p. 11](https://arxiv.org/pdf/2609.00419v1#page=11)

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Translation source: article. The unnumbered endpoint in the proof of Theorem 5, §4, p. 11 of arXiv:2609.00419v1 fixes a computable surjection with a computable section and profile P, and obtains uniformly c.e. homogeneous rows and a common enumeration index from the finite-one reduction. Nat.pair instantiates the fixed computable pairing. ComputablyEnumerableSet applies to the coded row graph, and monotone computable finite stages present the fixed effective enumeration of all uniformly c.e. families. The article-specific Alphabeta Math portal and designated defect-report URL both returned HTTP 404, and the local portal search found no matching collection or report. Any correction for this endpoint remains unverified. https://arxiv.org/pdf/2609.00419v1#page=11 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
theorem HomogeneousRowsFromCylinderReduction : ∀ (A P : _root_.Set _root_.Nat) (p : _root_.Nat → _root_.Nat),
  _root_.Computable p →
  _root_.Function.Surjective p →
  (∃ s : _root_.Nat → _root_.Nat,
    _root_.Computable s ∧ _root_.Function.RightInverse s p) →
  {y : _root_.Nat | _root_.Set.Infinite (_root_.Set.preimage p ({y} : _root_.Set _root_.Nat))} = P →
  let C := _root_.Set.preimage p A
  let cyl : _root_.Set _root_.Nat :=
    {z | ∃ x n : _root_.Nat, x ∈ A ∧ z = _root_.Nat.pair x n}
  ∀ h : _root_.Nat → _root_.Nat,
    _root_.Computable h →
    (∀ y : _root_.Nat, _root_.Set.Finite (_root_.Set.preimage h ({y} : _root_.Set _root_.Nat))) →
    (∀ z : _root_.Nat, z ∈ cyl ↔ h z ∈ C) →
    let encode : _root_.Nat → _root_.List _root_.Bool :=
      fun n => _root_.List.replicate n _root_.Bool.true
    let decode : _root_.List _root_.Bool → _root_.Option _root_.Nat :=
      fun w => if encode (_root_.List.length w) = w then
        _root_.Option.some (_root_.List.length w) else _root_.Option.none
    let uniformlyCE (W : _root_.Nat → _root_.Set _root_.Nat) : Prop :=
      _root_.ComputablyEnumerableSet encode decode
        (_root_.Function.LeftInverse.injective
          (show _root_.Function.LeftInverse _root_.List.length encode from
            fun _ => _root_.List.length_replicate))
        (fun n => by simp [decode, encode])
        (fun w hw => _root_.ite_eq_right (fun hEq => hw ⟨_root_.List.length w, hEq⟩))
        {z : _root_.Nat | ∃ x y : _root_.Nat, y ∈ W x ∧ z = _root_.Nat.pair x y}
    ∀ stage : _root_.Nat → _root_.Nat → _root_.Nat → _root_.Finset _root_.Nat,
      _root_.Computable (fun t : _root_.Nat × _root_.Nat × _root_.Nat =>
        (_root_.Equiv.symm _root_.Finset.equivBitIndices) (stage t.1 t.2.1 t.2.2)) →
      (∀ e x : _root_.Nat, _root_.Monotone (stage e x)) →
      let indexedRows (e x : _root_.Nat) : _root_.Set _root_.Nat :=
        {y | ∃ s : _root_.Nat, y ∈ stage e x s}
      (∀ W : _root_.Nat → _root_.Set _root_.Nat,
        uniformlyCE W → ∃ e : _root_.Nat, ∀ x : _root_.Nat, W x = indexedRows e x) →
      let V (x : _root_.Nat) : _root_.Set _root_.Nat :=
        _root_.Set.range (fun n : _root_.Nat => p (h (_root_.Nat.pair x n)))
      uniformlyCE V ∧
        (∃ e : _root_.Nat, ∀ x : _root_.Nat, V x = indexedRows e x) ∧
        (∀ x y : _root_.Nat, y ∈ V x → (y ∈ A ↔ x ∈ A))
```

Immediate internal dependencies: ProfileRealization, ComputablyEnumerableSet.

Existing repository dependencies: none.

Immediate external dependencies: ComputablePairing, ComputableRangeCE, ComputableUnpairing, PairingEquivalence (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/HomogeneousRowsFromCylinderReduction.json), [proof](Proofs/HomogeneousRowsFromCylinderReduction.lean), [compilation evidence](evidence/HomogeneousRowsFromCylinderReduction-compile.json).

## AscendingSelfReductionFromPullbackReduction: Ascending self-reduction from a finite-one reduction of the pullback

Main result; compiled and axiom-checked.

### Article

By Lemma 1, fix a total computable surjection $p$ with computable section such that

$$I_p=P,$$

and put

$$C=p^{-1}(A).$$

Suppose, toward a contradiction, that

$$h:C\leq_{\mathrm{fo}}A.$$

Define the partial computable function $f_h$ by

$$f_h(y)=h(u),$$

where $u$ is the least number such that

$$p(u)=y \qquad\text{and}\qquad h(u)\gt y.$$

Whenever $f_h(y)$ is defined,

$$f_h(y)\gt y$$

and, because $h$ is a reduction,

$$A(f_h(y)) =A(h(u)) =A(p(u)) =A(y).$$

Thus $f_h$ is a partial ascending self-reduction of $A$.

If $y\in P$, then $p^{-1}(y)$ is infinite. Since $h$ is finite-one,

$$h^{-1}(\{0,\ldots,y\}) = \bigcup_{z\leq y}h^{-1}(z)$$

is finite. Hence some $u\in p^{-1}(y)$ satisfies $h(u)\gt y$, and so

$$P\subseteq\mathrm{dom}\, f_h.$$

[§4, proof of Theorem 5, pp. 11–12 (p. 11 defines p and C, p. 12 states the result)](https://arxiv.org/pdf/2609.00419v1#page=12)

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Translation source: article. The selected unnumbered result in §4 of arXiv:2609.00419v1 fixes p and C on p. 11 and states the conclusion on p. 12. Nat.rfind preserves the least admissible input convention for f_h. The article-specific Alphabeta Math Research Portal and designated defect report both returned HTTP 404. No local counterpart or statement correction could be verified. https://arxiv.org/pdf/2609.00419v1#page=12 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
theorem AscendingSelfReductionFromPullbackReduction : ∀ (A P : _root_.Set _root_.Nat) (p h : _root_.Nat → _root_.Nat),
  _root_.Computable p →
  _root_.Function.Surjective p →
  (∃ s : _root_.Nat → _root_.Nat,
    _root_.Computable s ∧ _root_.Function.RightInverse s p) →
  {y : _root_.Nat | _root_.Set.Infinite (_root_.Set.preimage p ({y} : _root_.Set _root_.Nat))} = P →
  let C : _root_.Set _root_.Nat := _root_.Set.preimage p A
  _root_.Computable h →
  (∀ z : _root_.Nat, _root_.Set.Finite (_root_.Set.preimage h ({z} : _root_.Set _root_.Nat))) →
  (∀ u : _root_.Nat, u ∈ C ↔ h u ∈ A) →
  let f_h : _root_.Nat → _root_.Part _root_.Nat := fun y =>
    _root_.Part.map h
      (_root_.Nat.rfind (fun u => _root_.Part.some (_root_.Decidable.decide (p u = y ∧ y < h u))))
  _root_.Partrec f_h ∧
  (∀ y z : _root_.Nat, z ∈ f_h y → y < z ∧ (z ∈ A ↔ y ∈ A)) ∧
  P ⊆ {y : _root_.Nat | _root_.Part.Dom (f_h y)}
```

Immediate internal dependencies: ProfileRealization.

Existing repository dependencies: none.

Immediate external dependencies: PartialComputableSearch, PartialSearchDomain, FiniteFibresFinitePreimage, PartialSearchSpecification, PartialSearchComputablePostcomposition (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/AscendingSelfReductionFromPullbackReduction.json), [proof](Proofs/AscendingSelfReductionFromPullbackReduction.lean), [compilation evidence](evidence/AscendingSelfReductionFromPullbackReduction-compile.json).

## PriorityConstructionEffectiveness: Effectiveness of the priority construction

Main result; compiled and axiom-checked.

### Article

Several points concerning the effectiveness of the construction are worth emphasizing.

First, for a partial computable function $\varphi_e$, the condition

$$m\notin\mathrm{dom}\,\varphi_e$$

is decidable in $0'$. Thus an $\mathcal L_e$-strategy can choose a marker with permanent certification that it lies outside $\mathrm{dom}\,\varphi_e$.

Second, a $\mathcal U$-requirement acting at stage $s$ enumerates into $N$ only numbers at most $s$. Consequently, no action before stage $m$ can enumerate $m$ into $N$. Once the higher-priority $\mathcal U$-requirements have ceased acting, a newly chosen marker is also protected from every lower-priority $\mathcal U$-requirement. One which has already acted selected a row already contained in $N$; since the marker is chosen outside the current content of $N$, that row cannot contain it. One which has not yet acted includes the marker among its restraints and therefore selects a row disjoint from it.

Finally, the finite parameters hardcoded in the proofs of Lemmas 2 and 4 need not be recovered by the priority construction. For a $\mathcal U_e$-requirement, the current finite restraint set $Z_e$ is explicitly available at every stage. Once it stabilizes, Lemma 2 guarantees the existence of a finite row disjoint from it, and the bounded $0'$-search eventually finds a stabilization pair $(x,t)$ without having to recognize that the restraints have stabilized. For an $\mathcal L_e$-requirement, Lemma 4 is used only to guarantee arbitrarily large elements of

$$\mathbb{N}\setminus\mathrm{dom}\,\varphi_e,$$

while each individual candidate is checked by the $0'$-test described above. Thus the two lemmas are used only existentially in the verification, and no uniform computation of the finite parameters appearing in their proofs is required.

[§4, Remark 6, p. 13](https://arxiv.org/pdf/2609.00419v1#page=13)

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Translation source: article. The endpoint is Remark 6 in §4, p. 13 of arXiv:2609.00419v1. The stage and visit conventions come from the construction on pp. 8–9. The Lean statement uses Nat.pair for the fixed pairing, the paired domain set for 0′, and binary codes for finite sets. The trace visits the first s requirements at stage s with upper priority index 2e and lower priority index 2e+1. Upper search takes the current restraints, while lower search takes the current content of N and active markers. The searches are uniform in the requirement index, stage and these finite inputs. The existence clauses for a finite disjoint row and arbitrarily large numbers outside the domain express the existential use of Lemmas 2 and 4. The article-specific Alphabeta Math Research Portal and designated defect report both returned HTTP 404. The local collections supplied no matching report, portal counterpart or correction for Remark 6. https://arxiv.org/pdf/2609.00419v1#page=13 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
theorem PriorityConstructionEffectiveness : ∀ (φ : _root_.Nat → _root_.Nat → _root_.Part _root_.Nat)
  (V : _root_.Nat → _root_.Nat → _root_.Set _root_.Nat)
  (rowAt : _root_.Nat → _root_.Nat → _root_.Nat → _root_.Finset _root_.Nat)
  (pairBefore : (_root_.Nat × _root_.Nat) → (_root_.Nat × _root_.Nat) → Prop),
  _root_.Partrec₂ φ →
  (∀ f : _root_.Nat → _root_.Part _root_.Nat,
    _root_.Partrec f → ∃ e, φ e = f) →
  _root_.REPred (fun p : _root_.Nat × _root_.Nat × _root_.Nat =>
    p.2.2 ∈ V p.1 p.2.1) →
  (∀ i : _root_.Nat, ∃ e : _root_.Nat, ∀ x y : _root_.Nat,
    y ∈ V e x ↔ _root_.Part.Dom (φ i (_root_.Nat.pair x y))) →
  _root_.Computable (fun p : _root_.Nat × _root_.Nat × _root_.Nat =>
    (_root_.Equiv.symm _root_.Finset.equivBitIndices) (rowAt p.1 p.2.1 p.2.2)) →
  (∀ e x, _root_.Monotone (rowAt e x)) →
  (∀ e x y, y ∈ V e x ↔ ∃ r : _root_.Nat, y ∈ rowAt e x r) →
  _root_.IsStrictTotalOrder (_root_.Nat × _root_.Nat) pairBefore →
  _root_.ComputablePred (fun p : (_root_.Nat × _root_.Nat) × (_root_.Nat × _root_.Nat) =>
    pairBefore p.1 p.2) →
  let K : _root_.Set _root_.Nat :=
    {n |
      let (e, m) := _root_.Nat.unpair n
      _root_.Part.Dom (φ e m)}
  let relative := _root_.RelativeComputabilityAndEnumerability K
  let bits := _root_.Finset.equivBitIndices
  let upperCandidate (e s : _root_.Nat) (Z : _root_.Finset _root_.Nat)
      (q : _root_.Nat × _root_.Nat) : Prop :=
    let F := rowAt e q.1 q.2
    q.1 ≤ s ∧ q.2 ≤ s ∧
      (∀ m ∈ F, m ≤ s ∧ m ∉ Z) ∧
      ∀ r, q.2 ≤ r → rowAt e q.1 r = F
  let lowerCandidate (e s : _root_.Nat) (content active : _root_.Finset _root_.Nat)
      (m : _root_.Nat) : Prop :=
    m ≤ s ∧ ¬ _root_.Part.Dom (φ e m) ∧ m ∉ content ∧ m ∉ active
  relative.1 (Kᶜ) ∧
  ∃ (upperSearch : _root_.Nat → _root_.Nat → _root_.Finset _root_.Nat →
        _root_.Option (_root_.Nat × _root_.Nat))
    (lowerSearch : _root_.Nat → _root_.Nat → _root_.Finset _root_.Nat →
        _root_.Finset _root_.Nat → _root_.Option _root_.Nat),
    relative.2.2 (fun n =>
      let (e, args) := _root_.Nat.unpair n
      let (s, z) := _root_.Nat.unpair args
      match upperSearch e s (bits z) with
      | _root_.Option.none => 0
      | _root_.Option.some (x, t) => _root_.Nat.succ (_root_.Nat.pair x t)) ∧
    relative.2.2 (fun n =>
      let (e, args) := _root_.Nat.unpair n
      let (s, sets) := _root_.Nat.unpair args
      let (content, active) := _root_.Nat.unpair sets
      match lowerSearch e s (bits content) (bits active) with
      | _root_.Option.none => 0
      | _root_.Option.some m => _root_.Nat.succ m) ∧
    (∀ e s Z,
      match upperSearch e s Z with
      | _root_.Option.none => ∀ q, ¬ upperCandidate e s Z q
      | _root_.Option.some q =>
        upperCandidate e s Z q ∧ ∀ p, upperCandidate e s Z p → ¬ pairBefore p q) ∧
    (∀ e s content active,
      match lowerSearch e s content active with
      | _root_.Option.none => ∀ m, ¬ lowerCandidate e s content active m
      | _root_.Option.some m =>
        lowerCandidate e s content active m ∧
          ∀ n, lowerCandidate e s content active n → m ≤ n) ∧
    let upper (e : _root_.Nat) := 2 * e
    let lower (e : _root_.Nat) := 2 * e + 1
    let markerSet (marker : _root_.Nat → _root_.Option _root_.Nat) (p : _root_.Nat) :=
      _root_.Finset.biUnion (_root_.Finset.range p) (fun j =>
        if lower j < p then
          match marker j with
          | _root_.Option.none => ∅
          | _root_.Option.some m => {m}
        else (∅ : _root_.Finset _root_.Nat))
    let State := _root_.Finset _root_.Nat ×
      (_root_.Nat → _root_.Option _root_.Nat) × (_root_.Nat → _root_.Bool)
    let initial : State := (∅, fun _ => _root_.Option.none, fun _ => _root_.Bool.false)
    let upperAction (s e : _root_.Nat) (state : State) :=
      if state.2.2 e then _root_.Option.none
      else upperSearch e s (markerSet state.2.1 (upper e))
    let visit (s k : _root_.Nat) (state : State) : State :=
      let e := k / 2
      if k % 2 = 0 then
        match upperAction s e state with
        | _root_.Option.none => state
        | _root_.Option.some (x, t) =>
          let F := rowAt e x t
          let remaining (j : _root_.Nat) :=
            match state.2.1 j with
            | _root_.Option.none => _root_.Option.none
            | _root_.Option.some m =>
              if k < lower j ∧ m ∈ F then _root_.Option.none else _root_.Option.some m
          (state.1 ∪ F, remaining, _root_.Function.update state.2.2 e _root_.Bool.true)
      else
        match state.2.1 e with
        | _root_.Option.some _ => state
        | _root_.Option.none =>
          let next := lowerSearch e s state.1 (markerSet state.2.1 s)
          (state.1, _root_.Function.update state.2.1 e next, state.2.2)
    let visits (s : _root_.Nat) (initialState : State) (k : _root_.Nat) : State :=
      _root_.Nat.rec initialState (fun p state => visit s p state) k
    let state (s k : _root_.Nat) : State :=
      let start := _root_.Nat.rec initial (fun r prev => visits r prev r) s
      visits s start (_root_.Nat.min k s)
    let chosenPair (s e : _root_.Nat) :=
      if upper e < s then upperAction s e (state s (upper e)) else _root_.Option.none
    let restraints (s e : _root_.Nat) :=
      markerSet (state s (upper e)).2.1 (upper e)
    let N : _root_.Set _root_.Nat := {m | ∃ s, m ∈ (state s s).1}
    relative.2.2 (fun n =>
      let (s, e) := _root_.Nat.unpair n
      (_root_.Equiv.symm bits) (restraints s e)) ∧
    (∀ s k e m, (state s k).2.1 e = _root_.Option.some m →
      ¬ _root_.Part.Dom (φ e m) ∧ m ∉ (state s k).1 ∧
        ∀ j, (state s k).2.1 j = _root_.Option.some m → j = e) ∧
    (∀ s e q m, chosenPair s e = _root_.Option.some q → m ∈ rowAt e q.1 q.2 → m ≤ s) ∧
    (∀ s m, s < m → m ∉ (state s s).1) ∧
    (∀ s e m, lower e < s →
      (state s (lower e)).2.1 e = _root_.Option.none →
      (state s (lower e + 1)).2.1 e = _root_.Option.some m →
      (∀ r i, s < r → upper i < lower e → chosenPair r i = _root_.Option.none) →
      m ∉ N ∧
        ∀ r i q, lower e < upper i → chosenPair r i = _root_.Option.some q →
          m ∉ rowAt i q.1 q.2) ∧
    ∀ A : _root_.Set _root_.Nat,
      let cyl : _root_.Set _root_.Nat :=
        {z | ∃ x n : _root_.Nat, x ∈ A ∧ z = _root_.Nat.pair x n}
      let encode (n : _root_.Nat) := _root_.List.replicate n _root_.Bool.true
      let decode (w : _root_.List _root_.Bool) : _root_.Option _root_.Nat :=
        if encode (_root_.List.length w) = w then _root_.Option.some (_root_.List.length w)
        else _root_.Option.none
      let ce : _root_.Set _root_.Nat → Prop :=
        _root_.ComputablyEnumerableSet encode decode
          (_root_.List.replicate_left_injective _root_.Bool.true)
          (fun n => by simp [decode, encode])
          (fun w hw => _root_.ite_eq_right (fun h => hw ⟨_root_.List.length w, h⟩))
      ¬ _root_.ComputablePred (fun x : _root_.Nat => x ∈ A) →
      ¬ (_root_.OneOneReducible (fun x : _root_.Nat => x ∈ A) (fun z : _root_.Nat => z ∈ cyl) ∧
         _root_.OneOneReducible (fun z : _root_.Nat => z ∈ cyl) (fun x : _root_.Nat => x ∈ A)) →
      ¬ ce A → ¬ ce (Aᶜ) →
      (∀ e, (∀ x y, y ∈ V e x → (y ∈ A ↔ x ∈ A)) →
        ∀ Z : _root_.Finset _root_.Nat, (∃ S, ∀ s, S ≤ s → restraints s e = Z) →
        (∃ x, _root_.Set.Finite (V e x) ∧ V e x ∩ (Z : _root_.Set _root_.Nat) = ∅) ∧
        (∃ S, ∀ s, S ≤ s →
          ∃ q, upperSearch e s (restraints s e) = _root_.Option.some q) ∧
        (∃ s q, chosenPair s e = _root_.Option.some q)) ∧
      (∀ e, (∀ x y, y ∈ φ e x → x < y ∧ (y ∈ A ↔ x ∈ A)) →
        ∀ b : _root_.Nat, ∃ m : _root_.Nat, b < m ∧ ¬ _root_.Part.Dom (φ e m))
```

Immediate internal dependencies: PriorityRequirements, RelativeComputabilityAndEnumerability, ComputablyEnumerableSet, FixedStageRowStability, OracleNegativePullbackDecision, PriorityBoundedOracleSearches, PriorityCodedVisitTrace, SingletonOracleTapeCompilation, FiniteMarkerAvoidance, CofiniteDomainLemma.

Existing repository dependencies: none.

Immediate external dependencies: PartialCodeSurjectivity, OracleComputableRecursion, AlphabetaHaltingCompleteness, AlphabetaRecognizableEnumerable, UnboundedInfiniteNatSet (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/PriorityConstructionEffectiveness.json), [proof](Proofs/PriorityConstructionEffectiveness.lean), [compilation evidence](evidence/PriorityConstructionEffectiveness-compile.json).

## MaslovaCeDichotomy: Maslova's dichotomy for nonrecursive c.e. many-one degrees

Main result; compiled and axiom-checked.

### Article

We use the following consequence of Maslova's theorem [2], in the formulation recorded by Richter, Stephan, and Zhang [6, p. 17]: every nonrecursive c.e. many-one degree contains either exactly one or infinitely many finite-one degrees.

[§5, p. 13 (unnumbered, consequence of [2] as stated in [6, p. 17]); also §1, p. 1](https://arxiv.org/pdf/2609.00419v1#page=13)

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Translation source: article. The endpoint is the unnumbered consequence of Maslova’s theorem in §5, p. 13 of arXiv:2609.00419v1. The translation represents degrees by their equivalence classes as in §2 and instantiates the computable-enumerability prerequisite with the encoding of each natural number n as n false bits. The article-specific Alphabeta Math Research Portal and designated defect report both returned HTTP 404. No local counterpart or applicable correction could be verified. https://arxiv.org/pdf/2609.00419v1#page=13 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
theorem MaslovaCeDichotomy : let encode (n : _root_.Nat) := _root_.List.replicate n _root_.Bool.false
let decode (w : _root_.List _root_.Bool) :=
  if w = encode (_root_.List.length w) then _root_.Option.some (_root_.List.length w)
  else _root_.Option.none
let ce : _root_.Set _root_.Nat → Prop :=
  _root_.ComputablyEnumerableSet encode decode
    (_root_.List.replicate_left_injective _root_.Bool.false)
    (fun n => by simp [decode, encode])
    (fun w hw => _root_.ite_eq_right (fun h => hw ⟨_root_.List.length w, h.symm⟩))
let finiteOneReducible (X Y : _root_.Set _root_.Nat) : Prop :=
  ∃ f : _root_.Nat → _root_.Nat, _root_.Computable f ∧
    (∀ y : _root_.Nat, _root_.Set.Finite (_root_.Set.preimage f ({y} : _root_.Set _root_.Nat))) ∧
    (∀ x : _root_.Nat, x ∈ X ↔ f x ∈ Y)
let finiteOneDegree (X : _root_.Set _root_.Nat) : _root_.Set (_root_.Set _root_.Nat) :=
  {Y | finiteOneReducible Y X ∧ finiteOneReducible X Y}
∀ A : _root_.Set _root_.Nat,
  let d : _root_.Set (_root_.Set _root_.Nat) :=
    {X | _root_.ManyOneReducibilityOnNat X A ∧ _root_.ManyOneReducibilityOnNat A X}
  (¬ ∃ X ∈ d, _root_.ComputablePred (fun n : _root_.Nat => n ∈ X)) →
  (∃ X ∈ d, ce X) →
  let finiteOneDegrees := _root_.Set.image finiteOneDegree d
  _root_.ExistsUnique (fun D => D ∈ finiteOneDegrees) ∨ _root_.Set.Infinite finiteOneDegrees
```

Immediate internal dependencies: ManyOneReducibilityOnNat, ComputablyEnumerableSet, FiniteMarkerAvoidance, CofiniteDomainLemma, PriorityRequirements, HaltingSigmaOneCompleteness, ProfileRealization, PullbackReductions, HomogeneousRowsFromCylinderReduction, AscendingSelfReductionFromPullbackReduction, CylinderGreatestFiniteOneDegree, ReducibilityImplications.

Existing repository dependencies: none.

Immediate external dependencies: ManyOneDegreeEquality, FiniteSetMaximal, ComputableIffREAndCoRE, FiniteFibresFinitePreimage, PartialComputableSearch, PartialSearchDomAndOutput, NativeRelativeOracleCall, UnboundedInfiniteNatSet, AlphabetaManyOneComposition, AlphabetaRecognizableEnumerable, AlphabetaHaltingCompleteness, AlphabetaPostTheorem (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/MaslovaCeDichotomy.json), [proof](Proofs/MaslovaCeDichotomy.lean), [compilation evidence](evidence/MaslovaCeDichotomy-compile.json).

## NonrecursiveManyOneDegreeDichotomy: Dichotomy for nonrecursive many-one degrees

Main result; compiled and axiom-checked.

### Article

Every nonrecursive many-one degree contains either exactly one or infinitely many finite-one degrees. In particular, there is no nonrecursive many-one degree containing at least two but only finitely many finite-one degrees.

[§5, Corollary 7, p. 13](https://arxiv.org/pdf/2609.00419v1#page=13)

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Translation source: article. Corollary 7 in §5, p. 13 of arXiv:2609.00419v1 states both the dichotomy and its explicit exclusion of finite collections with at least two finite-one degrees. The type represents finite-one degrees by the equivalence classes defined in §2. The article-specific Alphabeta Math Research Portal and designated defect report returned HTTP 404. The local Alphabeta sources contained no matching report or correction for Corollary 7. https://arxiv.org/pdf/2609.00419v1#page=13 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
theorem NonrecursiveManyOneDegreeDichotomy : let finiteOneReducible (X Y : _root_.Set _root_.Nat) : Prop :=
  ∃ f : _root_.Nat → _root_.Nat, _root_.Computable f ∧
    (∀ y : _root_.Nat, _root_.Set.Finite (_root_.Set.preimage f ({y} : _root_.Set _root_.Nat))) ∧
    (∀ x : _root_.Nat, x ∈ X ↔ f x ∈ Y)
let finiteOneDegree (X : _root_.Set _root_.Nat) : _root_.Set (_root_.Set _root_.Nat) :=
  {Y | finiteOneReducible Y X ∧ finiteOneReducible X Y}
∀ d : _root_.ManyOneDegree,
  let representatives : _root_.Set (_root_.Set _root_.Nat) :=
    {X | _root_.ManyOneDegree.of X = d}
  (¬ ∃ X ∈ representatives, _root_.ComputablePred (fun n : _root_.Nat => n ∈ X)) →
  let finiteOneDegrees := _root_.Set.image finiteOneDegree representatives
  (_root_.ExistsUnique (fun D => D ∈ finiteOneDegrees) ∨ _root_.Set.Infinite finiteOneDegrees) ∧
    ¬ (_root_.Set.Finite finiteOneDegrees ∧
      ∃ D ∈ finiteOneDegrees, ∃ E ∈ finiteOneDegrees, D ≠ E)
```

Immediate internal dependencies: CylinderGreatestFiniteOneDegree, ComplementCeDichotomy, MaslovaCeDichotomy, LocalInterpolation, ComputablyEnumerableSet, ReducibilityImplications.

Existing repository dependencies: none.

Immediate external dependencies: FiniteSetMaximal, ManyOneDegreeRepresentative, ManyOneDegreeEquality, RecursivePullsBack (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/NonrecursiveManyOneDegreeDichotomy.json), [proof](Proofs/NonrecursiveManyOneDegreeDichotomy.lean), [compilation evidence](evidence/NonrecursiveManyOneDegreeDichotomy-compile.json).

## ComplementationOrderIsomorphism: Complementation induces an order isomorphism

Main result; compiled and axiom-checked.

### Article

For a many-one degree $\mathbf d$, let

$$\mathcal F(\mathbf d) = \{[X]_{\mathrm{fo}}:X\in\mathbf d\}.$$

Suppose next that $\overline A$ is c.e. Put

$$\mathbf d^{\,c}=[\overline A]_{\mathrm{m}}.$$

Complementation induces an order isomorphism

$$\Phi:\mathcal F(\mathbf d)\longrightarrow \mathcal F(\mathbf d^{\,c})$$

given by

$$\Phi([X]_{\mathrm{fo}})=[\overline X]_{\mathrm{fo}}.$$

Indeed, for every total computable function $f$,

$$f:X\leq_{\mathrm{m}}Y \quad\Longleftrightarrow\quad f:\overline X\leq_{\mathrm{m}}\overline Y,$$

and, since the fibres of $f$ are unchanged,

$$f:X\leq_{\mathrm{fo}}Y \quad\Longleftrightarrow\quad f:\overline X\leq_{\mathrm{fo}}\overline Y.$$

Thus $\Phi$ is well defined and order preserving. The same complementation map, now considered from $\mathcal F(\mathbf d^{\,c})$ to $\mathcal F(\mathbf d)$, is the inverse of $\Phi$. Hence $\Phi$ is an order isomorphism.

[§5, proof of Corollary 7, pp. 13–14 (notation on p. 13, isomorphism on p. 14)](https://arxiv.org/pdf/2609.00419v1#page=14)

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Translation source: article. The endpoint is the complementation order isomorphism in §5, pp. 13–14 of arXiv:2609.00419v1. The type retains the c.e. hypothesis on the complement of A and uses the equivalence classes and induced order of §2. The article-specific Alphabeta Math portal and the designated defect report both returned HTTP 404. No matching local report or correction for this endpoint could be verified. https://arxiv.org/pdf/2609.00419v1#page=14 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419 https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects [Defect report](https://alphabetamath.cc/research-portal/nonrecursive-many-one-degrees-2609-00419/prerequisite-omissions-and-potential-defects).

```lean
theorem ComplementationOrderIsomorphism : ∀ A : _root_.Set _root_.Nat,
  _root_.REPred (fun n : _root_.Nat => n ∈ Aᶜ) →
  let finiteOneReducible (X Y : _root_.Set _root_.Nat) : Prop :=
    ∃ f : _root_.Nat → _root_.Nat, _root_.Computable f ∧
      (∀ y : _root_.Nat, _root_.Set.Finite (_root_.Set.preimage f ({y} : _root_.Set _root_.Nat))) ∧
      (∀ x : _root_.Nat, x ∈ X ↔ f x ∈ Y)
  let finiteOneDegree (X : _root_.Set _root_.Nat) : _root_.Set (_root_.Set _root_.Nat) :=
    {Y | finiteOneReducible Y X ∧ finiteOneReducible X Y}
  let F (d : _root_.ManyOneDegree) : _root_.Set (_root_.Set (_root_.Set _root_.Nat)) :=
    _root_.Set.image finiteOneDegree {X | _root_.ManyOneDegree.of X = d}
  let degreeOrder (d : _root_.ManyOneDegree) : _root_.LE (F d) :=
    ⟨fun D E => ∃ X ∈ D.val, ∃ Y ∈ E.val, finiteOneReducible X Y⟩
  let d := _root_.ManyOneDegree.of A
  let dc := _root_.ManyOneDegree.of Aᶜ
  ∃ Φ : @_root_.OrderIso (F d) (F dc) (degreeOrder d) (degreeOrder dc),
    ∀ (X : _root_.Set _root_.Nat) (hX : _root_.ManyOneDegree.of X = d),
      (Φ ⟨finiteOneDegree X, ⟨X, hX, rfl⟩⟩).val =
        finiteOneDegree Xᶜ
```

Immediate internal dependencies: ReducibilityImplications.

Existing repository dependencies: none.

Immediate external dependencies: ManyOneDegreeEquality, PreorderQuotientOrder (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [reviewed translation](translations/ComplementationOrderIsomorphism.json), [proof](Proofs/ComplementationOrderIsomorphism.lean), [compilation evidence](evidence/ComplementationOrderIsomorphism-compile.json).

## OracleNegativePullbackDecision: One-query oracle tape decision for nonmembership after a total computable map

Prerequisite; compiled and axiom-checked.

### Article

No original article statement.

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Authored in Step 4 for use in the proof.

```lean
theorem OracleNegativePullbackDecision : ∀ (X : Set Nat) (f : Nat → Nat), Computable f →
  (RelativeComputabilityAndEnumerability X).1 {n | f n ∉ X}
```

Immediate internal dependencies: RelativeComputabilityAndEnumerability.

Existing repository dependencies: none.

Immediate external dependencies: OneSidedWordMachineRealization, LiteralWordRawMachine, LiteralWordSafeTape, LiteralWordFoldWrapper, MathlibPartrecTM2Evaluation (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [proof](Proofs/OracleNegativePullbackDecision.lean), [compilation evidence](evidence/OracleNegativePullbackDecision-compile.json).

## PriorityBoundedOracleSearches: Verified singleton-oracle bounded least searches for priority rows and admissible lower markers

Prerequisite; compiled and axiom-checked.

### Article

No original article statement.

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Authored in Step 4 for use in the proof.

```lean
theorem PriorityBoundedOracleSearches : ∀ (φ : Nat → Nat → Part Nat)
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
```

Immediate internal dependencies: none.

Existing repository dependencies: none.

Immediate external dependencies: NativeRelativeBoundedRecursion, PrimitiveRecursiveListBoundedUniversalTest, BinaryFiniteSetMembershipAndBound, PairCodeExactStageSquare (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [proof](Proofs/PriorityBoundedOracleSearches.lean), [compilation evidence](evidence/PriorityBoundedOracleSearches-compile.json).

## PriorityCodedVisitTrace: Exact bounded stage and visit trace for a decidable admissible marker set and computable pair order, with relative content and restraint codes and trace invariants

Prerequisite; compiled and axiom-checked.

### Article

No original article statement.

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Authored in Step 4 for use in the proof.

```lean
theorem PriorityCodedVisitTrace : ∀ (φ : Nat → Nat → Part Nat)
    (row : PriorityCodedTrace.Rows)
    (pairBefore : (Nat × Nat) → (Nat × Nat) → Prop)
    (query : Nat → Nat) (M : Set Nat),
  let K : Set Nat := {n | (φ n.unpair.1 n.unpair.2).Dom}
  let oracle : Set (Nat →. Nat) :=
    {(by classical exact fun n => Part.some (if n ∈ K then 1 else 0))}
  Computable (fun p : Nat × Nat × Nat => Finset.equivBitIndices.symm (row p.1 p.2.1 p.2.2)) →
  IsStrictTotalOrder (Nat × Nat) pairBefore →
  ComputablePred (fun p : (Nat × Nat) × (Nat × Nat) => pairBefore p.1 p.2) →
  Computable query →
  (∀ e x t, query (Nat.pair e (Nat.pair x t)) ∉ K ↔
    ∀ r, t ≤ r → row e x r = row e x t) →
  Nat.RecursiveIn oracle (by classical exact fun m => Part.some (if m ∈ M then 1 else 0)) →
  ∃ (U : PriorityCodedTrace.UpperSearch) (L : PriorityCodedTrace.LowerSearch),
    Nat.RecursiveIn oracle (fun n => Part.some (PriorityCodedTrace.upperCode U n)) ∧
    Nat.RecursiveIn oracle (fun n => Part.some (PriorityCodedTrace.lowerCode L n)) ∧
    PriorityCodedTrace.UpperCorrect row pairBefore U ∧
    PriorityCodedTrace.LowerCorrect φ M L ∧
    Nat.RecursiveIn oracle (fun n => Part.some (PriorityCodedTrace.traceCode row U L n)) ∧
    Nat.RecursiveIn oracle (fun s => Part.some
      (Finset.equivBitIndices.symm (PriorityCodedTrace.content row U L s s))) ∧
    Nat.RecursiveIn oracle (fun n => Part.some
      (Finset.equivBitIndices.symm (PriorityCodedTrace.restraints row U L n.unpair.1 n.unpair.2))) ∧
    PriorityCodedTrace.Laws φ row M U L
```

Immediate internal dependencies: PriorityBoundedOracleSearches.

Existing repository dependencies: none.

Immediate external dependencies: NativeRelativeBoundedRecursion, PriorityFiniteSetBitCodes, PriorityFiniteSetBitMembership (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [proof](Proofs/PriorityCodedVisitTrace.lean), [compilation evidence](evidence/PriorityCodedVisitTrace-compile.json).

## SingletonOracleTapeCompilation: Compile singleton characteristic oracle recursion to canonical binary oracle tapes, preserving partial acceptance and total numeric output

Prerequisite; compiled and axiom-checked.

### Article

No original article statement.

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Authored in Step 4 for use in the proof.

```lean
theorem SingletonOracleTapeCompilation : ∀ X : Set Nat,
  let O : Set (Nat →. Nat) :=
    {fun n => Part.some (@ite Nat (n ∈ X) (Classical.propDecidable _) 1 0)}
  (∀ f : Nat →. Nat, Nat.RecursiveIn O f →
    (RelativeComputabilityAndEnumerability X).2.1 {n | (f n).Dom}) ∧
  (∀ f : Nat → Nat, Nat.RecursiveIn O (fun n => Part.some (f n)) →
    (RelativeComputabilityAndEnumerability X).2.2 f)
```

Immediate internal dependencies: OracleNegativePullbackDecision, RelativeComputabilityAndEnumerability.

Existing repository dependencies: none.

Immediate external dependencies: LiteralWordSafeTape, LiteralWordFoldWrapper, MathlibFinitePrefixEvaluation, MathlibPartialMinimizationMembership (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [proof](Proofs/SingletonOracleTapeCompilation.lean), [compilation evidence](evidence/SingletonOracleTapeCompilation-compile.json).

## CETapeOracleSigmaTwo: A set accepted by a binary oracle tape with a c.e. oracle has a primitive-recursive Sigma-two presentation

Prerequisite; compiled and axiom-checked.

### Article

No original article statement.

### Alphabeta Math

No Alphabeta Math source recorded.

### Lean statement

Authored in Step 4 for use in the proof.

```lean
theorem CETapeOracleSigmaTwo : ∀ (X N : Set Nat), REPred (fun q : Nat => q ∈ X) →
  (RelativeComputabilityAndEnumerability X).2.1 N →
  {xs : Fin 1 → Nat | xs 0 ∈ N} ∈
    (ArithmeticalHierarchyLevels 2 1 (Nat.le_succ 1)).1
```

Immediate internal dependencies: OracleNegativePullbackDecision, RelativeComputabilityAndEnumerability, ArithmeticalHierarchyLevels, ComputablyEnumerableSet.

Existing repository dependencies: none.

Immediate external dependencies: PrimitiveRecursiveBoundedCodeEvaluation, BoundedCodeEvaluationCompleteness, BoundedCodeEvaluationSoundness, PrimitiveRecursiveFiniteDomain, PrimitiveRecursiveListTakeWhile, PrimitiveRecursiveListFoldLeft, PrimitiveRecursiveListFoldRight (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [proof](Proofs/CETapeOracleSigmaTwo.lean), [compilation evidence](evidence/CETapeOracleSigmaTwo-compile.json).
