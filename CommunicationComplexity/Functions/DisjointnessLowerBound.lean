import CommunicationComplexity.Functions.Disjointness
import CommunicationComplexity.Deterministic.Transcript
import CommunicationComplexity.InformationTheory.Entropy
import CommunicationComplexity.InformationTheory.Pinsker
import CommunicationComplexity.InformationTheory.TVDistance
import CommunicationComplexity.PublicCoin.Minimax
import Mathlib.Probability.UniformOn
import PFR.Kullback

namespace CommunicationComplexity

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Functions.Disjointness

/-!
This file restarts the randomized lower bound for disjointness following the corrected proof in
`.codex/disjointness.txt`.

The proof uses the textbook hard distribution: choose a special coordinate `T`; at `T`, sample
independent bits `(X_T, Y_T)`; away from `T`, sample one of `(0,0)`, `(1,0)`, `(0,1)` uniformly
and independently.  The information terms below are the corrected ones from (6.6):

* Alice: `I(X_T : M | T, X_<T, Y_≥T, D)`.
* Bob: `I(Y_T : M | T, X_≤T, Y_>T, D)`.

The old file used the wrong `Y_≠T` / `X_≠T` conditioning terms, which came from the typoed
transcription and led to a different proof.
-/

namespace RandomizedLowerBound

variable (n : ℕ+)

noncomputable instance setFinFiniteMeasureSpace :
    FiniteMeasureSpace (Set (Fin n)) :=
  FiniteMeasureSpace.of (Set (Fin n))

/-- The three possible disjoint coordinate-pairs used away from the special coordinate. -/
inductive DisjointCoordinate
  | neither
  | leftOnly
  | rightOnly
  deriving DecidableEq, Fintype

instance disjointCoordinateNonempty : Nonempty DisjointCoordinate :=
  ⟨DisjointCoordinate.neither⟩

instance disjointCoordinateMeasurableSpace : MeasurableSpace DisjointCoordinate := ⊤

instance disjointCoordinateDiscreteMeasurableSpace :
    DiscreteMeasurableSpace DisjointCoordinate := by
  infer_instance

instance disjointCoordinateFiniteMeasureSpace : FiniteMeasureSpace DisjointCoordinate :=
  FiniteMeasureSpace.of DisjointCoordinate

namespace DisjointCoordinate

/-- Alice's bit in a disjoint coordinate-pair. -/
def xBit : DisjointCoordinate → Bool
  | neither => false
  | leftOnly => true
  | rightOnly => false

/-- Bob's bit in a disjoint coordinate-pair. -/
def yBit : DisjointCoordinate → Bool
  | neither => false
  | leftOnly => false
  | rightOnly => true

/-- There are three disjoint coordinate-pairs. -/
theorem card :
    Fintype.card DisjointCoordinate = 3 := by
  decide

/-- A disjoint coordinate-pair never has both bits equal to `true`. -/
theorem not_xBit_and_yBit (c : DisjointCoordinate) :
    ¬(xBit c = true ∧ yBit c = true) := by
  cases c <;> simp [xBit, yBit]

/-- Swap Alice's and Bob's sides in a disjoint coordinate. -/
def swap : DisjointCoordinate → DisjointCoordinate
  | neither => neither
  | leftOnly => rightOnly
  | rightOnly => leftOnly

/-- Swapping sides twice recovers the original disjoint coordinate. -/
theorem swap_swap (c : DisjointCoordinate) :
    swap (swap c) = c := by
  cases c <;> rfl

/-- After swapping a disjoint coordinate, Alice sees Bob's original bit. -/
theorem xBit_swap (c : DisjointCoordinate) :
    xBit (swap c) = yBit c := by
  cases c <;> rfl

/-- After swapping a disjoint coordinate, Bob sees Alice's original bit. -/
theorem yBit_swap (c : DisjointCoordinate) :
    yBit (swap c) = xBit c := by
  cases c <;> rfl

end DisjointCoordinate

/-- The sample space for the hard distribution.  The `other` coordinate at `T` is ignored; keeping
it in the sample space makes the ambient type a simple product-like finite type. -/
structure HardSample where
  T : Fin n
  xT : Bool
  yT : Bool
  other : Fin n → DisjointCoordinate
  deriving DecidableEq, Fintype

namespace HardSample

instance : Nonempty (HardSample n) :=
  ⟨{ T := ⟨0, n.pos⟩
     xT := false
     yT := false
     other := fun _ => DisjointCoordinate.neither }⟩

instance : MeasurableSpace (HardSample n) := ⊤

/-- We use the uniform distribution on the explicit hard-distribution sample space. -/
noncomputable instance measureSpace : MeasureSpace (HardSample n) :=
  ⟨ProbabilityTheory.uniformOn Set.univ⟩

noncomputable instance isProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure (HardSample n)) := by
  change IsProbabilityMeasure (ProbabilityTheory.uniformOn Set.univ)
  infer_instance

noncomputable instance finiteProbabilitySpace : FiniteProbabilitySpace (HardSample n) :=
  FiniteProbabilitySpace.of (HardSample n)

private def equivProd :
    HardSample n ≃ Fin n × Bool × Bool × (Fin n → DisjointCoordinate) where
  toFun ω := (ω.T, ω.xT, ω.yT, ω.other)
  invFun p :=
    { T := p.1
      xT := p.2.1
      yT := p.2.2.1
      other := p.2.2.2 }
  left_inv ω := by
    rcases ω with ⟨T, xT, yT, other⟩
    rfl
  right_inv p := by
    rcases p with ⟨T, xT, yT, other⟩
    rfl

/-- Cardinality of the explicit hard-distribution sample space. -/
theorem card :
    Fintype.card (HardSample n) = (n : ℕ) * 4 * 3 ^ (n : ℕ) := by
  calc
    Fintype.card (HardSample n) =
        Fintype.card (Fin n × Bool × Bool × (Fin n → DisjointCoordinate)) :=
      Fintype.card_congr (equivProd n)
    _ = (n : ℕ) * 4 * 3 ^ (n : ℕ) := by
      simp [Fintype.card_prod, Fintype.card_pi, DisjointCoordinate.card]
      ring

end HardSample

/-- Alice's bit at coordinate `i` under a hard-distribution sample. -/
def xBit (ω : HardSample n) (i : Fin n) : Bool :=
  if i = ω.T then ω.xT else (ω.other i).xBit

/-- Bob's bit at coordinate `i` under a hard-distribution sample. -/
def yBit (ω : HardSample n) (i : Fin n) : Bool :=
  if i = ω.T then ω.yT else (ω.other i).yBit

/-- Alice's input set under a hard-distribution sample. -/
def X (ω : HardSample n) : Set (Fin n) :=
  {i | xBit n ω i = true}

/-- Bob's input set under a hard-distribution sample. -/
def Y (ω : HardSample n) : Set (Fin n) :=
  {i | yBit n ω i = true}

/-- Alice's full input vector under a hard-distribution sample. -/
def xVector (ω : HardSample n) : Fin n → Bool :=
  xBit n ω

/-- Bob's full input vector under a hard-distribution sample. -/
def yVector (ω : HardSample n) : Fin n → Bool :=
  yBit n ω

/-- Reverse the coordinate order of a boolean vector. -/
def reverseBoolVector (v : Fin n → Bool) : Fin n → Bool :=
  v ∘ Fin.rev

/-- Reversing a boolean vector twice recovers it. -/
theorem reverseBoolVector_reverseBoolVector (v : Fin n → Bool) :
    reverseBoolVector n (reverseBoolVector n v) = v := by
  funext i
  simp [reverseBoolVector]

/-- Reversing boolean vectors is injective. -/
theorem reverseBoolVector_injective :
    Function.Injective (reverseBoolVector n) := by
  intro v w h
  have h' := congrArg (reverseBoolVector n) h
  simpa [reverseBoolVector_reverseBoolVector] using h'

/-- Reverse the coordinate order of a subset of coordinates. -/
def reverseSet (S : Set (Fin n)) : Set (Fin n) :=
  {i | Fin.rev i ∈ S}

/-- Reversing a coordinate set twice recovers it. -/
theorem reverseSet_reverseSet (S : Set (Fin n)) :
    reverseSet n (reverseSet n S) = S := by
  ext i
  simp [reverseSet]

/-- The input pair generated by a hard-distribution sample. -/
def input (ω : HardSample n) : Set (Fin n) × Set (Fin n) :=
  (X n ω, Y n ω)

/-- The event that the special coordinate is an actual intersection. -/
def specialIntersect : Set (HardSample n) :=
  {ω | ω.xT = true ∧ ω.yT = true}

/-- The event that the two special-coordinate bits have prescribed values. -/
def specialBitsEvent (bx bY : Bool) : Set (HardSample n) :=
  {ω | ω.xT = bx ∧ ω.yT = bY}

/-- The event that the special coordinate has a prescribed value. -/
def specialCoordinateEvent (i : Fin n) : Set (HardSample n) :=
  {ω | ω.T = i}

/-- The event that both special-coordinate bits are zero. -/
def specialZeroZero : Set (HardSample n) :=
  specialBitsEvent n false false

/-- The event that the generated input pair is disjoint. -/
def disjointEvent : Set (HardSample n) :=
  {ω | Disjoint (X n ω) (Y n ω)}

noncomputable instance specialIntersectFintype :
    Fintype {ω : HardSample n // ω ∈ specialIntersect n} := by
  unfold specialIntersect
  infer_instance

noncomputable instance specialBitsEventFintype (bx bY : Bool) :
    Fintype {ω : HardSample n // ω ∈ specialBitsEvent n bx bY} := by
  unfold specialBitsEvent
  infer_instance

noncomputable instance specialCoordinateEventFintype (i : Fin n) :
    Fintype {ω : HardSample n // ω ∈ specialCoordinateEvent n i} := by
  unfold specialCoordinateEvent
  infer_instance

/-- The special coordinate selected by the hard distribution. -/
def specialCoordinate (ω : HardSample n) : Fin n :=
  ω.T

/-- Alice's bit at the special coordinate. -/
def specialX (ω : HardSample n) : Bool :=
  ω.xT

/-- Bob's bit at the special coordinate. -/
def specialY (ω : HardSample n) : Bool :=
  ω.yT

/-- Alice's input bits before the special coordinate, padded by `false` elsewhere. -/
def xBeforeSpecial (ω : HardSample n) : Fin n → Bool :=
  fun i => if i < ω.T then xBit n ω i else false

/-- Alice's input bits up to and including the special coordinate, padded by `false` elsewhere. -/
def xLeSpecial (ω : HardSample n) : Fin n → Bool :=
  fun i => if i ≤ ω.T then xBit n ω i else false

/-- Bob's input bits after the special coordinate, padded by `false` elsewhere. -/
def yAfterSpecial (ω : HardSample n) : Fin n → Bool :=
  fun i => if ω.T < i then yBit n ω i else false

/-- Bob's input bits from the special coordinate onward, padded by `false` elsewhere. -/
def yGeSpecial (ω : HardSample n) : Fin n → Bool :=
  fun i => if ω.T ≤ i then yBit n ω i else false

/-- The common coarse variable `T, X_<T, Y_>T` used in Claim 6.21. -/
def coarseConditioning (ω : HardSample n) :
    Fin n × (Fin n → Bool) × (Fin n → Bool) :=
  (specialCoordinate n ω, xBeforeSpecial n ω, yAfterSpecial n ω)

/-- The corrected Alice conditioning variable from (6.6): `T, X_<T, Y_≥T`. -/
def aliceClaimConditioning (ω : HardSample n) :
    Fin n × (Fin n → Bool) × (Fin n → Bool) :=
  (specialCoordinate n ω, xBeforeSpecial n ω, yGeSpecial n ω)

/-- The corrected Bob conditioning variable from (6.6): `T, X_≤T, Y_>T`. -/
def bobClaimConditioning (ω : HardSample n) :
    Fin n × (Fin n → Bool) × (Fin n → Bool) :=
  (specialCoordinate n ω, xLeSpecial n ω, yAfterSpecial n ω)

/-- Alice's fixed-coordinate bit used in Lemma 6.20. -/
def fixedXBit (i : Fin n) (ω : HardSample n) : Bool :=
  xBit n ω i

/-- Alice's fixed-coordinate `X_<i` prefix used in Lemma 6.20. -/
def fixedXBefore (i : Fin n) (ω : HardSample n) : Fin n → Bool :=
  fun j => if j < i then xBit n ω j else false

/-- Bob's fixed-coordinate `Y_<i` prefix used in Lemma 6.20. -/
def fixedYBefore (i : Fin n) (ω : HardSample n) : Fin n → Bool :=
  fun j => if j < i then yBit n ω j else false

/-- Bob's fixed-coordinate `Y_≥i` suffix used in Lemma 6.20. -/
def fixedYGe (i : Fin n) (ω : HardSample n) : Fin n → Bool :=
  fun j => if i ≤ j then yBit n ω j else false

/-- The fixed-coordinate Alice conditioning variable `X_<i, Y_≥i` from Lemma 6.20. -/
def fixedAliceConditioning (i : Fin n) (ω : HardSample n) :
    (Fin n → Bool) × (Fin n → Bool) :=
  (fixedXBefore n i ω, fixedYGe n i ω)

/-- The values of Alice's corrected conditioning variable for which `Y_T = false`. -/
def aliceClaimConditioningYFalseValues :
    Set (Fin n × (Fin n → Bool) × (Fin n → Bool)) :=
  {c | c.2.2 c.1 = false}

/-- The `Y_≥T` component of Alice's corrected conditioning contains the bit `Y_T`. -/
theorem yGeSpecial_specialCoordinate (ω : HardSample n) :
    yGeSpecial n ω (specialCoordinate n ω) = specialY n ω := by
  simp [yGeSpecial, specialCoordinate, specialY, yBit]

/-- The event `Y_T=false` is determined by Alice's corrected conditioning variable. -/
theorem specialY_false_eq_preimage_aliceClaimConditioningYFalseValues :
    (((specialY n) ⁻¹' {false}) : Set (HardSample n)) =
      (aliceClaimConditioning n) ⁻¹' aliceClaimConditioningYFalseValues n := by
  ext ω
  simp [aliceClaimConditioningYFalseValues, aliceClaimConditioning,
    yGeSpecial_specialCoordinate]

/-- The conditioning-value recoding induced by reversing coordinates and swapping Alice/Bob. -/
def dualConditioningValue
    (c : Fin n × (Fin n → Bool) × (Fin n → Bool)) :
    Fin n × (Fin n → Bool) × (Fin n → Bool) :=
  (Fin.rev c.1, reverseBoolVector n c.2.2, reverseBoolVector n c.2.1)

/-- Recoding a conditioning value twice recovers the original value. -/
theorem dualConditioningValue_dualConditioningValue
    (c : Fin n × (Fin n → Bool) × (Fin n → Bool)) :
    dualConditioningValue n (dualConditioningValue n c) = c := by
  rcases c with ⟨i, x, y⟩
  simp [dualConditioningValue, reverseBoolVector_reverseBoolVector]

/-- The conditioning-value duality map is injective. -/
theorem dualConditioningValue_injective :
    Function.Injective (dualConditioningValue n) := by
  intro c c' h
  have h' := congrArg (dualConditioningValue n) h
  simpa [dualConditioningValue_dualConditioningValue] using h'

/-- The `Z = (M, T, X_<T, Y_>T)` variable used in Claim 6.21. -/
noncomputable def zVariable
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (ω : HardSample n) :
    p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)) :=
  (p.transcript (input n ω), coarseConditioning n ω)

/-- The hard input distribution, as a probability measure on input pairs. -/
noncomputable def inputProbabilityMeasure :
    ProbabilityMeasure (Set (Fin n) × Set (Fin n)) :=
  ProbabilityMeasure.map
    (⟨(volume : Measure (HardSample n)), inferInstance⟩ :
      ProbabilityMeasure (HardSample n))
    (Measurable.of_discrete.aemeasurable (f := input n))

/-- The hard input distribution packaged as a finite probability space for distributional error. -/
noncomputable def inputDist :
    FiniteProbabilitySpace (Set (Fin n) × Set (Fin n)) :=
  FiniteProbabilitySpace.ofProbabilityMeasure
    (Set (Fin n) × Set (Fin n)) (inputProbabilityMeasure n)

/-- The protocol dual swaps Alice/Bob and reverses both coordinate sets. -/
def dualProtocol
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool :=
  p.swap.comap (reverseSet n) (reverseSet n)

/-- Dualizing a protocol preserves its communication complexity. -/
theorem dualProtocol_complexity
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    (dualProtocol n p).complexity = p.complexity := by
  simp [dualProtocol]

/-- The leaf-level map induced by protocol duality. -/
noncomputable def dualProtocolLeafMap
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    p.Leaf → (dualProtocol n p).Leaf :=
  fun leaf =>
    Deterministic.Protocol.leafComap p.swap (reverseSet n) (reverseSet n)
      (Deterministic.Protocol.leafSwap p leaf)

/-- The leaf-level map induced by protocol duality is injective. -/
theorem dualProtocolLeafMap_injective
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    Function.Injective (dualProtocolLeafMap n p) := by
  intro R S h
  apply (Deterministic.Protocol.leafSwap p).injective
  apply Subtype.ext
  have hset := congrArg Subtype.val h
  ext yx
  have hmem := congrArg
    (fun A : Set (Set (Fin n) × Set (Fin n)) =>
      (reverseSet n yx.1, reverseSet n yx.2) ∈ A) hset
  simpa [dualProtocolLeafMap, Deterministic.Protocol.leafComap,
    Deterministic.Protocol.preimageInputSet, reverseSet_reverseSet] using hmem

theorem mem_X (ω : HardSample n) (i : Fin n) :
    i ∈ X n ω ↔ xBit n ω i = true :=
  Iff.rfl

theorem mem_Y (ω : HardSample n) (i : Fin n) :
    i ∈ Y n ω ↔ yBit n ω i = true :=
  Iff.rfl

theorem xBit_special (ω : HardSample n) :
    xBit n ω ω.T = ω.xT := by
  simp [xBit]

theorem yBit_special (ω : HardSample n) :
    yBit n ω ω.T = ω.yT := by
  simp [yBit]

theorem xBit_of_ne_special (ω : HardSample n) {i : Fin n} (hi : i ≠ ω.T) :
    xBit n ω i = (ω.other i).xBit := by
  simp [xBit, hi]

theorem yBit_of_ne_special (ω : HardSample n) {i : Fin n} (hi : i ≠ ω.T) :
    yBit n ω i = (ω.other i).yBit := by
  simp [yBit, hi]

/-- Away from `T`, generated coordinate-pairs are disjoint. -/
theorem not_xBit_and_yBit_of_ne_special
    (ω : HardSample n) {i : Fin n} (hi : i ≠ ω.T) :
    ¬(xBit n ω i = true ∧ yBit n ω i = true) := by
  rw [xBit_of_ne_special n ω hi, yBit_of_ne_special n ω hi]
  exact DisjointCoordinate.not_xBit_and_yBit (ω.other i)

/-- The disjoint coordinate with the given bits. On the invalid `(true, true)` input this chooses
an arbitrary disjoint coordinate; the projection lemmas below assume that invalid case away. -/
def coordinateOfBits (x y : Bool) : DisjointCoordinate :=
  if x = true then DisjointCoordinate.leftOnly
  else if y = true then DisjointCoordinate.rightOnly
  else DisjointCoordinate.neither

/-- `coordinateOfBits` preserves Alice's bit when the requested pair is disjoint. -/
theorem coordinateOfBits_xBit {x y : Bool} (h : ¬(x = true ∧ y = true)) :
    (coordinateOfBits x y).xBit = x := by
  cases x <;> cases y <;> simp [coordinateOfBits, DisjointCoordinate.xBit] at h ⊢

/-- `coordinateOfBits` preserves Bob's bit when the requested pair is disjoint. -/
theorem coordinateOfBits_yBit {x y : Bool} (h : ¬(x = true ∧ y = true)) :
    (coordinateOfBits x y).yBit = y := by
  cases x <;> cases y <;> simp [coordinateOfBits, DisjointCoordinate.yBit] at h ⊢

/-- `coordinateOfBits` reconstructs an existing disjoint coordinate from its two projections. -/
theorem coordinateOfBits_xBit_yBit (c : DisjointCoordinate) :
    coordinateOfBits c.xBit c.yBit = c := by
  cases c <;> simp [coordinateOfBits, DisjointCoordinate.xBit, DisjointCoordinate.yBit]

/-- Mix Alice's input from `ωX` with Bob's input from `ωY`. This is only intended to be used
when the two samples agree on `T`, `X_<T`, and `Y_>T`; under those hypotheses the mixed
coordinate requests are always disjoint. -/
def mix (ωX ωY : HardSample n) : HardSample n where
  T := ωX.T
  xT := ωX.xT
  yT := ωY.yT
  other := fun i =>
    if i = ωX.T then ωX.other i
    else coordinateOfBits (xBit n ωX i) (yBit n ωY i)

/-- Mixing a sample with itself recovers the original sample. -/
theorem mix_self (ω : HardSample n) :
    mix n ω ω = ω := by
  rcases ω with ⟨T, xT, yT, other⟩
  simp only [mix, xBit, yBit]
  congr
  funext i
  by_cases hi : i = T
  · simp [hi]
  · simp [hi, coordinateOfBits_xBit_yBit]

/-- The generated sets are disjoint exactly when the two special-coordinate bits are not both
`true`. -/
theorem disjoint_X_Y_iff (ω : HardSample n) :
    Disjoint (X n ω) (Y n ω) ↔ ¬(ω.xT = true ∧ ω.yT = true) := by
  rw [Set.disjoint_left]
  constructor
  · intro h hbits
    exact h (a := ω.T) (by simpa [X, xBit] using hbits.1) (by simpa [Y, yBit] using hbits.2)
  · intro h i hiX hiY
    by_cases hi : i = ω.T
    · subst hi
      exact h ⟨by simpa [X, xBit] using hiX, by simpa [Y, yBit] using hiY⟩
    · exact not_xBit_and_yBit_of_ne_special n ω hi ⟨hiX, hiY⟩

/-- Dualize the hard sample space by swapping Alice/Bob and reversing coordinate order. -/
def dualHardSample (ω : HardSample n) : HardSample n where
  T := Fin.rev ω.T
  xT := ω.yT
  yT := ω.xT
  other := fun i => DisjointCoordinate.swap (ω.other (Fin.rev i))

/-- Dualizing a hard sample twice recovers the original sample. -/
theorem dualHardSample_dualHardSample (ω : HardSample n) :
    dualHardSample n (dualHardSample n ω) = ω := by
  rcases ω with ⟨T, xT, yT, other⟩
  simp [dualHardSample, DisjointCoordinate.swap_swap]

/-- Alice's bit in the dual hard sample is Bob's original bit at the reversed coordinate. -/
theorem xBit_dualHardSample (ω : HardSample n) (i : Fin n) :
    xBit n (dualHardSample n ω) i = yBit n ω (Fin.rev i) := by
  by_cases hi : i = Fin.rev ω.T
  · subst i
    simp [dualHardSample, xBit, yBit]
  · have hrev : Fin.rev i ≠ ω.T := by
      intro h
      apply hi
      have h' := congrArg Fin.rev h
      simpa using h'
    simp [dualHardSample, xBit, yBit, hi, hrev, DisjointCoordinate.xBit_swap]

/-- Bob's bit in the dual hard sample is Alice's original bit at the reversed coordinate. -/
theorem yBit_dualHardSample (ω : HardSample n) (i : Fin n) :
    yBit n (dualHardSample n ω) i = xBit n ω (Fin.rev i) := by
  have h := xBit_dualHardSample n (dualHardSample n ω) (Fin.rev i)
  simpa [dualHardSample_dualHardSample] using h.symm

/-- Dual hard samples swap Alice's input with Bob's input and reverse coordinates. -/
theorem X_dualHardSample (ω : HardSample n) :
    X n (dualHardSample n ω) = reverseSet n (Y n ω) := by
  ext i
  simp [X, Y, reverseSet, xBit_dualHardSample]

/-- Dual hard samples swap Bob's input with Alice's input and reverse coordinates. -/
theorem Y_dualHardSample (ω : HardSample n) :
    Y n (dualHardSample n ω) = reverseSet n (X n ω) := by
  have h := X_dualHardSample n (dualHardSample n ω)
  have hdual := congrArg (reverseSet n) h
  simpa [dualHardSample_dualHardSample, reverseSet_reverseSet] using hdual.symm

/-- The generated input of a dual hard sample is the reversed, swapped original input. -/
theorem input_dualHardSample (ω : HardSample n) :
    input n (dualHardSample n ω) = (reverseSet n (Y n ω), reverseSet n (X n ω)) := by
  rw [input, X_dualHardSample, Y_dualHardSample]

/-- Hard-sample duality preserves the disjoint-input event. -/
theorem disjointEvent_dualHardSample (ω : HardSample n) :
    dualHardSample n ω ∈ disjointEvent n ↔ ω ∈ disjointEvent n := by
  change Disjoint (X n (dualHardSample n ω)) (Y n (dualHardSample n ω)) ↔
    Disjoint (X n ω) (Y n ω)
  rw [disjoint_X_Y_iff, disjoint_X_Y_iff]
  simp [dualHardSample, and_comm]

/-- Alice's special bit in the dual hard sample is Bob's original special bit. -/
theorem specialX_dualHardSample (ω : HardSample n) :
    specialX n (dualHardSample n ω) = specialY n ω := by
  simp [specialX, specialY, dualHardSample]

/-- Bob's special bit in the dual hard sample is Alice's original special bit. -/
theorem specialY_dualHardSample (ω : HardSample n) :
    specialY n (dualHardSample n ω) = specialX n ω := by
  simp [specialX, specialY, dualHardSample]

/-- The `X_T=Y_T=false` slice is invariant under hard-sample duality. -/
theorem specialZeroZero_dualHardSample (ω : HardSample n) :
    dualHardSample n ω ∈ specialZeroZero n ↔ ω ∈ specialZeroZero n := by
  simp [specialZeroZero, specialBitsEvent, dualHardSample, and_comm]

/-- Alice's full input vector in the dual is Bob's original full vector in reverse order. -/
theorem xVector_dualHardSample (ω : HardSample n) :
    xVector n (dualHardSample n ω) = reverseBoolVector n (yVector n ω) := by
  funext i
  simp [xVector, yVector, reverseBoolVector, xBit_dualHardSample]

/-- Bob's full input vector in the dual is Alice's original full vector in reverse order. -/
theorem yVector_dualHardSample (ω : HardSample n) :
    yVector n (dualHardSample n ω) = reverseBoolVector n (xVector n ω) := by
  funext i
  simp [xVector, yVector, reverseBoolVector, yBit_dualHardSample]

/-- Alice's before-special vector in the dual is Bob's after-special vector in reverse order. -/
theorem xBeforeSpecial_dualHardSample (ω : HardSample n) :
    xBeforeSpecial n (dualHardSample n ω) =
      reverseBoolVector n (yAfterSpecial n ω) := by
  funext i
  change
    (if i < Fin.rev ω.T then xBit n (dualHardSample n ω) i else false) =
      (if ω.T < Fin.rev i then yBit n ω (Fin.rev i) else false)
  rw [xBit_dualHardSample]
  by_cases h : i < Fin.rev ω.T
  · have h' : ω.T < Fin.rev i := (Fin.lt_rev_iff).1 h
    simp [h, h']
  · have h' : ¬ω.T < Fin.rev i := by
      intro h'
      exact h ((Fin.lt_rev_iff).2 h')
    simp [h, h']

/-- Bob's after-special vector in the dual is Alice's before-special vector in reverse order. -/
theorem yAfterSpecial_dualHardSample (ω : HardSample n) :
    yAfterSpecial n (dualHardSample n ω) =
      reverseBoolVector n (xBeforeSpecial n ω) := by
  have h := xBeforeSpecial_dualHardSample n (dualHardSample n ω)
  have hdual := congrArg (reverseBoolVector n) h
  simpa [dualHardSample_dualHardSample,
    reverseBoolVector_reverseBoolVector] using hdual.symm

/-- Alice's `X_≤T` vector in the dual is Bob's `Y_≥T` vector in reverse order. -/
theorem xLeSpecial_dualHardSample (ω : HardSample n) :
    xLeSpecial n (dualHardSample n ω) =
      reverseBoolVector n (yGeSpecial n ω) := by
  funext i
  change
    (if i ≤ Fin.rev ω.T then xBit n (dualHardSample n ω) i else false) =
      (if ω.T ≤ Fin.rev i then yBit n ω (Fin.rev i) else false)
  rw [xBit_dualHardSample]
  by_cases h : i ≤ Fin.rev ω.T
  · have h' : ω.T ≤ Fin.rev i := (Fin.le_rev_iff).1 h
    simp [h, h']
  · have h' : ¬ω.T ≤ Fin.rev i := by
      intro h'
      exact h ((Fin.le_rev_iff).2 h')
    simp [h, h']

/-- Bob's `Y_≥T` vector in the dual is Alice's `X_≤T` vector in reverse order. -/
theorem yGeSpecial_dualHardSample (ω : HardSample n) :
    yGeSpecial n (dualHardSample n ω) =
      reverseBoolVector n (xLeSpecial n ω) := by
  have h := xLeSpecial_dualHardSample n (dualHardSample n ω)
  have hdual := congrArg (reverseBoolVector n) h
  simpa [dualHardSample_dualHardSample,
    reverseBoolVector_reverseBoolVector] using hdual.symm

/-- The coarse `Z` conditioning data is self-dual up to the conditioning-value recoding. -/
theorem coarseConditioning_dualHardSample (ω : HardSample n) :
    coarseConditioning n (dualHardSample n ω) =
      dualConditioningValue n (coarseConditioning n ω) := by
  rw [coarseConditioning, coarseConditioning, dualConditioningValue,
    xBeforeSpecial_dualHardSample, yAfterSpecial_dualHardSample]
  simp [specialCoordinate, dualHardSample]

/-- Alice's corrected conditioning in the dual is Bob's corrected conditioning in recoded form. -/
theorem aliceClaimConditioning_dualHardSample (ω : HardSample n) :
    aliceClaimConditioning n (dualHardSample n ω) =
      dualConditioningValue n (bobClaimConditioning n ω) := by
  rw [aliceClaimConditioning, bobClaimConditioning, dualConditioningValue,
    xBeforeSpecial_dualHardSample, yGeSpecial_dualHardSample]
  simp [specialCoordinate, dualHardSample]

/-- Bob's corrected conditioning in the dual is Alice's corrected conditioning in recoded form. -/
theorem bobClaimConditioning_dualHardSample (ω : HardSample n) :
    bobClaimConditioning n (dualHardSample n ω) =
      dualConditioningValue n (aliceClaimConditioning n ω) := by
  rw [bobClaimConditioning, aliceClaimConditioning, dualConditioningValue,
    xLeSpecial_dualHardSample, yAfterSpecial_dualHardSample]
  simp [specialCoordinate, dualHardSample]

/-- If two samples agree on the data contained in `Z`, then Alice's bit from the first sample and
Bob's bit from the second sample are disjoint away from the special coordinate. -/
theorem not_xBit_left_and_yBit_right_of_same_conditioning
    {ωX ωY : HardSample n}
    (hT : ωX.T = ωY.T)
    (hBefore : xBeforeSpecial n ωX = xBeforeSpecial n ωY)
    (hAfter : yAfterSpecial n ωX = yAfterSpecial n ωY)
    {i : Fin n} (hi : i ≠ ωX.T) :
    ¬(xBit n ωX i = true ∧ yBit n ωY i = true) := by
  intro hbits
  by_cases hlt : i < ωX.T
  · have hltY : i < ωY.T := by
      simpa [← hT] using hlt
    have hx_eq : xBit n ωY i = xBit n ωX i := by
      have hfun := congrFun hBefore i
      simpa [xBeforeSpecial, hlt, hltY] using hfun.symm
    exact not_xBit_and_yBit_of_ne_special n ωY (by simpa [← hT] using hi)
      ⟨hx_eq.trans hbits.1, hbits.2⟩
  · have hgt : ωX.T < i := lt_of_le_of_ne (le_of_not_gt hlt) hi.symm
    have hgtY : ωY.T < i := by
      simpa [← hT] using hgt
    have hy_eq : yBit n ωX i = yBit n ωY i := by
      have hfun := congrFun hAfter i
      simpa [yAfterSpecial, hgt, hgtY] using hfun
    exact not_xBit_and_yBit_of_ne_special n ωX hi
      ⟨hbits.1, hy_eq.trans hbits.2⟩

/-- The mixed sample has Alice's input bits from the first sample. -/
theorem xBit_mix
    {ωX ωY : HardSample n}
    (hT : ωX.T = ωY.T)
    (hBefore : xBeforeSpecial n ωX = xBeforeSpecial n ωY)
    (hAfter : yAfterSpecial n ωX = yAfterSpecial n ωY)
    (i : Fin n) :
    xBit n (mix n ωX ωY) i = xBit n ωX i := by
  by_cases hi : i = ωX.T
  · subst hi
    simp [mix, xBit]
  · have hdisj :=
      not_xBit_left_and_yBit_right_of_same_conditioning n hT hBefore hAfter hi
    have hdisj' :
        ¬((ωX.other i).xBit = true ∧ yBit n ωY i = true) := by
      simpa [xBit_of_ne_special n ωX hi] using hdisj
    simp [mix, xBit, hi, coordinateOfBits_xBit hdisj']

/-- The mixed sample has Bob's input bits from the second sample. -/
theorem yBit_mix
    {ωX ωY : HardSample n}
    (hT : ωX.T = ωY.T)
    (hBefore : xBeforeSpecial n ωX = xBeforeSpecial n ωY)
    (hAfter : yAfterSpecial n ωX = yAfterSpecial n ωY)
    (i : Fin n) :
    yBit n (mix n ωX ωY) i = yBit n ωY i := by
  by_cases hi : i = ωX.T
  · subst hi
    simp [mix, yBit, hT]
  · have hdisj :=
      not_xBit_left_and_yBit_right_of_same_conditioning n hT hBefore hAfter hi
    have hiy : i ≠ ωY.T := by
      simpa [← hT] using hi
    have hdisj' :
        ¬(xBit n ωX i = true ∧ (ωY.other i).yBit = true) := by
      simpa [yBit_of_ne_special n ωY hiy] using hdisj
    simp [mix, yBit, hi, hiy, coordinateOfBits_yBit hdisj']

/-- The mixed sample has Alice's full input from the first sample. -/
theorem X_mix
    {ωX ωY : HardSample n}
    (hT : ωX.T = ωY.T)
    (hBefore : xBeforeSpecial n ωX = xBeforeSpecial n ωY)
    (hAfter : yAfterSpecial n ωX = yAfterSpecial n ωY) :
    X n (mix n ωX ωY) = X n ωX := by
  ext i
  simp [X, xBit_mix n hT hBefore hAfter i]

/-- The mixed sample has Bob's full input from the second sample. -/
theorem Y_mix
    {ωX ωY : HardSample n}
    (hT : ωX.T = ωY.T)
    (hBefore : xBeforeSpecial n ωX = xBeforeSpecial n ωY)
    (hAfter : yAfterSpecial n ωX = yAfterSpecial n ωY) :
    Y n (mix n ωX ωY) = Y n ωY := by
  ext i
  simp [Y, yBit_mix n hT hBefore hAfter i]

/-- The mixed sample's generated input is the mixed input pair. -/
theorem input_mix
    {ωX ωY : HardSample n}
    (hT : ωX.T = ωY.T)
    (hBefore : xBeforeSpecial n ωX = xBeforeSpecial n ωY)
    (hAfter : yAfterSpecial n ωX = yAfterSpecial n ωY) :
    input n (mix n ωX ωY) = (X n ωX, Y n ωY) := by
  rw [input, X_mix n hT hBefore hAfter, Y_mix n hT hBefore hAfter]

/-- Mixing preserves Alice's before-`T` conditioning data from the first sample. -/
theorem xBeforeSpecial_mix
    {ωX ωY : HardSample n}
    (hT : ωX.T = ωY.T)
    (hBefore : xBeforeSpecial n ωX = xBeforeSpecial n ωY)
    (hAfter : yAfterSpecial n ωX = yAfterSpecial n ωY) :
    xBeforeSpecial n (mix n ωX ωY) = xBeforeSpecial n ωX := by
  funext i
  by_cases hlt : i < ωX.T
  · simpa [xBeforeSpecial, mix, hlt] using xBit_mix n hT hBefore hAfter i
  · simp [xBeforeSpecial, mix, hlt]

/-- Mixing preserves Bob's after-`T` conditioning data from the second sample. -/
theorem yAfterSpecial_mix
    {ωX ωY : HardSample n}
    (hT : ωX.T = ωY.T)
    (hBefore : xBeforeSpecial n ωX = xBeforeSpecial n ωY)
    (hAfter : yAfterSpecial n ωX = yAfterSpecial n ωY) :
    yAfterSpecial n (mix n ωX ωY) = yAfterSpecial n ωY := by
  funext i
  by_cases hlt : ωY.T < i
  · simpa [yAfterSpecial, mix, hT, hlt] using yBit_mix n hT hBefore hAfter i
  · simp [yAfterSpecial, mix, hT, hlt]

/-- The mixed sample has Alice's special bit from the first sample. -/
theorem specialX_mix (ωX ωY : HardSample n) :
    specialX n (mix n ωX ωY) = specialX n ωX := by
  simp [specialX, mix]

/-- The mixed sample has Bob's special bit from the second sample. -/
theorem specialY_mix (ωX ωY : HardSample n) :
    specialY n (mix n ωX ωY) = specialY n ωY := by
  simp [specialY, mix]

/-- Swapping twice recovers the first sample. This is the involution behind the rectangle-counting
argument for conditional independence on `Z` fibers. -/
theorem mix_mix_swap
    {ωX ωY : HardSample n}
    (hT : ωX.T = ωY.T)
    (hBefore : xBeforeSpecial n ωX = xBeforeSpecial n ωY)
    (hAfter : yAfterSpecial n ωX = yAfterSpecial n ωY) :
    mix n (mix n ωX ωY) (mix n ωY ωX) = ωX := by
  simp only [mix]
  congr
  funext i
  by_cases hi : i = ωX.T
  · simp [hi]
  · have hx := xBit_mix n hT hBefore hAfter i
    have hy := yBit_mix n hT.symm hBefore.symm hAfter.symm i
    simp only [hi, ↓reduceIte]
    change coordinateOfBits (xBit n (mix n ωX ωY) i) (yBit n (mix n ωY ωX) i) =
      ωX.other i
    rw [hx, hy]
    simp [xBit_of_ne_special n ωX hi, yBit_of_ne_special n ωX hi,
      coordinateOfBits_xBit_yBit]

private def specialIntersectEquiv :
    {ω : HardSample n // ω ∈ specialIntersect n} ≃
      Fin n × (Fin n → DisjointCoordinate) where
  toFun ω := (ω.1.T, ω.1.other)
  invFun p :=
    ⟨{ T := p.1
       xT := true
       yT := true
       other := p.2 }, by simp [specialIntersect]⟩
  left_inv ω := by
    rcases ω with ⟨⟨T, xT, yT, other⟩, hω⟩
    rcases hω with ⟨hxT, hyT⟩
    cases hxT
    cases hyT
    rfl
  right_inv p := by
    rcases p with ⟨T, other⟩
    rfl

private def specialBitsEventEquiv (bx bY : Bool) :
    {ω : HardSample n // ω ∈ specialBitsEvent n bx bY} ≃
      Fin n × (Fin n → DisjointCoordinate) where
  toFun ω := (ω.1.T, ω.1.other)
  invFun p :=
    ⟨{ T := p.1
       xT := bx
       yT := bY
       other := p.2 }, by simp [specialBitsEvent]⟩
  left_inv ω := by
    rcases ω with ⟨⟨T, xT, yT, other⟩, hω⟩
    rcases hω with ⟨hxT, hyT⟩
    cases hxT
    cases hyT
    rfl
  right_inv p := by
    rcases p with ⟨T, other⟩
    rfl

private def specialCoordinateEventEquiv (i : Fin n) :
    {ω : HardSample n // ω ∈ specialCoordinateEvent n i} ≃
      Bool × Bool × (Fin n → DisjointCoordinate) where
  toFun ω := (ω.1.xT, ω.1.yT, ω.1.other)
  invFun p :=
    ⟨{ T := i
       xT := p.1
       yT := p.2.1
       other := p.2.2 }, by simp [specialCoordinateEvent]⟩
  left_inv ω := by
    rcases ω with ⟨⟨T, xT, yT, other⟩, hω⟩
    simp only [specialCoordinateEvent, Set.mem_setOf_eq] at hω
    subst T
    rfl
  right_inv p := by
    rcases p with ⟨xT, yT, other⟩
    rfl

private def specialCoordinateEventInterSpecialIntersectEquiv (i : Fin n) :
    {ω : HardSample n // ω ∈ specialCoordinateEvent n i ∩ specialIntersect n} ≃
      (Fin n → DisjointCoordinate) where
  toFun ω := ω.1.other
  invFun other :=
    ⟨{ T := i
       xT := true
       yT := true
       other := other }, by simp [specialCoordinateEvent, specialIntersect]⟩
  left_inv ω := by
    rcases ω with ⟨⟨T, xT, yT, other⟩, hω⟩
    rcases hω with ⟨hT, hxT, hyT⟩
    simp [specialCoordinateEvent] at hT
    simp only at hxT hyT
    subst T
    subst xT
    subst yT
    rfl
  right_inv other := rfl

noncomputable instance specialCoordinateEventInterSpecialIntersectFintype (i : Fin n) :
    Fintype {ω : HardSample n // ω ∈ specialCoordinateEvent n i ∩ specialIntersect n} :=
  Fintype.ofEquiv (Fin n → DisjointCoordinate)
    (specialCoordinateEventInterSpecialIntersectEquiv n i).symm

theorem card_specialIntersect :
    Fintype.card {ω : HardSample n // ω ∈ specialIntersect n} =
      (n : ℕ) * 3 ^ (n : ℕ) := by
  calc
    Fintype.card {ω : HardSample n // ω ∈ specialIntersect n} =
        Fintype.card (Fin n × (Fin n → DisjointCoordinate)) :=
      Fintype.card_congr (specialIntersectEquiv n)
    _ = (n : ℕ) * 3 ^ (n : ℕ) := by
      simp [Fintype.card_prod, Fintype.card_pi, DisjointCoordinate.card]

theorem card_specialBitsEvent (bx bY : Bool) :
    Fintype.card {ω : HardSample n // ω ∈ specialBitsEvent n bx bY} =
      (n : ℕ) * 3 ^ (n : ℕ) := by
  calc
    Fintype.card {ω : HardSample n // ω ∈ specialBitsEvent n bx bY} =
        Fintype.card (Fin n × (Fin n → DisjointCoordinate)) :=
      Fintype.card_congr (specialBitsEventEquiv n bx bY)
    _ = (n : ℕ) * 3 ^ (n : ℕ) := by
      simp [Fintype.card_prod, Fintype.card_pi, DisjointCoordinate.card]

theorem card_specialCoordinateEvent (i : Fin n) :
    Fintype.card {ω : HardSample n // ω ∈ specialCoordinateEvent n i} =
      4 * 3 ^ (n : ℕ) := by
  calc
    Fintype.card {ω : HardSample n // ω ∈ specialCoordinateEvent n i} =
        Fintype.card (Bool × Bool × (Fin n → DisjointCoordinate)) :=
      Fintype.card_congr (specialCoordinateEventEquiv n i)
    _ = 4 * 3 ^ (n : ℕ) := by
      simp [Fintype.card_prod, Fintype.card_pi, DisjointCoordinate.card]
      ring

theorem card_specialCoordinateEvent_inter_specialIntersect (i : Fin n) :
    Fintype.card {ω : HardSample n // ω ∈ specialCoordinateEvent n i ∩ specialIntersect n} =
      3 ^ (n : ℕ) := by
  calc
    Fintype.card {ω : HardSample n // ω ∈ specialCoordinateEvent n i ∩ specialIntersect n} =
        Fintype.card (Fin n → DisjointCoordinate) :=
      Fintype.card_congr (specialCoordinateEventInterSpecialIntersectEquiv n i)
    _ = 3 ^ (n : ℕ) := by
      simp [Fintype.card_pi, DisjointCoordinate.card]

open Classical in
/-- The hard distribution creates an intersection with probability `1 / 4`. -/
theorem measureReal_specialIntersect :
    (volume (specialIntersect n)).toReal = (1 / 4 : ℝ) := by
  letI : DecidablePred (fun ω : HardSample n => ω ∈ specialIntersect n) :=
    fun ω => Classical.propDecidable (ω ∈ specialIntersect n)
  change ((ProbabilityTheory.uniformOn Set.univ : Measure (HardSample n))
      (specialIntersect n)).toReal = (1 / 4 : ℝ)
  rw [uniformOn_univ_measureReal_eq_card_filter]
  have hfilter :
      (Finset.univ.filter fun ω : HardSample n => ω ∈ specialIntersect n).card =
        Fintype.card {ω : HardSample n // ω ∈ specialIntersect n} := by
    simp [Fintype.card_subtype]
  have hfilter_real :
      ((Finset.univ.filter fun ω : HardSample n => ω ∈ specialIntersect n).card : ℝ) =
        (Fintype.card {ω : HardSample n // ω ∈ specialIntersect n} : ℝ) := by
    exact_mod_cast hfilter
  rw [hfilter_real, card_specialIntersect, HardSample.card]
  have hn : ((n : ℕ) : ℝ) ≠ 0 := by positivity
  have hpow : ((3 ^ (n : ℕ) : ℕ) : ℝ) ≠ 0 := by positivity
  norm_num [Nat.cast_mul, Nat.cast_pow]
  field_simp [hn, hpow]

open Classical in
/-- Each prescribed pair of special-coordinate bits has probability `1 / 4`. -/
theorem measureReal_specialBitsEvent (bx bY : Bool) :
    (volume (specialBitsEvent n bx bY)).toReal = (1 / 4 : ℝ) := by
  letI : DecidablePred (fun ω : HardSample n => ω ∈ specialBitsEvent n bx bY) :=
    fun ω => Classical.propDecidable (ω ∈ specialBitsEvent n bx bY)
  change ((ProbabilityTheory.uniformOn Set.univ : Measure (HardSample n))
      (specialBitsEvent n bx bY)).toReal = (1 / 4 : ℝ)
  rw [uniformOn_univ_measureReal_eq_card_filter]
  have hfilter :
      (Finset.univ.filter fun ω : HardSample n => ω ∈ specialBitsEvent n bx bY).card =
        Fintype.card {ω : HardSample n // ω ∈ specialBitsEvent n bx bY} := by
    simp [Fintype.card_subtype]
  have hfilter_real :
      ((Finset.univ.filter fun ω : HardSample n => ω ∈ specialBitsEvent n bx bY).card : ℝ) =
        (Fintype.card {ω : HardSample n // ω ∈ specialBitsEvent n bx bY} : ℝ) := by
    exact_mod_cast hfilter
  rw [hfilter_real, card_specialBitsEvent, HardSample.card]
  have hn : ((n : ℕ) : ℝ) ≠ 0 := by positivity
  have hpow : ((3 ^ (n : ℕ) : ℕ) : ℝ) ≠ 0 := by positivity
  norm_num [Nat.cast_mul, Nat.cast_pow]
  field_simp [hn, hpow]

open Classical in
/-- Under the hard distribution, the special coordinate is uniform. -/
theorem measureReal_specialCoordinateEvent (i : Fin n) :
    (volume (specialCoordinateEvent n i)).toReal = (1 / (n : ℝ) : ℝ) := by
  change ((ProbabilityTheory.uniformOn Set.univ : Measure (HardSample n))
      (specialCoordinateEvent n i)).toReal = (1 / (n : ℝ) : ℝ)
  rw [uniformOn_univ_measureReal_eq_card_subtype, card_specialCoordinateEvent, HardSample.card]
  have hn : ((n : ℕ) : ℝ) ≠ 0 := by positivity
  have hpow : ((3 ^ (n : ℕ) : ℕ) : ℝ) ≠ 0 := by positivity
  norm_num [Nat.cast_mul, Nat.cast_pow]
  field_simp [hn, hpow]

open Classical in
/-- Under the hard distribution, `T=i` and the special bits intersect with probability
`1/(4n)`. -/
theorem measureReal_specialCoordinateEvent_inter_specialIntersect (i : Fin n) :
    (volume (specialCoordinateEvent n i ∩ specialIntersect n)).toReal =
      (1 / (4 * (n : ℝ)) : ℝ) := by
  change ((ProbabilityTheory.uniformOn Set.univ : Measure (HardSample n))
      (specialCoordinateEvent n i ∩ specialIntersect n)).toReal =
    (1 / (4 * (n : ℝ)) : ℝ)
  rw [uniformOn_univ_measureReal_eq_card_subtype,
    card_specialCoordinateEvent_inter_specialIntersect, HardSample.card]
  have hn : ((n : ℕ) : ℝ) ≠ 0 := by positivity
  have hpow : ((3 ^ (n : ℕ) : ℕ) : ℝ) ≠ 0 := by positivity
  norm_num [Nat.cast_mul, Nat.cast_pow]
  field_simp [hn, hpow]

/-- The event `(X_T, Y_T) = (0, 0)` has probability `1 / 4`. -/
theorem measureReal_specialZeroZero :
    (volume (specialZeroZero n)).toReal = (1 / 4 : ℝ) := by
  rw [specialZeroZero, measureReal_specialBitsEvent]

/-- The event `Y_T = false` has probability `1 / 2`. -/
theorem measureReal_specialY_false :
    (volume (((specialY n) ⁻¹' {false}) : Set (HardSample n))).toReal = (1 / 2 : ℝ) := by
  have hset :
      ((specialY n) ⁻¹' {false} : Set (HardSample n)) =
        specialBitsEvent n false false ∪ specialBitsEvent n true false := by
    ext ω
    rcases ω with ⟨T, xT, yT, other⟩
    cases xT <;> cases yT <;> simp [specialY, specialBitsEvent]
  have hdisj : Disjoint (specialBitsEvent n false false) (specialBitsEvent n true false) := by
    rw [Set.disjoint_left]
    intro ω hfalse htrue
    have hxFalse : ω.xT = false := by
      simpa [specialBitsEvent] using hfalse.1
    have hxTrue : ω.xT = true := by
      simpa [specialBitsEvent] using htrue.1
    rw [hxFalse] at hxTrue
    simp at hxTrue
  change (volume : Measure (HardSample n)).real ((specialY n) ⁻¹' {false}) = (1 / 2 : ℝ)
  rw [hset, measureReal_union hdisj MeasurableSet.of_discrete]
  rw [show (volume : Measure (HardSample n)).real (specialBitsEvent n false false) =
      (1 / 4 : ℝ) by
    simpa [Measure.real] using measureReal_specialBitsEvent n false false]
  rw [show (volume : Measure (HardSample n)).real (specialBitsEvent n true false) =
      (1 / 4 : ℝ) by
    simpa [Measure.real] using measureReal_specialBitsEvent n true false]
  norm_num

/-- The disjoint event is the complement of the special-intersection event. -/
theorem disjointEvent_eq_compl_specialIntersect :
    disjointEvent n = (specialIntersect n)ᶜ := by
  ext ω
  simp [disjointEvent, specialIntersect, disjoint_X_Y_iff]

/-- The hard distribution generates disjoint inputs with probability `3 / 4`. -/
theorem measureReal_disjointEvent :
    (volume (disjointEvent n)).toReal = (3 / 4 : ℝ) := by
  rw [disjointEvent_eq_compl_specialIntersect]
  change ((volume : Measure (HardSample n)).real ((specialIntersect n)ᶜ)) = (3 / 4 : ℝ)
  rw [measureReal_compl MeasurableSet.of_discrete]
  rw [probReal_univ]
  rw [show (volume : Measure (HardSample n)).real (specialIntersect n) = (1 / 4 : ℝ) by
    simpa [Measure.real] using measureReal_specialIntersect n]
  norm_num

open Classical in
/-- Under the hard distribution, `T=i` and disjointness have probability `3/(4n)`. -/
theorem measureReal_specialCoordinateEvent_inter_disjointEvent (i : Fin n) :
    (volume (specialCoordinateEvent n i ∩ disjointEvent n)).toReal =
      (3 / (4 * (n : ℝ)) : ℝ) := by
  have hset :
      specialCoordinateEvent n i ∩ disjointEvent n =
        specialCoordinateEvent n i \ (specialCoordinateEvent n i ∩ specialIntersect n) := by
    rw [disjointEvent_eq_compl_specialIntersect]
    ext ω
    simp
  change (volume : Measure (HardSample n)).real (specialCoordinateEvent n i ∩ disjointEvent n) =
    (3 / (4 * (n : ℝ)) : ℝ)
  rw [hset]
  rw [measureReal_diff]
  · rw [show (volume : Measure (HardSample n)).real (specialCoordinateEvent n i) =
        (1 / (n : ℝ) : ℝ) by
      simpa [Measure.real] using measureReal_specialCoordinateEvent n i]
    rw [show (volume : Measure (HardSample n)).real
        (specialCoordinateEvent n i ∩ specialIntersect n) =
          (1 / (4 * (n : ℝ)) : ℝ) by
      simpa [Measure.real] using measureReal_specialCoordinateEvent_inter_specialIntersect n i]
    have hn : (n : ℝ) ≠ 0 := by positivity
    field_simp [hn]
    ring
  · exact Set.inter_subset_left
  · exact MeasurableSet.of_discrete

/-- The disjoint event has positive measure under the hard distribution. -/
theorem measure_disjointEvent_ne_zero :
    (volume : Measure (HardSample n)) (disjointEvent n) ≠ 0 := by
  have hreal :
      ((volume : Measure (HardSample n)) (disjointEvent n)).toReal ≠ 0 := by
    rw [measureReal_disjointEvent n]
    norm_num
  exact (ENNReal.toReal_ne_zero.mp hreal).1

/-- The hard distribution conditioned on the generated input being disjoint. -/
noncomputable def disjointCondMeasure : Measure (HardSample n) :=
  (volume : Measure (HardSample n))[|disjointEvent n]

open Classical in
/-- Under the disjoint-conditioned hard distribution, the special coordinate remains uniform. -/
theorem disjointCondMeasure_measureReal_specialCoordinateEvent (i : Fin n) :
    (disjointCondMeasure n).real (specialCoordinateEvent n i) =
      (1 / (n : ℝ) : ℝ) := by
  rw [disjointCondMeasure]
  rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  have hinter :
      disjointEvent n ∩ specialCoordinateEvent n i =
        specialCoordinateEvent n i ∩ disjointEvent n := by
    rw [Set.inter_comm]
  have hnum :
      (volume : Measure (HardSample n)).real (specialCoordinateEvent n i ∩ disjointEvent n) =
        (3 / (4 * (n : ℝ)) : ℝ) := by
    simpa [Measure.real] using measureReal_specialCoordinateEvent_inter_disjointEvent n i
  have hden : (volume : Measure (HardSample n)).real (disjointEvent n) = (3 / 4 : ℝ) := by
    simpa [Measure.real] using measureReal_disjointEvent n
  rw [hinter, hnum, hden]
  have hn : (n : ℝ) ≠ 0 := by positivity
  field_simp [hn]

/-- The special-coordinate singleton event is the corresponding named event. -/
theorem specialCoordinate_preimage_singleton (i : Fin n) :
    (specialCoordinate n) ⁻¹' {i} = specialCoordinateEvent n i := by
  ext ω
  simp [specialCoordinate, specialCoordinateEvent]

open Classical in
/-- Under the disjoint-conditioned distribution, preimages of special-coordinate singletons
have the uniform mass. -/
theorem disjointCondMeasure_measureReal_specialCoordinate_preimage_singleton (i : Fin n) :
    (disjointCondMeasure n).real ((specialCoordinate n) ⁻¹' {i}) =
      (1 / (n : ℝ) : ℝ) := by
  rw [specialCoordinate_preimage_singleton,
    disjointCondMeasure_measureReal_specialCoordinateEvent]

open Classical in
/-- Under disjoint conditioning, integrating a function of `T` is the uniform coordinate
average. -/
theorem integral_specialCoordinate_disjointCondMeasure (f : Fin n → ℝ) :
    (∫ ω, f (specialCoordinate n ω) ∂(disjointCondMeasure n)) =
      (1 / (n : ℝ) : ℝ) * ∑ i : Fin n, f i := by
  haveI : IsProbabilityMeasure (disjointCondMeasure n) := by
    rw [disjointCondMeasure]
    exact ProbabilityTheory.cond_isProbabilityMeasure (measure_disjointEvent_ne_zero n)
  rw [FiniteMeasureSpace.integral_comp_eq_sum_measureReal_fibers
    (μ := disjointCondMeasure n) (Z := specialCoordinate n) (f := f)]
  simp_rw [disjointCondMeasure_measureReal_specialCoordinate_preimage_singleton]
  rw [Finset.mul_sum]

/-- Under the measure conditioned on disjointness, the disjointness event holds almost surely. -/
theorem disjointCondMeasure_ae_disjointEvent :
    ∀ᵐ ω ∂disjointCondMeasure n, ω ∈ disjointEvent n := by
  rw [disjointCondMeasure]
  exact ae_cond_mem MeasurableSet.of_discrete

/-- If Bob's special bit is `false`, the generated inputs are disjoint. -/
theorem mem_disjointEvent_of_specialY_eq_false
    {ω : HardSample n} (hY : specialY n ω = false) :
    ω ∈ disjointEvent n := by
  change Disjoint (X n ω) (Y n ω)
  rw [disjoint_X_Y_iff]
  intro hboth
  rw [show ω.yT = false by simpa [specialY] using hY] at hboth
  simp at hboth

/-- A prescribed special-coordinate bit pair is disjoint exactly when it is not `(true,true)`. -/
theorem specialBitsEvent_subset_disjointEvent
    (bx bY : Bool) (hbits : ¬(bx = true ∧ bY = true)) :
    specialBitsEvent n bx bY ⊆ disjointEvent n := by
  intro ω hω
  rw [specialBitsEvent] at hω
  change Disjoint (X n ω) (Y n ω)
  rw [disjoint_X_Y_iff]
  intro hspecial
  exact hbits ⟨hω.1.symm.trans hspecial.1, hω.2.symm.trans hspecial.2⟩

/-- The `(X_T,Y_T)=(0,0)` slice is contained in the disjoint event. -/
theorem specialZeroZero_subset_disjointEvent :
    specialZeroZero n ⊆ disjointEvent n := by
  intro ω hω
  rw [specialZeroZero, specialBitsEvent] at hω
  exact mem_disjointEvent_of_specialY_eq_false n (by simpa [specialY] using hω.2)

/-- Under the disjoint-conditioned hard distribution, `(X_T,Y_T)=(0,0)` has mass `1 / 3`. -/
theorem disjointCondMeasure_measureReal_specialZeroZero :
    (disjointCondMeasure n).real (specialZeroZero n) = (1 / 3 : ℝ) := by
  rw [disjointCondMeasure]
  rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  have hinter :
      disjointEvent n ∩ specialZeroZero n = specialZeroZero n := by
    exact Set.inter_eq_right.mpr (specialZeroZero_subset_disjointEvent n)
  rw [hinter]
  rw [show (volume : Measure (HardSample n)).real (disjointEvent n) = (3 / 4 : ℝ) by
    simpa [Measure.real] using measureReal_disjointEvent n]
  rw [show (volume : Measure (HardSample n)).real (specialZeroZero n) = (1 / 4 : ℝ) by
    simpa [Measure.real] using measureReal_specialZeroZero n]
  norm_num

open Classical in
/-- Under the disjoint-conditioned hard distribution, each non-intersecting special bit-pair has
mass `1/3`. -/
theorem disjointCondMeasure_measureReal_specialBitsEvent
    (bx bY : Bool) (hbits : ¬(bx = true ∧ bY = true)) :
    (disjointCondMeasure n).real (specialBitsEvent n bx bY) = (1 / 3 : ℝ) := by
  rw [disjointCondMeasure]
  rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  have hinter :
      disjointEvent n ∩ specialBitsEvent n bx bY = specialBitsEvent n bx bY := by
    exact Set.inter_eq_right.mpr (specialBitsEvent_subset_disjointEvent n bx bY hbits)
  rw [hinter]
  rw [show (volume : Measure (HardSample n)).real (disjointEvent n) = (3 / 4 : ℝ) by
    simpa [Measure.real] using measureReal_disjointEvent n]
  rw [show (volume : Measure (HardSample n)).real (specialBitsEvent n bx bY) = (1 / 4 : ℝ) by
    simpa [Measure.real] using measureReal_specialBitsEvent n bx bY]
  norm_num

/-- Under the disjoint-conditioned hard distribution, `Y_T=false` has mass `2 / 3`. -/
theorem disjointCondMeasure_measureReal_specialY_false :
    (disjointCondMeasure n).real (((specialY n) ⁻¹' {false}) : Set (HardSample n)) =
      (2 / 3 : ℝ) := by
  rw [disjointCondMeasure]
  rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  have hsubset : ((specialY n) ⁻¹' {false} : Set (HardSample n)) ⊆ disjointEvent n := by
    intro ω hω
    exact mem_disjointEvent_of_specialY_eq_false n (by simpa using hω)
  have hinter :
      disjointEvent n ∩ ((specialY n) ⁻¹' {false} : Set (HardSample n)) =
        (specialY n) ⁻¹' {false} := by
    exact Set.inter_eq_right.mpr hsubset
  rw [hinter]
  rw [show (volume : Measure (HardSample n)).real (disjointEvent n) = (3 / 4 : ℝ) by
    simpa [Measure.real] using measureReal_disjointEvent n]
  rw [show (volume : Measure (HardSample n)).real
      (((specialY n) ⁻¹' {false}) : Set (HardSample n)) = (1 / 2 : ℝ) by
    simpa [Measure.real] using measureReal_specialY_false n]
  norm_num

open Classical in
/-- The disjoint-conditioned hard distribution, further conditioned on Bob's special bit being
`false`. This is the Alice-side conditioning used in the Claim 6.21 Pinsker step. -/
noncomputable def disjointSpecialYFalseMeasure : Measure (HardSample n) :=
  (disjointCondMeasure n)[|(specialY n) ⁻¹' {false}]

open Classical in
/-- Conditioning the disjoint law on `Y_T = false` gives a probability measure. -/
theorem disjointSpecialYFalseMeasure_isProbabilityMeasure :
    IsProbabilityMeasure (disjointSpecialYFalseMeasure n) := by
  haveI : IsProbabilityMeasure (disjointCondMeasure n) := by
    rw [disjointCondMeasure]
    exact ProbabilityTheory.cond_isProbabilityMeasure (measure_disjointEvent_ne_zero n)
  rw [disjointSpecialYFalseMeasure]
  apply ProbabilityTheory.cond_isProbabilityMeasure
  rw [← MeasureTheory.measureReal_ne_zero_iff]
  rw [disjointCondMeasure_measureReal_specialY_false]
  norm_num

open Classical in
/-- Under `D ∧ Y_T=false`, Alice's special bit is uniform. -/
theorem disjointSpecialYFalseMeasure_measureReal_specialX_singleton (b : Bool) :
    (disjointSpecialYFalseMeasure n).real ((specialX n) ⁻¹' {b}) = (1 / 2 : ℝ) := by
  rw [disjointSpecialYFalseMeasure]
  rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  have hden :
      (disjointCondMeasure n).real (((specialY n) ⁻¹' {false}) : Set (HardSample n)) =
        (2 / 3 : ℝ) :=
    disjointCondMeasure_measureReal_specialY_false n
  cases b
  · have hinter :
        ((specialY n) ⁻¹' {false} : Set (HardSample n)) ∩ ((specialX n) ⁻¹' {false}) =
          specialZeroZero n := by
      ext ω
      rcases ω with ⟨T, xT, yT, other⟩
      cases xT <;> cases yT <;> simp [specialX, specialY, specialZeroZero, specialBitsEvent]
    rw [hinter, disjointCondMeasure_measureReal_specialZeroZero, hden]
    norm_num
  · have hinter :
        ((specialY n) ⁻¹' {false} : Set (HardSample n)) ∩ ((specialX n) ⁻¹' {true}) =
          specialBitsEvent n true false := by
      ext ω
      rcases ω with ⟨T, xT, yT, other⟩
      cases xT <;> cases yT <;> simp [specialX, specialY, specialBitsEvent]
    rw [hinter]
    rw [disjointCondMeasure_measureReal_specialBitsEvent]
    · rw [hden]
      norm_num
    · simp

noncomputable instance disjointCondMeasure_isProbabilityMeasure :
    IsProbabilityMeasure (disjointCondMeasure n) := by
  rw [disjointCondMeasure]
  exact ProbabilityTheory.cond_isProbabilityMeasure (measure_disjointEvent_ne_zero n)

/-- A measure-preserving self-map leaves every random variable identically distributed with its
pullback along that map. -/
theorem identDistrib_self_comp_measurePreserving
    {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    (F : Ω → α) (hF : Measurable F) :
    IdentDistrib F (F ∘ T) μ μ := by
  refine ⟨hF.aemeasurable, (hF.comp hT.measurable).aemeasurable, ?_⟩
  nth_rw 1 [← hT.map_eq]
  rw [Measure.map_map hF hT.measurable]

/-- The preimage of a singleton under hard-sample duality is the dual singleton. -/
theorem dualHardSample_preimage_singleton (ω : HardSample n) :
    (dualHardSample n) ⁻¹' ({ω} : Set (HardSample n)) =
      {dualHardSample n ω} := by
  ext ω'
  constructor
  · intro h
    have h' : dualHardSample n ω' = ω := by
      simpa using h
    have h'' := congrArg (dualHardSample n) h'
    simpa [dualHardSample_dualHardSample] using h''
  · intro h
    have h' : ω' = dualHardSample n ω := by
      simpa using h
    rw [h']
    simp [dualHardSample_dualHardSample]

/-- The uniform hard-sample measure gives the same mass to a sample and its dual. -/
theorem volume_measureReal_singleton_dualHardSample (ω : HardSample n) :
    (volume : Measure (HardSample n)).real ({dualHardSample n ω} : Set (HardSample n)) =
      (volume : Measure (HardSample n)).real ({ω} : Set (HardSample n)) := by
  change ((ProbabilityTheory.uniformOn Set.univ : Measure (HardSample n)).real
      ({dualHardSample n ω} : Set (HardSample n))) =
    ((ProbabilityTheory.uniformOn Set.univ : Measure (HardSample n)).real
      ({ω} : Set (HardSample n)))
  repeat rw [Measure.real]
  rw [uniformOn_univ_measureReal_eq_card_subtype,
    uniformOn_univ_measureReal_eq_card_subtype]
  simp

/-- Hard-sample duality preserves the uniform hard-sample measure. -/
theorem volume_measurePreserving_dualHardSample :
    MeasurePreserving (dualHardSample n)
      (volume : Measure (HardSample n)) (volume : Measure (HardSample n)) := by
  refine ⟨Measurable.of_discrete, ?_⟩
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro ω
  rw [Measure.real]
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  rw [← Measure.real, dualHardSample_preimage_singleton,
    volume_measureReal_singleton_dualHardSample]

/-- The disjoint-conditioned hard-sample measure gives the same mass to a sample and its dual. -/
theorem disjointCondMeasure_measureReal_singleton_dualHardSample (ω : HardSample n) :
    (disjointCondMeasure n).real ({dualHardSample n ω} : Set (HardSample n)) =
      (disjointCondMeasure n).real ({ω} : Set (HardSample n)) := by
  rw [disjointCondMeasure]
  rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  by_cases hω : ω ∈ disjointEvent n
  · have hdual : dualHardSample n ω ∈ disjointEvent n :=
      (disjointEvent_dualHardSample n ω).2 hω
    have hleft :
        disjointEvent n ∩ ({dualHardSample n ω} : Set (HardSample n)) =
          {dualHardSample n ω} := by
      ext η
      simp [hdual]
    have hright : disjointEvent n ∩ ({ω} : Set (HardSample n)) = {ω} := by
      ext η
      simp [hω]
    rw [hleft, hright, volume_measureReal_singleton_dualHardSample]
  · have hdual : dualHardSample n ω ∉ disjointEvent n := by
      intro h
      exact hω ((disjointEvent_dualHardSample n ω).1 h)
    have hleft :
        disjointEvent n ∩ ({dualHardSample n ω} : Set (HardSample n)) =
          ∅ := by
      ext η
      by_cases hη : η = dualHardSample n ω
      · subst η
        simp [hdual]
      · simp [hη]
    have hright : disjointEvent n ∩ ({ω} : Set (HardSample n)) = ∅ := by
      ext η
      by_cases hη : η = ω
      · subst η
        simp [hω]
      · simp [hη]
    rw [hleft, hright]

/-- Hard-sample duality preserves the disjoint-conditioned hard-sample measure. -/
theorem disjointCondMeasure_measurePreserving_dualHardSample :
    MeasurePreserving (dualHardSample n) (disjointCondMeasure n) (disjointCondMeasure n) := by
  refine ⟨Measurable.of_discrete, ?_⟩
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro ω
  rw [Measure.real]
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  rw [← Measure.real, dualHardSample_preimage_singleton,
    disjointCondMeasure_measureReal_singleton_dualHardSample]

open Classical in
/-- Conditioning on a subevent of disjointness is the same under the ambient hard distribution and
under the hard distribution first conditioned on disjointness. -/
theorem volume_cond_eq_disjointCondMeasure_cond_of_subset_disjointEvent
    {A : Set (HardSample n)} (hA : A ⊆ disjointEvent n) :
    (volume : Measure (HardSample n))[|A] = (disjointCondMeasure n)[|A] := by
  rw [disjointCondMeasure]
  rw [ProbabilityTheory.cond_cond_eq_cond_inter
    MeasurableSet.of_discrete MeasurableSet.of_discrete (volume : Measure (HardSample n))]
  congr 1
  ext ω
  simp [hA]

open Classical in
/-- Conditioning on `(X_T,Y_T)=(0,0)` costs at most a factor `2` relative to conditioning only on
`Y_T=false` under the disjoint distribution. This is the reweighting step before Markov in Claim
6.21. -/
theorem volume_cond_specialZeroZero_measureReal_le_two_mul_disjointSpecialYFalseMeasure
    (S : Set (HardSample n)) :
    ((volume : Measure (HardSample n))[|specialZeroZero n]).real S ≤
      2 * (disjointSpecialYFalseMeasure n).real S := by
  let μ : Measure (HardSample n) := disjointCondMeasure n
  let Y0 : Set (HardSample n) := (specialY n) ⁻¹' {false}
  have hzero_subset_y0 : specialZeroZero n ⊆ Y0 := by
    intro ω hω
    rw [specialZeroZero, specialBitsEvent] at hω
    simpa [Y0, specialY] using hω.2
  have hcond_zero :
      (volume : Measure (HardSample n))[|specialZeroZero n] = μ[|specialZeroZero n] := by
    simpa [μ] using
      volume_cond_eq_disjointCondMeasure_cond_of_subset_disjointEvent n
        (specialZeroZero_subset_disjointEvent n)
  have hleft :
      ((volume : Measure (HardSample n))[|specialZeroZero n]).real S =
        (μ.real (specialZeroZero n))⁻¹ * μ.real (specialZeroZero n ∩ S) := by
    rw [hcond_zero]
    rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  have hright :
      (disjointSpecialYFalseMeasure n).real S =
        (μ.real Y0)⁻¹ * μ.real (Y0 ∩ S) := by
    rw [disjointSpecialYFalseMeasure]
    change (μ[|Y0]).real S = (μ.real Y0)⁻¹ * μ.real (Y0 ∩ S)
    rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  have hzero_mass : μ.real (specialZeroZero n) = (1 / 3 : ℝ) := by
    simpa [μ] using disjointCondMeasure_measureReal_specialZeroZero n
  have hy0_mass : μ.real Y0 = (2 / 3 : ℝ) := by
    simpa [μ, Y0] using disjointCondMeasure_measureReal_specialY_false n
  have hmono : μ.real (specialZeroZero n ∩ S) ≤ μ.real (Y0 ∩ S) :=
    measureReal_mono (by
      intro ω hω
      exact ⟨hzero_subset_y0 hω.1, hω.2⟩)
  rw [hleft, hright, hzero_mass, hy0_mass]
  norm_num
  linarith

/-- The transcript random variable induced by a deterministic protocol on the hard sample space. -/
noncomputable def message
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (ω : HardSample n) : p.Leaf :=
  p.transcript (input n ω)

/-- The transcript entropy is at most the protocol length in bits, for any ambient measure. -/
theorem entropy_message_le_complexity_mul_log_two_of_measure
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (μ : Measure (HardSample n)) :
    H[message n p ; μ] ≤
      p.complexity * Real.log 2 := by
  letI : Nonempty p.Leaf := ⟨p.transcript (∅, ∅)⟩
  exact ProbabilityTheory.entropy_le_nat_mul_log_two_of_card_le_two_pow
    (message n p) μ
    (Deterministic.Protocol.card_leaf_le_two_pow_complexity p)

/-- The dual protocol transcript on the dual hard sample is the original transcript recoded
through protocol duality. -/
theorem message_dualProtocol_dualHardSample
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (ω : HardSample n) :
    message n (dualProtocol n p) (dualHardSample n ω) =
      dualProtocolLeafMap n p (message n p ω) := by
  change (p.swap.comap (reverseSet n) (reverseSet n)).transcript
      (input n (dualHardSample n ω)) =
    dualProtocolLeafMap n p (p.transcript (input n ω))
  rw [input_dualHardSample, input]
  rw [← Deterministic.Protocol.leafComap_transcript p.swap (reverseSet n) (reverseSet n)
    (reverseSet n (Y n ω)) (reverseSet n (X n ω))]
  rw [reverseSet_reverseSet, reverseSet_reverseSet]
  rw [← Deterministic.Protocol.leafSwap_transcript p]
  rfl

/-- Dualize a `Z = (M,T,X_<T,Y_>T)` value by recoding the leaf and the coarse conditioning
data. -/
noncomputable def dualZValue
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))) :
    (dualProtocol n p).Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)) :=
  (dualProtocolLeafMap n p z.1, dualConditioningValue n z.2)

/-- The `Z`-value recoding induced by protocol and hard-sample duality is injective. -/
theorem dualZValue_injective
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    Function.Injective (dualZValue n p) := by
  intro z z' h
  rcases z with ⟨leaf, c⟩
  rcases z' with ⟨leaf', c'⟩
  simp only [dualZValue, Prod.mk.injEq] at h ⊢
  exact ⟨dualProtocolLeafMap_injective n p h.1, dualConditioningValue_injective n h.2⟩

/-- The `Z` variable for the dual protocol and hard sample is the recoded original `Z`. -/
theorem zVariable_dualProtocol_dualHardSample
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (ω : HardSample n) :
    zVariable n (dualProtocol n p) (dualHardSample n ω) =
      dualZValue n p (zVariable n p ω) := by
  change (message n (dualProtocol n p) (dualHardSample n ω),
      coarseConditioning n (dualHardSample n ω)) =
    (dualProtocolLeafMap n p (message n p ω),
      dualConditioningValue n (coarseConditioning n ω))
  rw [message_dualProtocol_dualHardSample, coarseConditioning_dualHardSample]

/-- Pulling a recoded dual `Z` fiber back along hard-sample duality gives the original `Z`
fiber. -/
theorem zVariable_dualProtocol_preimage_dualZValue
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))) :
    (dualHardSample n) ⁻¹'
        ((zVariable n (dualProtocol n p)) ⁻¹' {dualZValue n p z}) =
      (zVariable n p) ⁻¹' {z} := by
  ext ω
  change zVariable n (dualProtocol n p) (dualHardSample n ω) = dualZValue n p z ↔
    zVariable n p ω = z
  rw [zVariable_dualProtocol_dualHardSample]
  exact (dualZValue_injective n p).eq_iff

/-- The ambient hard-sample measure gives corresponding original and dual `Z` fibers the same
mass. -/
theorem volume_zVariable_dualProtocol_dualZValue
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))) :
    (volume : Measure (HardSample n))
        ((zVariable n (dualProtocol n p)) ⁻¹' {dualZValue n p z}) =
      (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) := by
  let μ : Measure (HardSample n) := volume
  let S : Set (HardSample n) :=
    (zVariable n (dualProtocol n p)) ⁻¹' {dualZValue n p z}
  have hpre :
      μ ((dualHardSample n) ⁻¹' S) = μ S :=
    Measure.measure_preimage_of_map_eq_self
      (volume_measurePreserving_dualHardSample n).map_eq
      MeasurableSet.of_discrete.nullMeasurableSet
  rw [← hpre]
  exact congrArg (fun S : Set (HardSample n) => μ S)
    (zVariable_dualProtocol_preimage_dualZValue n p z)

/-- Real-valued version of `volume_zVariable_dualProtocol_dualZValue`. -/
theorem volume_measureReal_zVariable_dualProtocol_dualZValue
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))) :
    (volume : Measure (HardSample n)).real
        ((zVariable n (dualProtocol n p)) ⁻¹' {dualZValue n p z}) =
      (volume : Measure (HardSample n)).real ((zVariable n p) ⁻¹' {z}) := by
  repeat rw [Measure.real]
  rw [volume_zVariable_dualProtocol_dualZValue]

/-- Probabilities under the hard input distribution can be computed on the explicit hard sample
space by taking preimages under `input`. -/
theorem inputDist_measureReal_eq_preimage (S : Set (Set (Fin n) × Set (Fin n))) :
    letI := inputDist n
    (volume S).toReal =
      (volume ((input n) ⁻¹' S : Set (HardSample n))).toReal := by
  change
    ((inputProbabilityMeasure n : ProbabilityMeasure (Set (Fin n) × Set (Fin n))) :
        Measure (Set (Fin n) × Set (Fin n))).real S =
      (volume ((input n) ⁻¹' S : Set (HardSample n))).toReal
  rw [inputProbabilityMeasure]
  rw [Measure.real]
  rw [ProbabilityMeasure.map_apply' _ _ MeasurableSet.of_discrete]
  rfl

/-- The sample-space event where a deterministic protocol errs on disjointness. -/
def protocolErrorEvent
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) : Set (HardSample n) :=
  {ω | p.run (X n ω) (Y n ω) ≠ disjointness n (X n ω) (Y n ω)}

/-- Distributional error under the hard input distribution is the probability of the named
sample-space error event. -/
theorem distributionalError_inputDist_eq_protocolErrorEvent
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    p.distributionalError (inputDist n) (disjointness n) =
      (volume (protocolErrorEvent n p)).toReal := by
  rw [Deterministic.Protocol.distributionalError]
  rw [inputDist_measureReal_eq_preimage]
  rfl

/-- The special-coordinate bit-pair. -/
def specialPair (ω : HardSample n) : Bool × Bool :=
  (specialX n ω, specialY n ω)

/-- Uniform law on one bit. -/
noncomputable def uniformBool : ProbabilityMeasure Bool :=
  ⟨ProbabilityTheory.uniformOn Set.univ, inferInstance⟩

/-- Each bit has mass `1 / 2` under the uniform law on one bit. -/
theorem uniformBool_singleton (b : Bool) :
    ((uniformBool : ProbabilityMeasure Bool) : Measure Bool).real {b} =
      (1 / 2 : ℝ) := by
  rw [uniformBool]
  change (ProbabilityTheory.uniformOn Set.univ : Measure Bool).real {b} = (1 / 2 : ℝ)
  rw [Measure.real, ProbabilityTheory.uniformOn_univ]
  norm_num

open Classical in
/-- The law of `X_T` under `D ∧ Y_T=false` is the uniform bit law. -/
theorem disjointSpecialYFalseMeasure_specialX_law_eq_uniformBool :
    ProbabilityMeasure.map
        (⟨disjointSpecialYFalseMeasure n, disjointSpecialYFalseMeasure_isProbabilityMeasure n⟩ :
          ProbabilityMeasure (HardSample n))
        (Measurable.of_discrete.aemeasurable (f := specialX n)) =
      uniformBool := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro b
  rw [Measure.real]
  rw [ProbabilityMeasure.map_apply' _ _ MeasurableSet.of_discrete]
  rw [← Measure.real]
  change (disjointSpecialYFalseMeasure n).real ((specialX n) ⁻¹' {b}) =
    ((uniformBool : ProbabilityMeasure Bool) : Measure Bool).real {b}
  rw [disjointSpecialYFalseMeasure_measureReal_specialX_singleton,
    uniformBool_singleton]

/-- The uniform law on one bit has full support. -/
theorem uniformBool_toPMF_ne_zero (b : Bool) :
    ((uniformBool : ProbabilityMeasure Bool) : Measure Bool).toPMF b ≠ 0 := by
  intro hb
  have hreal :
      (((uniformBool : ProbabilityMeasure Bool) : Measure Bool).toPMF b).toReal =
        (1 / 2 : ℝ) := by
    simpa [Measure.toPMF_apply, Measure.real] using uniformBool_singleton b
  rw [hb] at hreal
  norm_num at hreal

open Classical in
/-- On one-bit probability measures, Mathlib's `klDiv` to the uniform bit law agrees with the
real-valued PFR `KLDiv` used by the entropy API. -/
theorem toReal_klDiv_bool_uniform_eq_KLDiv (μ : ProbabilityMeasure Bool) :
    (InformationTheory.klDiv (μ : Measure Bool)
        ((uniformBool : ProbabilityMeasure Bool) : Measure Bool)).toReal =
      KL[id ; (μ : Measure Bool) # id ;
        ((uniformBool : ProbabilityMeasure Bool) : Measure Bool)] := by
  have hnonneg :
      0 ≤ KL[id ; (μ : Measure Bool) # id ;
        ((uniformBool : ProbabilityMeasure Bool) : Measure Bool)] := by
    exact KLDiv_nonneg (μ := (μ : Measure Bool))
      (μ' := ((uniformBool : ProbabilityMeasure Bool) : Measure Bool))
      (X := id) (Y := id) Measurable.of_discrete Measurable.of_discrete
      (fun b hb => False.elim (uniformBool_toPMF_ne_zero b (by
        simpa [Measure.toPMF_apply] using hb)))
  rw [FiniteMeasureSpace.probabilityMeasure_klDiv_eq_sum_log μ uniformBool]
  rw [if_neg]
  · rw [ENNReal.toReal_ofReal]
    · rw [KLDiv_eq_sum]
      simp [Measure.toPMF_apply, Measure.real]
    · simpa [KLDiv_eq_sum, Measure.toPMF_apply, Measure.real] using hnonneg
  · rintro ⟨b, hb, -⟩
    exact uniformBool_toPMF_ne_zero b hb

open Classical in
/-- Positive conditional fibers let the Mathlib one-bit KL be read as the PFR real-valued
`KLDiv` of the corresponding random variable. -/
theorem toReal_klDiv_map_bool_uniform_eq_KLDiv_of_measureReal_ne_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → Bool) (S : Set Ω) (hX : Measurable X) (hS : μ.real S ≠ 0) :
    (InformationTheory.klDiv (Measure.map X (μ[|S]))
        ((uniformBool : ProbabilityMeasure Bool) : Measure Bool)).toReal =
      KL[X ; μ[|S] # id ;
        ((uniformBool : ProbabilityMeasure Bool) : Measure Bool)] := by
  let μS : ProbabilityMeasure Ω :=
    ⟨μ[|S], ProbabilityTheory.cond_isProbabilityMeasure
      ((MeasureTheory.measureReal_ne_zero_iff (μ := μ) (s := S)).mp hS)⟩
  have h :=
    toReal_klDiv_bool_uniform_eq_KLDiv
      (ProbabilityMeasure.map μS hX.aemeasurable)
  simpa [μS, KLDiv] using h

/-- Uniform law on a bit-pair. -/
noncomputable def uniformBoolPair : ProbabilityMeasure (Bool × Bool) :=
  ⟨ProbabilityTheory.uniformOn Set.univ, inferInstance⟩

/-- Each bit-pair has mass `1 / 4` under the uniform law on two bits. -/
theorem uniformBoolPair_singleton (b : Bool × Bool) :
    ((uniformBoolPair : ProbabilityMeasure (Bool × Bool)) : Measure (Bool × Bool)).real {b} =
      (1 / 4 : ℝ) := by
  rw [uniformBoolPair]
  change (ProbabilityTheory.uniformOn Set.univ : Measure (Bool × Bool)).real {b} = (1 / 4 : ℝ)
  rw [Measure.real, ProbabilityTheory.uniformOn_univ]
  norm_num [Fintype.card_prod]

/-- The uniform law on two bits is the product of the one-bit uniform laws. -/
theorem uniformBoolPair_eq_prod :
    uniformBoolPair =
      TVDistance.probabilityMeasureProd uniformBool uniformBool := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro b
  rw [uniformBoolPair_singleton]
  rcases b with ⟨bx, bY⟩
  rw [TVDistance.probabilityMeasureProd]
  change (1 / 4 : ℝ) =
    (((uniformBool : ProbabilityMeasure Bool) : Measure Bool).prod
        ((uniformBool : ProbabilityMeasure Bool) : Measure Bool) ({(bx, bY)})).toReal
  rw [show ({(bx, bY)} : Set (Bool × Bool)) = ({bx} : Set Bool) ×ˢ ({bY} : Set Bool) by
    ext p
    simp [Prod.ext_iff]]
  rw [Measure.prod_prod, ENNReal.toReal_mul]
  have hx :
      (((uniformBool : ProbabilityMeasure Bool) : Measure Bool) ({bx} : Set Bool)).toReal =
        (1 / 2 : ℝ) := by
    simpa [Measure.real] using uniformBool_singleton bx
  have hy :
      (((uniformBool : ProbabilityMeasure Bool) : Measure Bool) ({bY} : Set Bool)).toReal =
        (1 / 2 : ℝ) := by
    simpa [Measure.real] using uniformBool_singleton bY
  rw [hx, hy]
  norm_num

/-- The hard-distribution measure conditioned on a `Z=z` fiber. -/
noncomputable def zFiberMeasure
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))) :
    Measure (HardSample n) :=
  (volume : Measure (HardSample n))[|(zVariable n p) ⁻¹' {z}]

noncomputable instance zFiberMeasure_isProbabilityMeasure
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)))
    (hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0) :
    IsProbabilityMeasure (zFiberMeasure n p z) := by
  rw [zFiberMeasure]
  exact ProbabilityTheory.cond_isProbabilityMeasure hz

/-- Conditional probabilities under a `Z=z` fiber are computed by intersecting with the fiber and
dividing by its mass. -/
theorem zFiberMeasure_real_apply
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)))
    (S : Set (HardSample n)) :
    (zFiberMeasure n p z).real S =
      ((volume : Measure (HardSample n)).real ((zVariable n p) ⁻¹' {z}))⁻¹ *
        (volume : Measure (HardSample n)).real (((zVariable n p) ⁻¹' {z}) ∩ S) := by
  rw [zFiberMeasure]
  exact ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete _ S

open Classical in
/-- The mass of a `Z` fiber under the Alice-side conditioned measure, with the `3/2` scaling
from `Pr_D[Y_T=false]=2/3` made explicit. -/
theorem disjointSpecialYFalseMeasure_measureReal_zVariable
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))) :
    (disjointSpecialYFalseMeasure n).real ((zVariable n p) ⁻¹' {z}) =
      (3 / 2 : ℝ) *
        (disjointCondMeasure n).real
          (((specialY n) ⁻¹' {false}) ∩ ((zVariable n p) ⁻¹' {z})) := by
  rw [disjointSpecialYFalseMeasure]
  rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  rw [disjointCondMeasure_measureReal_specialY_false]
  ring

open Classical in
/-- Conditioning first on `Y_T=false` under `D`, then on a `Z` value, is the same as
conditioning under `D` on the intersection of those events. -/
theorem disjointSpecialYFalseMeasure_cond_zVariable_eq_cond_inter
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))) :
    (disjointSpecialYFalseMeasure n)[|zVariable n p ← z] =
      (disjointCondMeasure n)[|
        ((specialY n) ⁻¹' {false}) ∩ ((zVariable n p) ⁻¹' {z})] := by
  rw [disjointSpecialYFalseMeasure]
  exact ProbabilityTheory.cond_cond_eq_cond_inter
    MeasurableSet.of_discrete MeasurableSet.of_discrete (disjointCondMeasure n)

open Classical in
/-- Conditioning a `Z=z` fiber further on a special Bob-bit value is the same as conditioning the
ambient hard distribution on the intersection of those two fiber events. -/
theorem zFiberMeasure_cond_specialY_eq_volume_cond_inter
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)))
    (b : Bool) :
    (zFiberMeasure n p z)[|(specialY n) ⁻¹' {b}] =
      (volume : Measure (HardSample n))[|
        ((zVariable n p) ⁻¹' {z}) ∩ ((specialY n) ⁻¹' {b})] := by
  rw [zFiberMeasure]
  exact ProbabilityTheory.cond_cond_eq_cond_inter
    MeasurableSet.of_discrete MeasurableSet.of_discrete (volume : Measure (HardSample n))

/-- The event `Z=z ∧ Y_T=false` is contained in the disjoint-input event. -/
theorem zVariable_inter_specialYFalse_subset_disjointEvent
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))) :
    ((zVariable n p) ⁻¹' {z}) ∩ ((specialY n) ⁻¹' {false}) ⊆ disjointEvent n := by
  intro ω hω
  exact mem_disjointEvent_of_specialY_eq_false n (by simpa using hω.2)

open Classical in
/-- Conditioning a `Z=z` fiber further on `Y_T=false` agrees with conditioning the
`D ∧ Y_T=false` measure on the same `Z` fiber. -/
theorem zFiberMeasure_cond_specialYFalse_eq_disjointSpecialYFalseMeasure_cond_zVariable
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))) :
    (zFiberMeasure n p z)[|(specialY n) ⁻¹' {false}] =
      (disjointSpecialYFalseMeasure n)[|zVariable n p ← z] := by
  rw [zFiberMeasure_cond_specialY_eq_volume_cond_inter]
  rw [show ((zVariable n p) ⁻¹' {z}) ∩ ((specialY n) ⁻¹' {false}) =
      ((specialY n) ⁻¹' {false}) ∩ ((zVariable n p) ⁻¹' {z}) by
    ext ω
    simp [and_comm]]
  rw [disjointSpecialYFalseMeasure_cond_zVariable_eq_cond_inter]
  rw [← volume_cond_eq_disjointCondMeasure_cond_of_subset_disjointEvent n
    (by
      intro ω hω
      exact mem_disjointEvent_of_specialY_eq_false n (by simpa using hω.1))]

open Classical in
/-- A positive `Z=z` fiber under `D ∧ Y_T=false` has positive ambient hard-distribution volume. -/
theorem volume_zFiber_ne_zero_of_disjointSpecialYFalseMeasure_ne_zero
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)))
    (hz : (disjointSpecialYFalseMeasure n).real ((zVariable n p) ⁻¹' {z}) ≠ 0) :
    (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0 := by
  have hac_y : disjointSpecialYFalseMeasure n ≪ disjointCondMeasure n := by
    rw [disjointSpecialYFalseMeasure]
    exact ProbabilityTheory.cond_absolutelyContinuous
  have hac_d : disjointCondMeasure n ≪ (volume : Measure (HardSample n)) := by
    rw [disjointCondMeasure]
    exact ProbabilityTheory.cond_absolutelyContinuous
  have hac : disjointSpecialYFalseMeasure n ≪ (volume : Measure (HardSample n)) :=
    hac_y.trans hac_d
  intro hvol
  have hy_zero :
      (disjointSpecialYFalseMeasure n) ((zVariable n p) ⁻¹' {z}) = 0 :=
    hac hvol
  exact hz (by simp [Measure.real, hy_zero])

open Classical in
/-- A positive `Z=z` fiber under `D ∧ Y_T=false` makes the `Y_T=false` branch of the ambient
`Z=z` fiber positive. -/
theorem zFiberMeasure_specialYFalse_ne_zero_of_disjointSpecialYFalseMeasure_ne_zero
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)))
    (hz : (disjointSpecialYFalseMeasure n).real ((zVariable n p) ⁻¹' {z}) ≠ 0) :
    (zFiberMeasure n p z).real ((specialY n) ⁻¹' {false}) ≠ 0 := by
  let Z : Set (HardSample n) := (zVariable n p) ⁻¹' {z}
  let Y0 : Set (HardSample n) := (specialY n) ⁻¹' {false}
  have hfactor := disjointSpecialYFalseMeasure_measureReal_zVariable n p z
  have hμD_real_ne : (disjointCondMeasure n).real (Y0 ∩ Z) ≠ 0 := by
    intro hzero
    apply hz
    rw [hfactor]
    simp [Y0, Z, hzero]
  have hac_d : disjointCondMeasure n ≪ (volume : Measure (HardSample n)) := by
    rw [disjointCondMeasure]
    exact ProbabilityTheory.cond_absolutelyContinuous
  have hμD_ne : (disjointCondMeasure n) (Y0 ∩ Z) ≠ 0 :=
    (MeasureTheory.measureReal_ne_zero_iff
      (μ := disjointCondMeasure n) (s := Y0 ∩ Z)).mp hμD_real_ne
  have hvol_inter_ne : (volume : Measure (HardSample n)) (Y0 ∩ Z) ≠ 0 := by
    intro hvol
    exact hμD_ne (hac_d hvol)
  have hvol_inter_real_ne : (volume : Measure (HardSample n)).real (Z ∩ Y0) ≠ 0 := by
    rw [Set.inter_comm]
    exact (MeasureTheory.measureReal_ne_zero_iff
      (μ := (volume : Measure (HardSample n))) (s := Y0 ∩ Z)).mpr hvol_inter_ne
  have hzvol :
      (volume : Measure (HardSample n)) Z ≠ 0 :=
    volume_zFiber_ne_zero_of_disjointSpecialYFalseMeasure_ne_zero n p z (by simpa [Z] using hz)
  have hzvol_real : (volume : Measure (HardSample n)).real Z ≠ 0 :=
    (MeasureTheory.measureReal_ne_zero_iff
      (μ := (volume : Measure (HardSample n))) (s := Z)).mpr hzvol
  rw [zFiberMeasure]
  rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  change
    ((volume : Measure (HardSample n)).real Z)⁻¹ *
      (volume : Measure (HardSample n)).real (Z ∩ Y0) ≠ 0
  exact mul_ne_zero (inv_ne_zero hzvol_real) hvol_inter_real_ne

/-- The conditional law of the special bit-pair on a positive-mass `Z=z` fiber. -/
noncomputable def conditionalSpecialPairLaw
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)))
    (hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0) :
    ProbabilityMeasure (Bool × Bool) :=
  ProbabilityMeasure.map
    (⟨zFiberMeasure n p z, zFiberMeasure_isProbabilityMeasure n p z hz⟩ :
      ProbabilityMeasure (HardSample n))
    (Measurable.of_discrete.aemeasurable (f := specialPair n))

/-- On a positive-mass `Z=z` fiber, the conditional `specialPair` singleton mass is the
corresponding preimage probability under the fiber measure. -/
theorem conditionalSpecialPairLaw_singleton
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)))
    (hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0)
    (b : Bool × Bool) :
    ((conditionalSpecialPairLaw n p z hz : ProbabilityMeasure (Bool × Bool)) :
        Measure (Bool × Bool)).real {b} =
      (zFiberMeasure n p z).real ((specialPair n) ⁻¹' {b}) := by
  rw [conditionalSpecialPairLaw]
  rw [Measure.real]
  rw [ProbabilityMeasure.map_apply' _ _ MeasurableSet.of_discrete]
  rfl

/-- The conditional law of Alice's special bit on a positive-mass `Z=z` fiber. -/
noncomputable def conditionalSpecialXLaw
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)))
    (hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0) :
    ProbabilityMeasure Bool :=
  ProbabilityMeasure.map
    (⟨zFiberMeasure n p z, zFiberMeasure_isProbabilityMeasure n p z hz⟩ :
      ProbabilityMeasure (HardSample n))
    (Measurable.of_discrete.aemeasurable (f := specialX n))

/-- The conditional law of Bob's special bit on a positive-mass `Z=z` fiber. -/
noncomputable def conditionalSpecialYLaw
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)))
    (hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0) :
    ProbabilityMeasure Bool :=
  ProbabilityMeasure.map
    (⟨zFiberMeasure n p z, zFiberMeasure_isProbabilityMeasure n p z hz⟩ :
      ProbabilityMeasure (HardSample n))
    (Measurable.of_discrete.aemeasurable (f := specialY n))

/-- On a positive-mass `Z=z` fiber, Alice's conditional special-bit singleton mass is the
corresponding preimage probability under the fiber measure. -/
theorem conditionalSpecialXLaw_singleton
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)))
    (hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0)
    (b : Bool) :
    ((conditionalSpecialXLaw n p z hz : ProbabilityMeasure Bool) : Measure Bool).real {b} =
      (zFiberMeasure n p z).real ((specialX n) ⁻¹' {b}) := by
  rw [conditionalSpecialXLaw]
  rw [Measure.real]
  rw [ProbabilityMeasure.map_apply' _ _ MeasurableSet.of_discrete]
  rfl

/-- On a positive-mass `Z=z` fiber, Bob's conditional special-bit singleton mass is the
corresponding preimage probability under the fiber measure. -/
theorem conditionalSpecialYLaw_singleton
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)))
    (hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0)
    (b : Bool) :
    ((conditionalSpecialYLaw n p z hz : ProbabilityMeasure Bool) : Measure Bool).real {b} =
      (zFiberMeasure n p z).real ((specialY n) ⁻¹' {b}) := by
  rw [conditionalSpecialYLaw]
  rw [Measure.real]
  rw [ProbabilityMeasure.map_apply' _ _ MeasurableSet.of_discrete]
  rfl

open Classical in
/-- The TV distance between the conditional special-pair law on a `Z=z` fiber and the uniform
bit-pair law, set to `0` on zero-mass fibers. -/
noncomputable def zDistance
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))) : ℝ :=
  if hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0 then
    tvDistance (conditionalSpecialPairLaw n p z hz) uniformBoolPair
  else
    0

open Classical in
/-- The TV distance between Alice's conditional special-bit law and a uniform bit, set to `0` on
zero-mass fibers. -/
noncomputable def xDistance
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))) : ℝ :=
  if hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0 then
    tvDistance (conditionalSpecialXLaw n p z hz) uniformBool
  else
    0

open Classical in
/-- The TV distance between Bob's conditional special-bit law and a uniform bit, set to `0` on
zero-mass fibers. -/
noncomputable def yDistance
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))) : ℝ :=
  if hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0 then
    tvDistance (conditionalSpecialYLaw n p z hz) uniformBool
  else
    0

open Classical in
/-- The conditional pair TV distance is nonnegative, including the zero-mass fallback case. -/
theorem zDistance_nonneg
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))) :
    0 ≤ zDistance n p z := by
  by_cases hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0
  · simp [zDistance, hz, TVDistance.tvDistance_nonneg]
  · simp [zDistance, hz]

open Classical in
/-- Alice's one-bit conditional TV distance is nonnegative, including the zero-mass fallback
case. -/
theorem xDistance_nonneg
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))) :
    0 ≤ xDistance n p z := by
  by_cases hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0
  · simp [xDistance, hz, TVDistance.tvDistance_nonneg]
  · simp [xDistance, hz]

open Classical in
/-- Bob's one-bit conditional TV distance is nonnegative, including the zero-mass fallback case. -/
theorem yDistance_nonneg
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))) :
    0 ≤ yDistance n p z := by
  by_cases hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0
  · simp [yDistance, hz, TVDistance.tvDistance_nonneg]
  · simp [yDistance, hz]

/-- Pulling a dual `Z` fiber intersected with a dual Alice-special-bit event back along
hard-sample duality gives the corresponding original Bob-special-bit event. -/
theorem dualHardSample_preimage_zVariable_dualZValue_inter_specialX
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))) (b : Bool) :
    (dualHardSample n) ⁻¹'
        (((zVariable n (dualProtocol n p)) ⁻¹' {dualZValue n p z}) ∩
          ((specialX n) ⁻¹' {b})) =
      ((zVariable n p) ⁻¹' {z}) ∩ ((specialY n) ⁻¹' {b}) := by
  ext ω
  change
    zVariable n (dualProtocol n p) (dualHardSample n ω) = dualZValue n p z ∧
        specialX n (dualHardSample n ω) = b ↔
      zVariable n p ω = z ∧ specialY n ω = b
  rw [zVariable_dualProtocol_dualHardSample, specialX_dualHardSample]
  exact and_congr ((dualZValue_injective n p).eq_iff) Iff.rfl

/-- The ambient hard-sample measure gives corresponding original and dual one-bit `Z`-fiber
events the same mass. -/
theorem volume_zVariable_dualProtocol_dualZValue_inter_specialX
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))) (b : Bool) :
    (volume : Measure (HardSample n))
        (((zVariable n (dualProtocol n p)) ⁻¹' {dualZValue n p z}) ∩
          ((specialX n) ⁻¹' {b})) =
      (volume : Measure (HardSample n))
        (((zVariable n p) ⁻¹' {z}) ∩ ((specialY n) ⁻¹' {b})) := by
  let μ : Measure (HardSample n) := volume
  let S : Set (HardSample n) :=
    ((zVariable n (dualProtocol n p)) ⁻¹' {dualZValue n p z}) ∩
      ((specialX n) ⁻¹' {b})
  have hpre :
      μ ((dualHardSample n) ⁻¹' S) = μ S :=
    Measure.measure_preimage_of_map_eq_self
      (volume_measurePreserving_dualHardSample n).map_eq
      MeasurableSet.of_discrete.nullMeasurableSet
  rw [← hpre]
  exact congrArg (fun S : Set (HardSample n) => μ S)
    (dualHardSample_preimage_zVariable_dualZValue_inter_specialX n p z b)

/-- Real-valued version of
`volume_zVariable_dualProtocol_dualZValue_inter_specialX`. -/
theorem volume_measureReal_zVariable_dualProtocol_dualZValue_inter_specialX
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))) (b : Bool) :
    (volume : Measure (HardSample n)).real
        (((zVariable n (dualProtocol n p)) ⁻¹' {dualZValue n p z}) ∩
          ((specialX n) ⁻¹' {b})) =
      (volume : Measure (HardSample n)).real
        (((zVariable n p) ⁻¹' {z}) ∩ ((specialY n) ⁻¹' {b})) := by
  repeat rw [Measure.real]
  rw [volume_zVariable_dualProtocol_dualZValue_inter_specialX]

open Classical in
/-- The Alice one-bit law on the dual protocol's recoded `Z` fiber is Bob's one-bit law on the
original `Z` fiber. -/
theorem conditionalSpecialXLaw_dualProtocol_dualZValue
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)))
    (hzDual :
      (volume : Measure (HardSample n))
          ((zVariable n (dualProtocol n p)) ⁻¹' {dualZValue n p z}) ≠ 0)
    (hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0) :
    conditionalSpecialXLaw n (dualProtocol n p) (dualZValue n p z) hzDual =
      conditionalSpecialYLaw n p z hz := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro b
  rw [conditionalSpecialXLaw_singleton, conditionalSpecialYLaw_singleton]
  rw [zFiberMeasure_real_apply, zFiberMeasure_real_apply]
  rw [volume_measureReal_zVariable_dualProtocol_dualZValue]
  rw [volume_measureReal_zVariable_dualProtocol_dualZValue_inter_specialX]

open Classical in
/-- The Alice one-bit distance for the dual protocol at the recoded `Z` value is the original
Bob one-bit distance. -/
theorem xDistance_dualProtocol_dualZValue_eq_yDistance
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))) :
    xDistance n (dualProtocol n p) (dualZValue n p z) = yDistance n p z := by
  by_cases hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0
  · have hzDual :
        (volume : Measure (HardSample n))
            ((zVariable n (dualProtocol n p)) ⁻¹' {dualZValue n p z}) ≠ 0 := by
      rwa [volume_zVariable_dualProtocol_dualZValue n p z]
    rw [xDistance, yDistance, dif_pos hzDual, dif_pos hz]
    rw [conditionalSpecialXLaw_dualProtocol_dualZValue n p z hzDual hz]
  · have hzDual :
        ¬(volume : Measure (HardSample n))
            ((zVariable n (dualProtocol n p)) ⁻¹' {dualZValue n p z}) ≠ 0 := by
      rwa [volume_zVariable_dualProtocol_dualZValue n p z]
    rw [xDistance, yDistance, dif_neg hzDual, dif_neg hz]

open Classical in
/-- The dual Alice bad event on the `X_T=Y_T=false` slice is the original Bob bad event. -/
theorem volume_specialZeroZero_inter_xDistance_dualProtocol_eq_yDistance
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (γ : ℝ) :
    (volume : Measure (HardSample n)).real
        (specialZeroZero n ∩
          {ω | γ < xDistance n (dualProtocol n p) (zVariable n (dualProtocol n p) ω)}) =
      (volume : Measure (HardSample n)).real
        (specialZeroZero n ∩ {ω | γ < yDistance n p (zVariable n p ω)}) := by
  let μ : Measure (HardSample n) := volume
  let Sdual : Set (HardSample n) :=
    specialZeroZero n ∩
      {ω | γ < xDistance n (dualProtocol n p) (zVariable n (dualProtocol n p) ω)}
  let S : Set (HardSample n) :=
    specialZeroZero n ∩ {ω | γ < yDistance n p (zVariable n p ω)}
  have hpre : (dualHardSample n) ⁻¹' Sdual = S := by
    ext ω
    change
      dualHardSample n ω ∈ specialZeroZero n ∧
          γ < xDistance n (dualProtocol n p)
            (zVariable n (dualProtocol n p) (dualHardSample n ω)) ↔
        ω ∈ specialZeroZero n ∧ γ < yDistance n p (zVariable n p ω)
    rw [specialZeroZero_dualHardSample, zVariable_dualProtocol_dualHardSample,
      xDistance_dualProtocol_dualZValue_eq_yDistance]
  have hmeasure : μ S = μ Sdual := by
    have hpre_measure :
        μ ((dualHardSample n) ⁻¹' Sdual) = μ Sdual :=
      Measure.measure_preimage_of_map_eq_self
        (volume_measurePreserving_dualHardSample n).map_eq
        MeasurableSet.of_discrete.nullMeasurableSet
    simpa [hpre] using hpre_measure
  repeat rw [Measure.real]
  rw [hmeasure]

open Classical in
/-- Pinsker for Alice's one-bit fiber distance against the uniform bit. -/
theorem two_mul_xDistance_sq_le_toReal_klDiv_uniformBool
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))}
    (hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0) :
    2 * xDistance n p z ^ 2 ≤
      (InformationTheory.klDiv
        ((conditionalSpecialXLaw n p z hz : ProbabilityMeasure Bool) : Measure Bool)
        ((uniformBool : ProbabilityMeasure Bool) : Measure Bool)).toReal := by
  rw [xDistance, dif_pos hz]
  exact two_mul_tvDistance_sq_le_toReal_klDiv
    (conditionalSpecialXLaw n p z hz) uniformBool
    (FiniteMeasureSpace.probabilityMeasure_klDiv_ne_top_of_forall_toPMF_ne_zero
      (conditionalSpecialXLaw n p z hz) uniformBool uniformBool_toPMF_ne_zero)

open Classical in
/-- Alice's one-bit fiber KL cost on a `Z=z` fiber, set to `0` on zero-mass fibers. -/
noncomputable def xFiberKL
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))) : ℝ :=
  if hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0 then
    (InformationTheory.klDiv
      ((conditionalSpecialXLaw n p z hz : ProbabilityMeasure Bool) : Measure Bool)
      ((uniformBool : ProbabilityMeasure Bool) : Measure Bool)).toReal
  else
    0

open Classical in
/-- Alice's one-bit fiber KL cost is nonnegative, including the zero-mass fallback case. -/
theorem xFiberKL_nonneg
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))) :
    0 ≤ xFiberKL n p z := by
  by_cases hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0
  · simp [xFiberKL, hz]
  · simp [xFiberKL, hz]

open Classical in
/-- Pointwise Pinsker for Alice, with zero-mass `Z` fibers handled by `xFiberKL`. -/
theorem two_mul_xDistance_sq_le_xFiberKL
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))) :
    2 * xDistance n p z ^ 2 ≤ xFiberKL n p z := by
  by_cases hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0
  · simpa [xFiberKL, hz] using two_mul_xDistance_sq_le_toReal_klDiv_uniformBool n p hz
  · simp [xFiberKL, xDistance, hz]

open Classical in
/-- Integrated Alice Pinsker bound over the `D ∧ Y_T=false` conditioned measure. -/
theorem two_mul_integral_xDistance_sq_le_integral_xFiberKL_disjointSpecialYFalse
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    2 * (∫ ω, (xDistance n p (zVariable n p ω)) ^ 2
        ∂(disjointSpecialYFalseMeasure n)) ≤
      ∫ ω, xFiberKL n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n) := by
  let μ : Measure (HardSample n) := disjointSpecialYFalseMeasure n
  haveI : IsProbabilityMeasure μ := by
    simpa [μ] using disjointSpecialYFalseMeasure_isProbabilityMeasure n
  have hpoint :
      ∀ ω : HardSample n,
        2 * (xDistance n p (zVariable n p ω)) ^ 2 ≤
          xFiberKL n p (zVariable n p ω) := by
    intro ω
    exact two_mul_xDistance_sq_le_xFiberKL n p (zVariable n p ω)
  have h := integral_mono (μ := μ) Integrable.of_finite Integrable.of_finite hpoint
  simpa [μ, integral_const_mul] using h

open Classical in
/-- Jensen's inequality converts a squared Alice-side average-distance estimate under
`D ∧ Y_T=false` into the average-distance estimate used before Markov. -/
theorem disjointSpecialYFalseMeasure_integral_xDistance_le_of_integral_sq_le
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {γ : ℝ}
    (hsq :
      ∫ ω, (xDistance n p (zVariable n p ω)) ^ 2 ∂(disjointSpecialYFalseMeasure n) ≤
        γ ^ 4) :
    ∫ ω, xDistance n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n) ≤
      γ ^ 2 := by
  let μ : ProbabilityMeasure (HardSample n) :=
    ⟨disjointSpecialYFalseMeasure n, disjointSpecialYFalseMeasure_isProbabilityMeasure n⟩
  let f : HardSample n → ℝ := fun ω => xDistance n p (zVariable n p ω)
  have hjensen :
      (∫ ω, f ω ∂(μ : Measure (HardSample n))) ^ 2 ≤
        ∫ ω, (f ω) ^ 2 ∂(μ : Measure (HardSample n)) :=
    FiniteMeasureSpace.probabilityMeasure_sq_integral_le_integral_sq μ f
  have hsq_bound :
      (∫ ω, f ω ∂(μ : Measure (HardSample n))) ^ 2 ≤ (γ ^ 2) ^ 2 := by
    calc
      (∫ ω, f ω ∂(μ : Measure (HardSample n))) ^ 2
          ≤ ∫ ω, (f ω) ^ 2 ∂(μ : Measure (HardSample n)) := hjensen
      _ ≤ γ ^ 4 := by simpa [μ, f] using hsq
      _ = (γ ^ 2) ^ 2 := by ring
  have hint_nonneg :
      0 ≤ ∫ ω, f ω ∂(μ : Measure (HardSample n)) :=
    integral_nonneg fun ω => xDistance_nonneg n p (zVariable n p ω)
  have hγ_sq_nonneg : 0 ≤ γ ^ 2 := sq_nonneg γ
  exact (sq_le_sq₀ hint_nonneg hγ_sq_nonneg).mp hsq_bound

open Classical in
/-- Markov's inequality converts the textbook Alice-side average-distance estimate under
`D ∧ Y_T=false` into a bad-`Z` probability bound. -/
theorem disjointSpecialYFalseMeasure_xDistance_bad_le_of_integral_le
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {γ : ℝ}
    (hγ : 0 < γ)
    (havg :
      ∫ ω, xDistance n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n) ≤ γ ^ 2) :
    (disjointSpecialYFalseMeasure n).real
      {ω | γ < xDistance n p (zVariable n p ω)} ≤ γ := by
  let μ : Measure (HardSample n) := disjointSpecialYFalseMeasure n
  let f : HardSample n → ℝ := fun ω => xDistance n p (zVariable n p ω)
  haveI : IsProbabilityMeasure μ := by
    simpa [μ] using disjointSpecialYFalseMeasure_isProbabilityMeasure n
  have hmarkov :
      γ * μ.real {ω : HardSample n | γ ≤ f ω} ≤ ∫ ω, f ω ∂μ :=
    mul_meas_ge_le_integral_of_nonneg
      (μ := μ) (f := f)
      (ae_of_all _ fun ω => xDistance_nonneg n p (zVariable n p ω))
      Integrable.of_finite γ
  have hbad_le :
      μ.real {ω : HardSample n | γ < f ω} ≤ μ.real {ω : HardSample n | γ ≤ f ω} :=
    measureReal_mono (by
      intro ω hω
      exact le_of_lt (by simpa using hω))
  have hge_le : μ.real {ω : HardSample n | γ ≤ f ω} ≤ γ := by
    have hge_mul :
        μ.real {ω : HardSample n | γ ≤ f ω} * γ ≤ γ ^ 2 := by
      calc
        μ.real {ω : HardSample n | γ ≤ f ω} * γ ≤ ∫ ω, f ω ∂μ := by
          simpa [mul_comm] using hmarkov
        _ ≤ γ ^ 2 := havg
    have hge_nonneg :
        0 ≤ μ.real {ω : HardSample n | γ ≤ f ω} :=
      measureReal_nonneg
    nlinarith
  exact hbad_le.trans hge_le

/-- A `Z` value is good when the conditional special-pair law on its fiber is within `2γ` of
uniform; zero-mass fibers use the `zDistance = 0` fallback. -/
def goodZ
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (γ : ℝ)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))) : Prop :=
  zDistance n p z ≤ 2 * γ

/-- The good-fiber event `𝓖` in Claim 6.21, pulled back to the hard sample space through `Z`. -/
def goodZEvent
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) (γ : ℝ) :
    Set (HardSample n) :=
  {ω | goodZ n p γ (zVariable n p ω)}

/-- The generated input belongs to the transcript leaf of any deterministic protocol. -/
theorem input_mem_transcript
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) (ω : HardSample n) :
    input n ω ∈
      (message n p ω : Set (Set (Fin n) × Set (Fin n))) :=
  Deterministic.Protocol.mem_transcript p (input n ω)

/-- If a sample has `Z=z`, its generated input lies in the transcript leaf `z.1`. -/
theorem input_mem_leaf_of_zVariable_eq
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))}
    {ω : HardSample n}
    (hω : zVariable n p ω = z) :
    input n ω ∈ (z.1 : Set (Set (Fin n) × Set (Fin n))) := by
  have hmsg : message n p ω = z.1 := by
    simpa [zVariable, message] using congrArg Prod.fst hω
  simpa [hmsg] using input_mem_transcript n p ω

/-- Equal `Z` value fixes the special coordinate. -/
theorem specialCoordinate_eq_of_zVariable_eq
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))}
    {ω : HardSample n}
    (hω : zVariable n p ω = z) :
    specialCoordinate n ω = z.2.1 := by
  simpa [zVariable] using congrArg (fun z => z.2.1) hω

/-- Equal `Z` value fixes Alice's bits before the special coordinate. -/
theorem xBeforeSpecial_eq_of_zVariable_eq
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))}
    {ω : HardSample n}
    (hω : zVariable n p ω = z) :
    xBeforeSpecial n ω = z.2.2.1 := by
  simpa [zVariable] using congrArg (fun z => z.2.2.1) hω

/-- Equal `Z` value fixes Bob's bits after the special coordinate. -/
theorem yAfterSpecial_eq_of_zVariable_eq
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))}
    {ω : HardSample n}
    (hω : zVariable n p ω = z) :
    yAfterSpecial n ω = z.2.2.2 := by
  simpa [zVariable] using congrArg (fun z => z.2.2.2) hω

/-- The transcript leaf component of `Z` is a rectangle: two samples in the same `Z` fiber also
contain the two mixed input pairs in that leaf. -/
theorem mixed_inputs_mem_leaf_of_zVariable_eq
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))}
    {ω ω' : HardSample n}
    (hω : zVariable n p ω = z)
    (hω' : zVariable n p ω' = z) :
    (X n ω', Y n ω) ∈ (z.1 : Set (Set (Fin n) × Set (Fin n))) ∧
      (X n ω, Y n ω') ∈ (z.1 : Set (Set (Fin n) × Set (Fin n))) := by
  have hrect :
      Rectangle.IsRectangle (z.1 : Set (Set (Fin n) × Set (Fin n))) :=
    Deterministic.Protocol.leafRectangles_isRectangle p (z.1 : Set (Set (Fin n) × Set (Fin n)))
      z.1.2
  have hωmem : (X n ω, Y n ω) ∈ (z.1 : Set (Set (Fin n) × Set (Fin n))) := by
    simpa [input] using input_mem_leaf_of_zVariable_eq n p hω
  have hω'mem : (X n ω', Y n ω') ∈ (z.1 : Set (Set (Fin n) × Set (Fin n))) := by
    simpa [input] using input_mem_leaf_of_zVariable_eq n p hω'
  exact (Rectangle.IsRectangle_iff _).mp hrect (X n ω) (X n ω') (Y n ω) (Y n ω')
    hωmem hω'mem

/-- Two samples in the same `Z` fiber have the same special coordinate. -/
theorem specialCoordinate_eq_of_same_zVariable
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))}
    {ω ω' : HardSample n}
    (hω : zVariable n p ω = z)
    (hω' : zVariable n p ω' = z) :
    ω.T = ω'.T := by
  have hTω := specialCoordinate_eq_of_zVariable_eq n p hω
  have hTω' := specialCoordinate_eq_of_zVariable_eq n p hω'
  simpa [specialCoordinate] using hTω.trans hTω'.symm

/-- Two samples in the same `Z` fiber have the same `X_<T` conditioning data. -/
theorem xBeforeSpecial_eq_of_same_zVariable
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))}
    {ω ω' : HardSample n}
    (hω : zVariable n p ω = z)
    (hω' : zVariable n p ω' = z) :
    xBeforeSpecial n ω = xBeforeSpecial n ω' := by
  have hωx := xBeforeSpecial_eq_of_zVariable_eq n p hω
  have hω'x := xBeforeSpecial_eq_of_zVariable_eq n p hω'
  exact hωx.trans hω'x.symm

/-- Two samples in the same `Z` fiber have the same `Y_>T` conditioning data. -/
theorem yAfterSpecial_eq_of_same_zVariable
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))}
    {ω ω' : HardSample n}
    (hω : zVariable n p ω = z)
    (hω' : zVariable n p ω' = z) :
    yAfterSpecial n ω = yAfterSpecial n ω' := by
  have hωy := yAfterSpecial_eq_of_zVariable_eq n p hω
  have hω'y := yAfterSpecial_eq_of_zVariable_eq n p hω'
  exact hωy.trans hω'y.symm

/-- The mixed sample of two samples in the same `Z` fiber remains in that `Z` fiber. -/
theorem zVariable_mix_eq_of_same_zVariable
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))}
    {ωX ωY : HardSample n}
    (hωX : zVariable n p ωX = z)
    (hωY : zVariable n p ωY = z) :
    zVariable n p (mix n ωX ωY) = z := by
  have hT := specialCoordinate_eq_of_same_zVariable n p hωX hωY
  have hBefore := xBeforeSpecial_eq_of_same_zVariable n p hωX hωY
  have hAfter := yAfterSpecial_eq_of_same_zVariable n p hωX hωY
  have hinput := input_mix n hT hBefore hAfter
  have hleaf :
      input n (mix n ωX ωY) ∈
        (z.1 : Set (Set (Fin n) × Set (Fin n))) := by
    have hmixed := mixed_inputs_mem_leaf_of_zVariable_eq n p hωX hωY
    simpa [hinput] using hmixed.2
  have htranscript : p.transcript (input n (mix n ωX ωY)) = z.1 :=
    Deterministic.Protocol.transcript_eq_of_mem_leaf p z.1 hleaf
  have hTz : specialCoordinate n (mix n ωX ωY) = z.2.1 := by
    have hTωX := specialCoordinate_eq_of_zVariable_eq n p hωX
    simpa [specialCoordinate, mix] using hTωX
  have hBeforeZ : xBeforeSpecial n (mix n ωX ωY) = z.2.2.1 := by
    rw [xBeforeSpecial_mix n hT hBefore hAfter]
    exact xBeforeSpecial_eq_of_zVariable_eq n p hωX
  have hAfterZ : yAfterSpecial n (mix n ωX ωY) = z.2.2.2 := by
    rw [yAfterSpecial_mix n hT hBefore hAfter]
    exact yAfterSpecial_eq_of_zVariable_eq n p hωY
  ext <;> simp [zVariable, coarseConditioning, htranscript, hTz, hBeforeZ, hAfterZ]

/-- If two samples are in a `Z=z` fiber, and the first has Alice special bit `bX` while the
second has Bob special bit `bY`, then their mix is in the same fiber with special pair
`(bX, bY)`. -/
theorem mix_mem_fiber_inter_specialPair_of_mem_specialX_specialY
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))}
    {ωX ωY : HardSample n} {bX bY : Bool}
    (hωX : ωX ∈ ((zVariable n p) ⁻¹' {z}) ∩ ((specialX n) ⁻¹' {bX}))
    (hωY : ωY ∈ ((zVariable n p) ⁻¹' {z}) ∩ ((specialY n) ⁻¹' {bY})) :
    mix n ωX ωY ∈ ((zVariable n p) ⁻¹' {z}) ∩ ((specialPair n) ⁻¹' {(bX, bY)}) := by
  have hZX : zVariable n p ωX = z := by simpa using hωX.1
  have hZY : zVariable n p ωY = z := by simpa using hωY.1
  refine ⟨?_, ?_⟩
  · simpa using zVariable_mix_eq_of_same_zVariable n p hZX hZY
  · have hX : specialX n ωX = bX := by simpa using hωX.2
    have hY : specialY n ωY = bY := by simpa using hωY.2
    simp [specialPair, specialX_mix, specialY_mix, hX, hY]

/-- The swapped mix of two samples in a `Z=z` fiber remains in that fiber. -/
theorem mix_swap_mem_fiber_of_mem_specialX_specialY
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))}
    {ωX ωY : HardSample n} {bX bY : Bool}
    (hωX : ωX ∈ ((zVariable n p) ⁻¹' {z}) ∩ ((specialX n) ⁻¹' {bX}))
    (hωY : ωY ∈ ((zVariable n p) ⁻¹' {z}) ∩ ((specialY n) ⁻¹' {bY})) :
    mix n ωY ωX ∈ (zVariable n p) ⁻¹' {z} := by
  have hZX : zVariable n p ωX = z := by simpa using hωX.1
  have hZY : zVariable n p ωY = z := by simpa using hωY.1
  simpa using zVariable_mix_eq_of_same_zVariable n p hZY hZX

/-- If one sample in a fiber has special pair `b` and the other is just in the fiber, mixing with
the special-pair sample on Alice's side lands in the fiber with Alice special bit `b.1`. -/
theorem mix_mem_fiber_inter_specialX_of_mem_specialPair_fiber
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))}
    {ωPair ω : HardSample n} {b : Bool × Bool}
    (hωPair : ωPair ∈ ((zVariable n p) ⁻¹' {z}) ∩ ((specialPair n) ⁻¹' {b}))
    (hω : ω ∈ (zVariable n p) ⁻¹' {z}) :
    mix n ωPair ω ∈ ((zVariable n p) ⁻¹' {z}) ∩ ((specialX n) ⁻¹' {b.1}) := by
  have hZPair : zVariable n p ωPair = z := by simpa using hωPair.1
  have hZω : zVariable n p ω = z := by simpa using hω
  have hpair : specialPair n ωPair = b := by simpa using hωPair.2
  refine ⟨?_, ?_⟩
  · simpa using zVariable_mix_eq_of_same_zVariable n p hZPair hZω
  · have hX : specialX n ωPair = b.1 := by
      simpa [specialPair] using congrArg Prod.fst hpair
    simp [specialX_mix, hX]

/-- If one sample in a fiber has special pair `b` and the other is just in the fiber, mixing with
the special-pair sample on Bob's side lands in the fiber with Bob special bit `b.2`. -/
theorem mix_mem_fiber_inter_specialY_of_mem_fiber_specialPair
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))}
    {ωPair ω : HardSample n} {b : Bool × Bool}
    (hω : ω ∈ (zVariable n p) ⁻¹' {z})
    (hωPair : ωPair ∈ ((zVariable n p) ⁻¹' {z}) ∩ ((specialPair n) ⁻¹' {b})) :
    mix n ω ωPair ∈ ((zVariable n p) ⁻¹' {z}) ∩ ((specialY n) ⁻¹' {b.2}) := by
  have hZω : zVariable n p ω = z := by simpa using hω
  have hZPair : zVariable n p ωPair = z := by simpa using hωPair.1
  have hpair : specialPair n ωPair = b := by simpa using hωPair.2
  refine ⟨?_, ?_⟩
  · simpa using zVariable_mix_eq_of_same_zVariable n p hZω hZPair
  · have hY : specialY n ωPair = b.2 := by
      simpa [specialPair] using congrArg Prod.snd hpair
    simp [specialY_mix, hY]

open Classical in
/-- The switching map `(ωX, ωY) ↦ (mix ωX ωY, mix ωY ωX)` gives the cardinal identity
underlying conditional independence of `specialX` and `specialY` on a `Z=z` fiber. -/
theorem card_fiber_inter_specialX_mul_card_fiber_inter_specialY
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)))
    (b : Bool × Bool) :
    Fintype.card {ω : HardSample n //
        ω ∈ ((zVariable n p) ⁻¹' {z}) ∩ ((specialX n) ⁻¹' {b.1})} *
      Fintype.card {ω : HardSample n //
        ω ∈ ((zVariable n p) ⁻¹' {z}) ∩ ((specialY n) ⁻¹' {b.2})} =
    Fintype.card {ω : HardSample n //
        ω ∈ ((zVariable n p) ⁻¹' {z}) ∩ ((specialPair n) ⁻¹' {b})} *
      Fintype.card {ω : HardSample n // ω ∈ (zVariable n p) ⁻¹' {z}} := by
  let A := {ω : HardSample n //
    ω ∈ ((zVariable n p) ⁻¹' {z}) ∩ ((specialX n) ⁻¹' {b.1})}
  let B := {ω : HardSample n //
    ω ∈ ((zVariable n p) ⁻¹' {z}) ∩ ((specialY n) ⁻¹' {b.2})}
  let C := {ω : HardSample n //
    ω ∈ ((zVariable n p) ⁻¹' {z}) ∩ ((specialPair n) ⁻¹' {b})}
  let D := {ω : HardSample n // ω ∈ (zVariable n p) ⁻¹' {z}}
  have hcard : Fintype.card (A × B) = Fintype.card (C × D) := by
    refine Fintype.card_congr
      { toFun := ?toFun
        invFun := ?invFun
        left_inv := ?left_inv
        right_inv := ?right_inv }
    · intro ab
      refine
        (⟨mix n ab.1.1 ab.2.1,
            mix_mem_fiber_inter_specialPair_of_mem_specialX_specialY n p ab.1.2 ab.2.2⟩,
          ⟨mix n ab.2.1 ab.1.1,
            mix_swap_mem_fiber_of_mem_specialX_specialY n p ab.1.2 ab.2.2⟩)
    · intro cd
      refine
        (⟨mix n cd.1.1 cd.2.1,
            mix_mem_fiber_inter_specialX_of_mem_specialPair_fiber n p cd.1.2 cd.2.2⟩,
          ⟨mix n cd.2.1 cd.1.1,
            mix_mem_fiber_inter_specialY_of_mem_fiber_specialPair n p cd.2.2 cd.1.2⟩)
    · intro ab
      apply Prod.ext
      · apply Subtype.ext
        have hZA : zVariable n p ab.1.1 = z := by simpa using ab.1.2.1
        have hZB : zVariable n p ab.2.1 = z := by simpa using ab.2.2.1
        exact mix_mix_swap n
          (specialCoordinate_eq_of_same_zVariable n p hZA hZB)
          (xBeforeSpecial_eq_of_same_zVariable n p hZA hZB)
          (yAfterSpecial_eq_of_same_zVariable n p hZA hZB)
      · apply Subtype.ext
        have hZA : zVariable n p ab.1.1 = z := by simpa using ab.1.2.1
        have hZB : zVariable n p ab.2.1 = z := by simpa using ab.2.2.1
        exact mix_mix_swap n
          (specialCoordinate_eq_of_same_zVariable n p hZB hZA)
          (xBeforeSpecial_eq_of_same_zVariable n p hZB hZA)
          (yAfterSpecial_eq_of_same_zVariable n p hZB hZA)
    · intro cd
      apply Prod.ext
      · apply Subtype.ext
        have hZC : zVariable n p cd.1.1 = z := by simpa using cd.1.2.1
        have hZD : zVariable n p cd.2.1 = z := cd.2.2
        exact mix_mix_swap n
          (specialCoordinate_eq_of_same_zVariable n p hZC hZD)
          (xBeforeSpecial_eq_of_same_zVariable n p hZC hZD)
          (yAfterSpecial_eq_of_same_zVariable n p hZC hZD)
      · apply Subtype.ext
        have hZC : zVariable n p cd.1.1 = z := by simpa using cd.1.2.1
        have hZD : zVariable n p cd.2.1 = z := cd.2.2
        exact mix_mix_swap n
          (specialCoordinate_eq_of_same_zVariable n p hZD hZC)
          (xBeforeSpecial_eq_of_same_zVariable n p hZD hZC)
          (yAfterSpecial_eq_of_same_zVariable n p hZD hZC)
  simpa [A, B, C, D, Fintype.card_prod] using hcard

open Classical in
/-- Under the uniform hard-distribution measure, real measure is cardinality divided by the size
of the sample space. -/
theorem measureReal_eq_card_subtype_div (S : Set (HardSample n)) :
    (volume : Measure (HardSample n)).real S =
      (Fintype.card {ω : HardSample n // ω ∈ S} : ℝ) /
        Fintype.card (HardSample n) := by
  change ((ProbabilityTheory.uniformOn Set.univ : Measure (HardSample n)) S).toReal = _
  rw [uniformOn_univ_measureReal_eq_card_filter]
  congr 1
  exact_mod_cast (by simp [Fintype.card_subtype])

set_option maxHeartbeats 800000 in
-- The statement contains several dependent subtype cardinalities over protocol leaves; elaborating
-- the local set abbreviations and the final `convert` needs more than the default budget.
open Classical in
/-- The rectangle switching identity, translated from cardinalities to the uniform
hard-distribution measure. -/
theorem fiber_volume_factorization
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)))
    (b : Bool × Bool) :
    (volume : Measure (HardSample n)).real ((zVariable n p) ⁻¹' {z}) *
        (volume : Measure (HardSample n)).real
          (((zVariable n p) ⁻¹' {z}) ∩ ((specialPair n) ⁻¹' {b})) =
      (volume : Measure (HardSample n)).real
          (((zVariable n p) ⁻¹' {z}) ∩ ((specialX n) ⁻¹' {b.1})) *
        (volume : Measure (HardSample n)).real
          (((zVariable n p) ⁻¹' {z}) ∩ ((specialY n) ⁻¹' {b.2})) := by
  let F : Set (HardSample n) := (zVariable n p) ⁻¹' {z}
  let P : Set (HardSample n) := F ∩ ((specialPair n) ⁻¹' {b})
  let X : Set (HardSample n) := F ∩ ((specialX n) ⁻¹' {b.1})
  let Y : Set (HardSample n) := F ∩ ((specialY n) ⁻¹' {b.2})
  change
    (volume : Measure (HardSample n)).real F * (volume : Measure (HardSample n)).real P =
      (volume : Measure (HardSample n)).real X * (volume : Measure (HardSample n)).real Y
  rw [measureReal_eq_card_subtype_div n F, measureReal_eq_card_subtype_div n P,
    measureReal_eq_card_subtype_div n X, measureReal_eq_card_subtype_div n Y]
  have hcard := card_fiber_inter_specialX_mul_card_fiber_inter_specialY n p z b
  have hcard_real :
      (Fintype.card {ω : HardSample n // ω ∈ X} : ℝ) *
        (Fintype.card {ω : HardSample n // ω ∈ Y} : ℝ) =
      (Fintype.card {ω : HardSample n // ω ∈ P} : ℝ) *
        (Fintype.card {ω : HardSample n // ω ∈ F} : ℝ) := by
    dsimp only [F, P, X, Y]
    exact_mod_cast hcard
  have hN : (Fintype.card (HardSample n) : ℝ) ≠ 0 := by positivity
  have hcard_real' :
      (Fintype.card {ω : HardSample n // ω ∈ F} : ℝ) *
        (Fintype.card {ω : HardSample n // ω ∈ P} : ℝ) =
      (Fintype.card {ω : HardSample n // ω ∈ X} : ℝ) *
        (Fintype.card {ω : HardSample n // ω ∈ Y} : ℝ) := by
    rw [mul_comm, ← hcard_real]
  field_simp [hN]
  convert hcard_real'

/-- To prove the conditional special-pair law factors, it suffices to prove singleton
factorization for the four bit-pairs. -/
theorem conditionalSpecialPairLaw_eq_prod_of_singleton_factorization
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)))
    (hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0)
    (hfactor : ∀ b : Bool × Bool,
      ((conditionalSpecialPairLaw n p z hz : ProbabilityMeasure (Bool × Bool)) :
          Measure (Bool × Bool)).real {b} =
        ((conditionalSpecialXLaw n p z hz : ProbabilityMeasure Bool) :
          Measure Bool).real {b.1} *
        ((conditionalSpecialYLaw n p z hz : ProbabilityMeasure Bool) :
          Measure Bool).real {b.2}) :
    conditionalSpecialPairLaw n p z hz =
      TVDistance.probabilityMeasureProd
        (conditionalSpecialXLaw n p z hz) (conditionalSpecialYLaw n p z hz) := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro b
  rw [hfactor b]
  rcases b with ⟨bx, bY⟩
  rw [TVDistance.probabilityMeasureProd]
  change
    ((conditionalSpecialXLaw n p z hz : ProbabilityMeasure Bool) :
        Measure Bool).real {bx} *
      ((conditionalSpecialYLaw n p z hz : ProbabilityMeasure Bool) :
        Measure Bool).real {bY} =
      (((conditionalSpecialXLaw n p z hz : ProbabilityMeasure Bool) :
          Measure Bool).prod
        ((conditionalSpecialYLaw n p z hz : ProbabilityMeasure Bool) :
          Measure Bool) ({(bx, bY)})).toReal
  rw [show ({(bx, bY)} : Set (Bool × Bool)) = ({bx} : Set Bool) ×ˢ ({bY} : Set Bool) by
    ext b
    simp [Prod.ext_iff]]
  rw [Measure.prod_prod, ENNReal.toReal_mul]
  rfl

/-- Singleton factorization can be proved directly on the underlying `Z=z` fiber measure. -/
theorem conditionalSpecialPairLaw_eq_prod_of_zFiberMeasure_factorization
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)))
    (hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0)
    (hfactor : ∀ b : Bool × Bool,
      (zFiberMeasure n p z).real ((specialPair n) ⁻¹' {b}) =
        (zFiberMeasure n p z).real ((specialX n) ⁻¹' {b.1}) *
        (zFiberMeasure n p z).real ((specialY n) ⁻¹' {b.2})) :
    conditionalSpecialPairLaw n p z hz =
      TVDistance.probabilityMeasureProd
        (conditionalSpecialXLaw n p z hz) (conditionalSpecialYLaw n p z hz) := by
  refine conditionalSpecialPairLaw_eq_prod_of_singleton_factorization n p z hz ?_
  intro b
  rw [conditionalSpecialPairLaw_singleton, conditionalSpecialXLaw_singleton,
    conditionalSpecialYLaw_singleton]
  exact hfactor b

/-- A cross-multiplied version of singleton factorization, phrased using the original hard
distribution instead of conditional fiber probabilities. -/
theorem conditionalSpecialPairLaw_eq_prod_of_fiber_volume_factorization
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)))
    (hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0)
    (hfactor : ∀ b : Bool × Bool,
      (volume : Measure (HardSample n)).real ((zVariable n p) ⁻¹' {z}) *
          (volume : Measure (HardSample n)).real
            (((zVariable n p) ⁻¹' {z}) ∩ ((specialPair n) ⁻¹' {b})) =
        (volume : Measure (HardSample n)).real
            (((zVariable n p) ⁻¹' {z}) ∩ ((specialX n) ⁻¹' {b.1})) *
          (volume : Measure (HardSample n)).real
            (((zVariable n p) ⁻¹' {z}) ∩ ((specialY n) ⁻¹' {b.2}))) :
    conditionalSpecialPairLaw n p z hz =
      TVDistance.probabilityMeasureProd
        (conditionalSpecialXLaw n p z hz) (conditionalSpecialYLaw n p z hz) := by
  refine conditionalSpecialPairLaw_eq_prod_of_zFiberMeasure_factorization n p z hz ?_
  intro b
  rw [zFiberMeasure_real_apply, zFiberMeasure_real_apply, zFiberMeasure_real_apply]
  have hm :
      (volume : Measure (HardSample n)).real ((zVariable n p) ⁻¹' {z}) ≠ 0 := by
    rwa [MeasureTheory.measureReal_ne_zero_iff]
  have h := hfactor b
  field_simp [hm]
  exact h

open Classical in
/-- The protocol transcript is a rectangle on each coarse fiber, so conditioned on a positive
`Z=z` fiber the special bits factor as the product of their two marginals. -/
theorem conditionalSpecialPairLaw_eq_prod
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)))
    (hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0) :
    conditionalSpecialPairLaw n p z hz =
      TVDistance.probabilityMeasureProd
        (conditionalSpecialXLaw n p z hz) (conditionalSpecialYLaw n p z hz) := by
  exact conditionalSpecialPairLaw_eq_prod_of_fiber_volume_factorization n p z hz
    (fiber_volume_factorization n p z)

open Classical in
/-- A product special-pair law gives singleton factorization of the conditional bit laws on the
same `Z` fiber. -/
theorem conditionalSpecialPairLaw_singleton_factorization_of_eq_prod
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)))
    (hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0)
    (hprod :
      conditionalSpecialPairLaw n p z hz =
        TVDistance.probabilityMeasureProd
          (conditionalSpecialXLaw n p z hz) (conditionalSpecialYLaw n p z hz))
    (b : Bool × Bool) :
    ((conditionalSpecialPairLaw n p z hz : ProbabilityMeasure (Bool × Bool)) :
        Measure (Bool × Bool)).real {b} =
      ((conditionalSpecialXLaw n p z hz : ProbabilityMeasure Bool) :
        Measure Bool).real {b.1} *
        ((conditionalSpecialYLaw n p z hz : ProbabilityMeasure Bool) :
          Measure Bool).real {b.2} := by
  rw [hprod]
  rcases b with ⟨bX, bY⟩
  rw [TVDistance.probabilityMeasureProd]
  change
    (((conditionalSpecialXLaw n p z hz : ProbabilityMeasure Bool) :
        Measure Bool).prod
      ((conditionalSpecialYLaw n p z hz : ProbabilityMeasure Bool) :
        Measure Bool) ({(bX, bY)})).toReal =
      ((conditionalSpecialXLaw n p z hz : ProbabilityMeasure Bool) :
        Measure Bool).real {bX} *
        ((conditionalSpecialYLaw n p z hz : ProbabilityMeasure Bool) :
          Measure Bool).real {bY}
  rw [show ({(bX, bY)} : Set (Bool × Bool)) = ({bX} : Set Bool) ×ˢ ({bY} : Set Bool) by
    ext b
    simp [Prod.ext_iff]]
  rw [Measure.prod_prod, ENNReal.toReal_mul]
  rfl

open Classical in
/-- On a product-law `Z` fiber, conditioning on one Bob special-bit value does not change Alice's
special-bit law. -/
theorem conditionalSpecialXLaw_eq_cond_specialY_of_prod
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)))
    (hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0)
    (hprod :
      conditionalSpecialPairLaw n p z hz =
        TVDistance.probabilityMeasureProd
          (conditionalSpecialXLaw n p z hz) (conditionalSpecialYLaw n p z hz))
    (bY : Bool)
    (hY : (zFiberMeasure n p z).real ((specialY n) ⁻¹' {bY}) ≠ 0) :
    conditionalSpecialXLaw n p z hz =
      ProbabilityMeasure.map
        (⟨(zFiberMeasure n p z)[|(specialY n) ⁻¹' {bY}],
          ProbabilityTheory.cond_isProbabilityMeasure_of_real hY⟩ :
          ProbabilityMeasure (HardSample n))
        (Measurable.of_discrete.aemeasurable (f := specialX n)) := by
  let ν : ProbabilityMeasure (HardSample n) :=
    ⟨(zFiberMeasure n p z)[|(specialY n) ⁻¹' {bY}],
      ProbabilityTheory.cond_isProbabilityMeasure_of_real hY⟩
  change conditionalSpecialXLaw n p z hz =
    ProbabilityMeasure.map ν (Measurable.of_discrete.aemeasurable (f := specialX n))
  apply ProbabilityMeasure.toMeasure_injective
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro bX
  rw [conditionalSpecialXLaw_singleton]
  rw [Measure.real]
  change ((zFiberMeasure n p z) ((specialX n) ⁻¹' {bX})).toReal =
    (((ProbabilityMeasure.map ν
      (Measurable.of_discrete.aemeasurable (f := specialX n)) : ProbabilityMeasure Bool) :
      Measure Bool) {bX}).toReal
  rw [ProbabilityMeasure.map_apply' _ _ MeasurableSet.of_discrete]
  rw [← Measure.real]
  change (zFiberMeasure n p z).real ((specialX n) ⁻¹' {bX}) =
    ((zFiberMeasure n p z)[|(specialY n) ⁻¹' {bY}]).real ((specialX n) ⁻¹' {bX})
  rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  have hpair :
      ((specialY n) ⁻¹' {bY}) ∩ ((specialX n) ⁻¹' {bX}) =
        (specialPair n) ⁻¹' {(bX, bY)} := by
    ext ω
    simp [specialPair, specialX, specialY, and_comm]
  have hfactor :=
    conditionalSpecialPairLaw_singleton_factorization_of_eq_prod n p z hz hprod (bX, bY)
  rw [conditionalSpecialPairLaw_singleton, conditionalSpecialXLaw_singleton,
    conditionalSpecialYLaw_singleton] at hfactor
  rw [hpair, hfactor]
  field_simp [hY]

open Classical in
/-- Rectangle switching implies the textbook fiber identity
`p(X_T | Z=z) = p(X_T | Z=z, Y_T=false)`. -/
theorem conditionalSpecialXLaw_eq_cond_specialYFalse
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)))
    (hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0)
    (hY : (zFiberMeasure n p z).real ((specialY n) ⁻¹' {false}) ≠ 0) :
    conditionalSpecialXLaw n p z hz =
      ProbabilityMeasure.map
        (⟨(zFiberMeasure n p z)[|(specialY n) ⁻¹' {false}],
          ProbabilityTheory.cond_isProbabilityMeasure_of_real hY⟩ :
          ProbabilityMeasure (HardSample n))
        (Measurable.of_discrete.aemeasurable (f := specialX n)) :=
  conditionalSpecialXLaw_eq_cond_specialY_of_prod n p z hz
    (conditionalSpecialPairLaw_eq_prod n p z hz) false hY

open Classical in
/-- After rectangle switching, Alice's `xFiberKL` can be computed by first conditioning on
`Y_T=false` inside the `Z=z` fiber. -/
theorem xFiberKL_eq_cond_specialYFalse_klDiv
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)))
    (hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0)
    (hY : (zFiberMeasure n p z).real ((specialY n) ⁻¹' {false}) ≠ 0) :
    xFiberKL n p z =
      (InformationTheory.klDiv
        ((ProbabilityMeasure.map
          (⟨(zFiberMeasure n p z)[|(specialY n) ⁻¹' {false}],
            ProbabilityTheory.cond_isProbabilityMeasure_of_real hY⟩ :
            ProbabilityMeasure (HardSample n))
          (Measurable.of_discrete.aemeasurable (f := specialX n)) :
          ProbabilityMeasure Bool) : Measure Bool)
        ((uniformBool : ProbabilityMeasure Bool) : Measure Bool)).toReal := by
  rw [xFiberKL, dif_pos hz]
  rw [conditionalSpecialXLaw_eq_cond_specialYFalse n p z hz hY]

open Classical in
/-- Alice's `xFiberKL` can be rewritten as KL for the special Alice bit under
`D ∧ Y_T=false` conditioned on the same `Z=z` fiber. -/
theorem xFiberKL_eq_disjointSpecialYFalseMeasure_cond_zVariable_klDiv
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)))
    (hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0)
    (hY : (zFiberMeasure n p z).real ((specialY n) ⁻¹' {false}) ≠ 0) :
    xFiberKL n p z =
      (InformationTheory.klDiv
        (Measure.map (specialX n)
          ((disjointSpecialYFalseMeasure n)[|zVariable n p ← z]))
        ((uniformBool : ProbabilityMeasure Bool) : Measure Bool)).toReal := by
  rw [xFiberKL_eq_cond_specialYFalse_klDiv n p z hz hY]
  change
    (InformationTheory.klDiv
      (Measure.map (specialX n)
        ((zFiberMeasure n p z)[|(specialY n) ⁻¹' {false}]))
      ((uniformBool : ProbabilityMeasure Bool) : Measure Bool)).toReal =
    (InformationTheory.klDiv
      (Measure.map (specialX n)
        ((disjointSpecialYFalseMeasure n)[|zVariable n p ← z]))
      ((uniformBool : ProbabilityMeasure Bool) : Measure Bool)).toReal
  rw [zFiberMeasure_cond_specialYFalse_eq_disjointSpecialYFalseMeasure_cond_zVariable]

open Classical in
/-- Positive mass under `D ∧ Y_T=false` supplies the positivity hypotheses needed to rewrite
Alice's fiber KL using the `D ∧ Y_T=false, Z=z` conditional law. -/
theorem xFiberKL_eq_disjointSpecialYFalseMeasure_cond_zVariable_klDiv_of_ne_zero
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)))
    (hz : (disjointSpecialYFalseMeasure n).real ((zVariable n p) ⁻¹' {z}) ≠ 0) :
    xFiberKL n p z =
      (InformationTheory.klDiv
        (Measure.map (specialX n)
          ((disjointSpecialYFalseMeasure n)[|zVariable n p ← z]))
        ((uniformBool : ProbabilityMeasure Bool) : Measure Bool)).toReal := by
  exact xFiberKL_eq_disjointSpecialYFalseMeasure_cond_zVariable_klDiv n p z
    (volume_zFiber_ne_zero_of_disjointSpecialYFalseMeasure_ne_zero n p z hz)
    (zFiberMeasure_specialYFalse_ne_zero_of_disjointSpecialYFalseMeasure_ne_zero n p z hz)

open Classical in
/-- Product-distribution step in Lemma 6.22 for `Z` fibers.  This uses the textbook rectangle
fact: conditioned on a transcript rectangle and the coarse data, the special bits are independent,
so the pair TV distance is controlled by the two one-bit TV distances. -/
theorem zDistance_le_xDistance_add_yDistance
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))) :
    zDistance n p z ≤ xDistance n p z + yDistance n p z := by
  by_cases hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0
  · simpa [zDistance, xDistance, yDistance, hz, conditionalSpecialPairLaw_eq_prod n p z hz,
      uniformBoolPair_eq_prod] using
      TVDistance.tvDistance_prod_le
        (conditionalSpecialXLaw n p z hz) uniformBool
        (conditionalSpecialYLaw n p z hz) uniformBool
  · simp [zDistance, xDistance, yDistance, hz]

/-- If both one-bit marginal distances on a `Z` fiber are at most `γ`, then the fiber is good. -/
theorem mem_goodZEvent_of_xDistance_yDistance_le
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {γ : ℝ} {ω : HardSample n}
    (hx : xDistance n p (zVariable n p ω) ≤ γ)
    (hy : yDistance n p (zVariable n p ω) ≤ γ) :
    ω ∈ goodZEvent n p γ := by
  have h := zDistance_le_xDistance_add_yDistance n p (zVariable n p ω)
  change zDistance n p (zVariable n p ω) ≤ 2 * γ
  linarith

/-- The corrected Alice information term in (6.6):
`I(X_T : M | T, X_<T, Y_≥T, D)`. -/
noncomputable def aliceInfoTerm
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) : ℝ :=
  I[specialX n : message n p | aliceClaimConditioning n ; disjointCondMeasure n]

/-- The corrected Bob information term in (6.6):
`I(Y_T : M | T, X_≤T, Y_>T, D)`. -/
noncomputable def bobInfoTerm
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) : ℝ :=
  I[specialY n : message n p | bobClaimConditioning n ; disjointCondMeasure n]

/-- The total corrected special-coordinate information from (6.6). -/
noncomputable def claimInfo
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) : ℝ :=
  aliceInfoTerm n p + bobInfoTerm n p

open Classical in
/-- Alice's corrected information term is nonnegative. -/
theorem aliceInfoTerm_nonneg
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    0 ≤ aliceInfoTerm n p := by
  rw [aliceInfoTerm]
  exact ProbabilityTheory.condMutualInfo_nonneg
    (μ := disjointCondMeasure n)
    (X := specialX n) (Y := message n p) (Z := aliceClaimConditioning n)
    Measurable.of_discrete Measurable.of_discrete

open Classical in
/-- Bob's corrected information term is nonnegative. -/
theorem bobInfoTerm_nonneg
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    0 ≤ bobInfoTerm n p := by
  rw [bobInfoTerm]
  exact ProbabilityTheory.condMutualInfo_nonneg
    (μ := disjointCondMeasure n)
    (X := specialY n) (Y := message n p) (Z := bobClaimConditioning n)
    Measurable.of_discrete Measurable.of_discrete

/-- Alice's information term is bounded by the total corrected information. -/
theorem aliceInfoTerm_le_claimInfo
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    aliceInfoTerm n p ≤ claimInfo n p := by
  rw [claimInfo]
  linarith [bobInfoTerm_nonneg n p]

/-- Bob's information term is bounded by the total corrected information. -/
theorem bobInfoTerm_le_claimInfo
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    bobInfoTerm n p ≤ claimInfo n p := by
  rw [claimInfo]
  linarith [aliceInfoTerm_nonneg n p]

open Classical in
/-- Alice's corrected information term for the dual protocol is Bob's corrected information term
for the original protocol. -/
theorem aliceInfoTerm_dualProtocol_eq_bobInfoTerm
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    aliceInfoTerm n (dualProtocol n p) = bobInfoTerm n p := by
  let μ : Measure (HardSample n) := disjointCondMeasure n
  have hmap : MeasurePreserving (dualHardSample n) μ μ := by
    simpa [μ] using disjointCondMeasure_measurePreserving_dualHardSample n
  have hpull :
      aliceInfoTerm n (dualProtocol n p) =
        I[fun ω => specialX n (dualHardSample n ω) :
          fun ω => message n (dualProtocol n p) (dualHardSample n ω) |
          fun ω => aliceClaimConditioning n (dualHardSample n ω) ; μ] := by
    rw [aliceInfoTerm]
    exact ProbabilityTheory.IdentDistrib.condMutualInfo_eq
      (μ := μ) (μ' := μ)
      (X := specialX n) (Y := message n (dualProtocol n p))
      (Z := aliceClaimConditioning n)
      (X' := fun ω => specialX n (dualHardSample n ω))
      (Y' := fun ω => message n (dualProtocol n p) (dualHardSample n ω))
      (Z' := fun ω => aliceClaimConditioning n (dualHardSample n ω))
      Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
      Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
      (identDistrib_self_comp_measurePreserving hmap
        (fun ω =>
          (specialX n ω, message n (dualProtocol n p) ω, aliceClaimConditioning n ω))
        Measurable.of_discrete)
  rw [hpull]
  have hrec :
      I[specialY n :
          (fun ω => dualProtocolLeafMap n p (message n p ω)) |
          (fun ω => dualConditioningValue n (bobClaimConditioning n ω)) ; μ] =
        I[specialY n : message n p | bobClaimConditioning n ; μ] := by
    simpa [Function.comp_def] using
      ProbabilityTheory.condMutualInfo_comp_right_conditioning_of_injective
        (μ := μ) (X := specialY n) (Y := message n p) (Z := bobClaimConditioning n)
        (f := dualProtocolLeafMap n p) (g := dualConditioningValue n)
        Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
        Measurable.of_discrete Measurable.of_discrete
        (dualProtocolLeafMap_injective n p) (dualConditioningValue_injective n)
  simpa [μ, bobInfoTerm, specialX_dualHardSample, message_dualProtocol_dualHardSample,
    aliceClaimConditioning_dualHardSample] using hrec

open Classical in
/-- Bob's corrected information term for the dual protocol is Alice's corrected information term
for the original protocol. -/
theorem bobInfoTerm_dualProtocol_eq_aliceInfoTerm
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    bobInfoTerm n (dualProtocol n p) = aliceInfoTerm n p := by
  let μ : Measure (HardSample n) := disjointCondMeasure n
  have hmap : MeasurePreserving (dualHardSample n) μ μ := by
    simpa [μ] using disjointCondMeasure_measurePreserving_dualHardSample n
  have hpull :
      bobInfoTerm n (dualProtocol n p) =
        I[fun ω => specialY n (dualHardSample n ω) :
          fun ω => message n (dualProtocol n p) (dualHardSample n ω) |
          fun ω => bobClaimConditioning n (dualHardSample n ω) ; μ] := by
    rw [bobInfoTerm]
    exact ProbabilityTheory.IdentDistrib.condMutualInfo_eq
      (μ := μ) (μ' := μ)
      (X := specialY n) (Y := message n (dualProtocol n p))
      (Z := bobClaimConditioning n)
      (X' := fun ω => specialY n (dualHardSample n ω))
      (Y' := fun ω => message n (dualProtocol n p) (dualHardSample n ω))
      (Z' := fun ω => bobClaimConditioning n (dualHardSample n ω))
      Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
      Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
      (identDistrib_self_comp_measurePreserving hmap
        (fun ω =>
          (specialY n ω, message n (dualProtocol n p) ω, bobClaimConditioning n ω))
        Measurable.of_discrete)
  rw [hpull]
  have hrec :
      I[specialX n :
          (fun ω => dualProtocolLeafMap n p (message n p ω)) |
          (fun ω => dualConditioningValue n (aliceClaimConditioning n ω)) ; μ] =
        I[specialX n : message n p | aliceClaimConditioning n ; μ] := by
    simpa [Function.comp_def] using
      ProbabilityTheory.condMutualInfo_comp_right_conditioning_of_injective
        (μ := μ) (X := specialX n) (Y := message n p) (Z := aliceClaimConditioning n)
        (f := dualProtocolLeafMap n p) (g := dualConditioningValue n)
        Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
        Measurable.of_discrete Measurable.of_discrete
        (dualProtocolLeafMap_injective n p) (dualConditioningValue_injective n)
  simpa [μ, aliceInfoTerm, specialY_dualHardSample, message_dualProtocol_dualHardSample,
    bobClaimConditioning_dualHardSample] using hrec

open Classical in
/-- Full-vector information for the dual protocol is the swapped full-vector information for the
original protocol. -/
theorem xVector_message_info_dualProtocol_eq_yVector_message_info
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    I[xVector n : message n (dualProtocol n p) | yVector n ; disjointCondMeasure n] =
      I[yVector n : message n p | xVector n ; disjointCondMeasure n] := by
  let μ : Measure (HardSample n) := disjointCondMeasure n
  have hmap : MeasurePreserving (dualHardSample n) μ μ := by
    simpa [μ] using disjointCondMeasure_measurePreserving_dualHardSample n
  have hpull :
      I[xVector n : message n (dualProtocol n p) | yVector n ; μ] =
        I[fun ω => xVector n (dualHardSample n ω) :
          fun ω => message n (dualProtocol n p) (dualHardSample n ω) |
          fun ω => yVector n (dualHardSample n ω) ; μ] := by
    exact ProbabilityTheory.IdentDistrib.condMutualInfo_eq
      (μ := μ) (μ' := μ)
      (X := xVector n) (Y := message n (dualProtocol n p)) (Z := yVector n)
      (X' := fun ω => xVector n (dualHardSample n ω))
      (Y' := fun ω => message n (dualProtocol n p) (dualHardSample n ω))
      (Z' := fun ω => yVector n (dualHardSample n ω))
      Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
      Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
      (identDistrib_self_comp_measurePreserving hmap
        (fun ω => (xVector n ω, message n (dualProtocol n p) ω, yVector n ω))
        Measurable.of_discrete)
  rw [show disjointCondMeasure n = μ by rfl, hpull]
  have hrec :
      I[(fun ω => reverseBoolVector n (yVector n ω)) :
          (fun ω => dualProtocolLeafMap n p (message n p ω)) |
          (fun ω => reverseBoolVector n (xVector n ω)) ; μ] =
        I[yVector n : message n p | xVector n ; μ] := by
    simpa [Function.comp_def] using
      ProbabilityTheory.condMutualInfo_of_inj'
        (X := yVector n) (Y := message n p) (Z := xVector n)
        Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete μ
        (reverseBoolVector_injective n) (dualProtocolLeafMap_injective n p)
        (reverseBoolVector_injective n)
  simpa [μ, xVector_dualHardSample, yVector_dualHardSample,
    message_dualProtocol_dualHardSample] using hrec

open Classical in
/-- The total corrected information is invariant under protocol duality. -/
theorem claimInfo_dualProtocol
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    claimInfo n (dualProtocol n p) = claimInfo n p := by
  rw [claimInfo, aliceInfoTerm_dualProtocol_eq_bobInfoTerm,
    bobInfoTerm_dualProtocol_eq_aliceInfoTerm, claimInfo, add_comm]

open Classical in
/-- The fixed-coordinate summand `I(X_i : M | X_<i, Y_≥i)` in Lemma 6.20. -/
noncomputable def fixedAliceInfoTerm
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (i : Fin n) : ℝ :=
  I[fixedXBit n i : message n p | fixedAliceConditioning n i ; disjointCondMeasure n]

open Classical in
/-- The zero cross-information term `I(X_i : Y_<i | X_<i, Y_≥i)` in Lemma 6.20. -/
noncomputable def fixedAliceCrossInfoTerm (i : Fin n) : ℝ :=
  I[fixedXBit n i : fixedYBefore n i | fixedAliceConditioning n i ; disjointCondMeasure n]

open Classical in
/-- Textbook Lemma 6.20 independence input for the hard distribution conditioned on `D`:
`I(X_i : Y_<i | X_<i, Y_≥i, D) = 0`. -/
theorem fixedAliceCrossInfoTerm_eq_zero (i : Fin n) :
    fixedAliceCrossInfoTerm n i = 0 := by
  sorry

open Classical in
/-- Textbook Lemma 6.20 chain-rule step for the Alice summands:
`∑ᵢ I(X_i : M | X_<i, Y_≥i, D) ≤ I(X : M | Y, D)`.

This is the proof-specific instance of Lemma 6.20; its only probabilistic input is
`fixedAliceCrossInfoTerm_eq_zero`. -/
theorem sum_fixedAliceInfoTerm_le_xVector_info
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    (∑ i : Fin n, fixedAliceInfoTerm n p i) ≤
      I[xVector n : message n p | yVector n ; disjointCondMeasure n] := by
  sorry

open Classical in
/-- Averaging over the special coordinate: conditioned on `D`, `T` is uniform and independent of
`(X,Y,M)`, so the Alice term in (6.6) is the average of the fixed-coordinate Lemma 6.20
summands. -/
theorem aliceInfoTerm_eq_average_fixedAliceInfoTerm
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    aliceInfoTerm n p =
      (∑ i : Fin n, fixedAliceInfoTerm n p i) / (n : ℝ) := by
  sorry

open Classical in
/-- Alice half of Lemma 6.20, after conditioning on disjointness and averaging over the uniform
special coordinate:
`I(X_T : M | T, X_<T, Y_≥T, D) ≤ I(X : M | Y, D) / n`. -/
theorem aliceInfoTerm_le_average_xVector_info
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    aliceInfoTerm n p ≤
      I[xVector n : message n p | yVector n ; disjointCondMeasure n] / (n : ℝ) := by
  rw [aliceInfoTerm_eq_average_fixedAliceInfoTerm]
  exact div_le_div_of_nonneg_right (sum_fixedAliceInfoTerm_le_xVector_info n p) (by positivity)

open Classical in
/-- Bob half of Lemma 6.20, after conditioning on disjointness and averaging over the uniform
special coordinate:
`I(Y_T : M | T, X_≤T, Y_>T, D) ≤ I(Y : M | X, D) / n`. -/
theorem bobInfoTerm_le_average_yVector_info
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    bobInfoTerm n p ≤
      I[yVector n : message n p | xVector n ; disjointCondMeasure n] / (n : ℝ) := by
  have h := aliceInfoTerm_le_average_xVector_info n (dualProtocol n p)
  simpa [aliceInfoTerm_dualProtocol_eq_bobInfoTerm,
    xVector_message_info_dualProtocol_eq_yVector_message_info] using h

open Classical in
/-- The Alice full-vector information is bounded by the transcript entropy. -/
theorem xVector_message_info_le_complexity_mul_log_two
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    I[xVector n : message n p | yVector n ; disjointCondMeasure n] ≤
      p.complexity * Real.log 2 := by
  exact
    (ProbabilityTheory.condMutualInfo_le_entropy_right
      (μ := disjointCondMeasure n)
      (X := xVector n) (Y := message n p) (Z := yVector n)
      Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete).trans
      (entropy_message_le_complexity_mul_log_two_of_measure n p (disjointCondMeasure n))

open Classical in
/-- The Bob full-vector information is bounded by the transcript entropy. -/
theorem yVector_message_info_le_complexity_mul_log_two
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    I[yVector n : message n p | xVector n ; disjointCondMeasure n] ≤
      p.complexity * Real.log 2 := by
  exact
    (ProbabilityTheory.condMutualInfo_le_entropy_right
      (μ := disjointCondMeasure n)
      (X := yVector n) (Y := message n p) (Z := xVector n)
      Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete).trans
      (entropy_message_le_complexity_mul_log_two_of_measure n p (disjointCondMeasure n))

open Classical in
/-- Alice half of Lemma 6.20 plus the entropy bound `H(M) ≤ ℓ`, averaged over the uniform
special coordinate. -/
theorem aliceInfoTerm_le_average_entropy_bound
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    aliceInfoTerm n p ≤ (p.complexity * Real.log 2) / (n : ℝ) := by
  have hchain := aliceInfoTerm_le_average_xVector_info n p
  have hentropy := xVector_message_info_le_complexity_mul_log_two n p
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  exact hchain.trans (div_le_div_of_nonneg_right hentropy hn_nonneg)

open Classical in
/-- Bob half of Lemma 6.20 plus the entropy bound `H(M) ≤ ℓ`, averaged over the uniform special
coordinate. -/
theorem bobInfoTerm_le_average_entropy_bound
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    bobInfoTerm n p ≤ (p.complexity * Real.log 2) / (n : ℝ) := by
  have hchain := bobInfoTerm_le_average_yVector_info n p
  have hentropy := yVector_message_info_le_complexity_mul_log_two n p
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  exact hchain.trans (div_le_div_of_nonneg_right hentropy hn_nonneg)

/-- Lemma 6.20 plus the entropy bound `H(M) ≤ ℓ`: the corrected claim information is at most
the averaged full-vector transcript information.  This is the part before (6.6) in
`.codex/disjointness.txt`. -/
theorem claimInfo_le_average_info_upper
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    claimInfo n p ≤ 2 * (p.complexity * Real.log 2) / (n : ℝ) := by
  rw [claimInfo]
  calc
    aliceInfoTerm n p + bobInfoTerm n p
        ≤ (p.complexity * Real.log 2) / (n : ℝ) +
            (p.complexity * Real.log 2) / (n : ℝ) :=
          add_le_add (aliceInfoTerm_le_average_entropy_bound n p)
            (bobInfoTerm_le_average_entropy_bound n p)
    _ = 2 * (p.complexity * Real.log 2) / (n : ℝ) := by ring

open Classical in
/-- On the branch `Y_T=false`, the corrected Alice suffix `Y_≥T` is the same information as
the coarse suffix `Y_>T`, since the missing coordinate is fixed to `false`. -/
theorem yGeSpecial_eq_yAfterSpecial_of_specialY_false
    {ω : HardSample n} (hY : specialY n ω = false) :
    yGeSpecial n ω = yAfterSpecial n ω := by
  funext j
  by_cases hlt : ω.T < j
  · have hle : ω.T ≤ j := le_of_lt hlt
    simp [yGeSpecial, yAfterSpecial, hle, hlt]
  · by_cases hle : ω.T ≤ j
    · have hEq : j = ω.T := le_antisymm (not_lt.mp hlt) hle
      subst j
      simp [yGeSpecial, yAfterSpecial, yBit]
      change ω.yT = false at hY
      exact hY
    · simp [yGeSpecial, yAfterSpecial, hle, hlt]

open Classical in
/-- On the branch `Y_T=false`, Alice's corrected Claim 6.21 conditioning is exactly the coarse
conditioning from the textbook `Z=(M,T,X_<T,Y_>T)`. -/
theorem aliceClaimConditioning_eq_coarseConditioning_of_specialY_false
    {ω : HardSample n} (hY : specialY n ω = false) :
    aliceClaimConditioning n ω = coarseConditioning n ω := by
  simp [aliceClaimConditioning, coarseConditioning,
    yGeSpecial_eq_yAfterSpecial_of_specialY_false n hY]

open Classical in
/-- Under `D ∧ Y_T=false`, Bob's special bit is almost surely `false`. -/
theorem disjointSpecialYFalseMeasure_ae_specialY_false :
    ∀ᵐ ω ∂disjointSpecialYFalseMeasure n, specialY n ω = false := by
  rw [disjointSpecialYFalseMeasure]
  filter_upwards [ae_cond_mem MeasurableSet.of_discrete] with ω hω
  simpa using hω

open Classical in
/-- Under `D ∧ Y_T=false`, Alice's fine conditioning variable is a.e. the coarse conditioning
variable. -/
theorem aliceClaimConditioning_ae_eq_coarseConditioning_disjointSpecialYFalse :
    aliceClaimConditioning n =ᵐ[disjointSpecialYFalseMeasure n] coarseConditioning n := by
  filter_upwards [disjointSpecialYFalseMeasure_ae_specialY_false n] with ω hY
  exact aliceClaimConditioning_eq_coarseConditioning_of_specialY_false n hY

open Classical in
/-- The Claim 6.21 Alice information term after additionally conditioning on `Y_T=false`:
`I(X_T : M | T, X_<T, Y_≥T, Y_T=0, D)`. -/
noncomputable def aliceInfoTermSpecialYFalse
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) : ℝ :=
  I[specialX n : message n p | aliceClaimConditioning n ; disjointSpecialYFalseMeasure n]

open Classical in
/-- The same Alice `Y_T=false` information term using the textbook coarse conditioning
`T, X_<T, Y_>T`. -/
noncomputable def aliceCoarseInfoTermSpecialYFalse
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) : ℝ :=
  I[specialX n : message n p | coarseConditioning n ; disjointSpecialYFalseMeasure n]

open Classical in
/-- Since `X_T` is uniform under `D ∧ Y_T=false`, the conditional KL average to the uniform bit
law is the mutual information between `X_T` and the full `Z=(M,T,X_<T,Y_>T)` variable. -/
theorem condKLDiv_specialX_zVariable_eq_mutualInfo_zVariable
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    condKLDiv (specialX n) id (zVariable n p) (disjointSpecialYFalseMeasure n)
        ((uniformBool : ProbabilityMeasure Bool) : Measure Bool) =
      I[specialX n : zVariable n p ; disjointSpecialYFalseMeasure n] := by
  haveI : IsProbabilityMeasure (disjointSpecialYFalseMeasure n) :=
    disjointSpecialYFalseMeasure_isProbabilityMeasure n
  have hmap : Measure.map (specialX n) (disjointSpecialYFalseMeasure n) =
      ((uniformBool : ProbabilityMeasure Bool) : Measure Bool) := by
    simpa using congrArg (fun ν : ProbabilityMeasure Bool => ((ν : Measure Bool)))
      (disjointSpecialYFalseMeasure_specialX_law_eq_uniformBool n)
  have hKL0 :
      KL[specialX n ; disjointSpecialYFalseMeasure n # id ;
        ((uniformBool : ProbabilityMeasure Bool) : Measure Bool)] = 0 := by
    simp [KLDiv, hmap]
  have hcond := condKLDiv_eq
    (μ := disjointSpecialYFalseMeasure n)
    (μ' := ((uniformBool : ProbabilityMeasure Bool) : Measure Bool))
    (X := specialX n) (Y := id) (Z := zVariable n p)
    Measurable.of_discrete Measurable.of_discrete
    (fun b hb => False.elim (uniformBool_toPMF_ne_zero b (by
      simpa [Measure.toPMF_apply] using hb)))
  rw [hKL0] at hcond
  rw [ProbabilityTheory.mutualInfo_eq_entropy_sub_condEntropy
    Measurable.of_discrete Measurable.of_discrete]
  simpa using hcond

open Classical in
/-- The fine `Y_≥T` and coarse `Y_>T` versions of the Alice `Y_T=false` information term agree,
because `Y_T` is fixed on the conditioned measure. -/
theorem aliceInfoTermSpecialYFalse_eq_aliceCoarseInfoTermSpecialYFalse
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    aliceInfoTermSpecialYFalse n p = aliceCoarseInfoTermSpecialYFalse n p := by
  haveI : IsProbabilityMeasure (disjointSpecialYFalseMeasure n) :=
    disjointSpecialYFalseMeasure_isProbabilityMeasure n
  rw [aliceInfoTermSpecialYFalse, aliceCoarseInfoTermSpecialYFalse]
  exact ProbabilityTheory.condMutualInfo_congr_ae
    (μ := disjointSpecialYFalseMeasure n)
    (X := specialX n) (Y := message n p) (Z := aliceClaimConditioning n)
    (X' := specialX n) (Y' := message n p) (Z' := coarseConditioning n)
    Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
    Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
    (by rfl) (by rfl) (aliceClaimConditioning_ae_eq_coarseConditioning_disjointSpecialYFalse n)

open Classical in
/-- The averaged Alice fiber KL cost under `D ∧ Y_T=false`, as a finite sum over `Z` values. -/
theorem integral_xFiberKL_disjointSpecialYFalse_eq_sum_zVariable
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    (∫ ω, xFiberKL n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n)) =
      ∑ z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)),
        (disjointSpecialYFalseMeasure n).real ((zVariable n p) ⁻¹' {z}) *
          xFiberKL n p z := by
  haveI : IsProbabilityMeasure (disjointSpecialYFalseMeasure n) :=
    disjointSpecialYFalseMeasure_isProbabilityMeasure n
  exact FiniteMeasureSpace.integral_comp_eq_sum_measureReal_fibers
    (μ := disjointSpecialYFalseMeasure n) (Z := zVariable n p) (f := xFiberKL n p)

open Classical in
/-- The averaged Alice fiber KL cost under `D ∧ Y_T=false` as a finite sum of actual KL
divergences for the conditional `Z=z` laws. -/
theorem integral_xFiberKL_disjointSpecialYFalse_eq_sum_zVariable_klDiv
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    (∫ ω, xFiberKL n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n)) =
      ∑ z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)),
        (disjointSpecialYFalseMeasure n).real ((zVariable n p) ⁻¹' {z}) *
          (InformationTheory.klDiv
            (Measure.map (specialX n)
              ((disjointSpecialYFalseMeasure n)[|zVariable n p ← z]))
            ((uniformBool : ProbabilityMeasure Bool) : Measure Bool)).toReal := by
  rw [integral_xFiberKL_disjointSpecialYFalse_eq_sum_zVariable]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : (disjointSpecialYFalseMeasure n).real ((zVariable n p) ⁻¹' {z}) = 0
  · simp [hz]
  · rw [xFiberKL_eq_disjointSpecialYFalseMeasure_cond_zVariable_klDiv_of_ne_zero n p z hz]

open Classical in
/-- The averaged Alice fiber KL under `D ∧ Y_T=false`, rewritten as the PFR real conditional KL
used by the entropy API. -/
theorem integral_xFiberKL_disjointSpecialYFalse_eq_condKLDiv_zVariable
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    (∫ ω, xFiberKL n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n)) =
      condKLDiv (specialX n) id (zVariable n p) (disjointSpecialYFalseMeasure n)
        ((uniformBool : ProbabilityMeasure Bool) : Measure Bool) := by
  haveI : IsProbabilityMeasure (disjointSpecialYFalseMeasure n) :=
    disjointSpecialYFalseMeasure_isProbabilityMeasure n
  rw [integral_xFiberKL_disjointSpecialYFalse_eq_sum_zVariable_klDiv]
  rw [condKLDiv, tsum_fintype]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : (disjointSpecialYFalseMeasure n).real ((zVariable n p) ⁻¹' {z}) = 0
  · simp [hz]
  · rw [toReal_klDiv_map_bool_uniform_eq_KLDiv_of_measureReal_ne_zero
      (μ := disjointSpecialYFalseMeasure n) (X := specialX n)
      (S := (zVariable n p) ⁻¹' {z}) Measurable.of_discrete hz]

open Classical in
/-- Flip only Alice's special-coordinate bit.  This preserves the coarse Claim 6.21 data
`T, X_<T, Y_>T` and toggles `X_T`. -/
def flipSpecialX (ω : HardSample n) : HardSample n where
  T := ω.T
  xT := !ω.xT
  yT := ω.yT
  other := ω.other

theorem flipSpecialX_flipSpecialX (ω : HardSample n) :
    flipSpecialX n (flipSpecialX n ω) = ω := by
  rcases ω with ⟨T, xT, yT, other⟩
  cases xT <;> rfl

theorem flipSpecialX_preimage_singleton (ω : HardSample n) :
    (flipSpecialX n) ⁻¹' ({ω} : Set (HardSample n)) = {flipSpecialX n ω} := by
  ext η
  constructor
  · intro hη
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hη
    rw [← hη]
    simp [flipSpecialX_flipSpecialX]
  · intro hη
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hη ⊢
    rw [hη, flipSpecialX_flipSpecialX]

theorem volume_measureReal_singleton_flipSpecialX (ω : HardSample n) :
    (volume : Measure (HardSample n)).real ({flipSpecialX n ω} : Set (HardSample n)) =
      (volume : Measure (HardSample n)).real ({ω} : Set (HardSample n)) := by
  change ((ProbabilityTheory.uniformOn Set.univ : Measure (HardSample n)).real
      ({flipSpecialX n ω} : Set (HardSample n))) =
    ((ProbabilityTheory.uniformOn Set.univ : Measure (HardSample n)).real
      ({ω} : Set (HardSample n)))
  repeat rw [Measure.real]
  rw [uniformOn_univ_measureReal_eq_card_subtype,
    uniformOn_univ_measureReal_eq_card_subtype]
  simp

theorem volume_measurePreserving_flipSpecialX :
    MeasurePreserving (flipSpecialX n)
      (volume : Measure (HardSample n)) (volume : Measure (HardSample n)) := by
  refine ⟨Measurable.of_discrete, ?_⟩
  rw [MeasureTheory.ext_iff_measureReal_singleton]
  intro ω
  rw [Measure.real]
  rw [Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  rw [← Measure.real, flipSpecialX_preimage_singleton,
    volume_measureReal_singleton_flipSpecialX]

theorem specialX_flipSpecialX (ω : HardSample n) :
    specialX n (flipSpecialX n ω) = !specialX n ω := by
  simp [flipSpecialX, specialX]

theorem specialY_flipSpecialX (ω : HardSample n) :
    specialY n (flipSpecialX n ω) = specialY n ω := by
  simp [flipSpecialX, specialY]

theorem xBeforeSpecial_flipSpecialX (ω : HardSample n) :
    xBeforeSpecial n (flipSpecialX n ω) = xBeforeSpecial n ω := by
  funext i
  by_cases hlt : i < ω.T
  · have hi : i ≠ ω.T := ne_of_lt hlt
    simp [xBeforeSpecial, xBit, flipSpecialX, hlt, hi]
  · simp [xBeforeSpecial, flipSpecialX, hlt]

theorem yAfterSpecial_flipSpecialX (ω : HardSample n) :
    yAfterSpecial n (flipSpecialX n ω) = yAfterSpecial n ω := by
  funext i
  simp [yAfterSpecial, yBit, flipSpecialX]

theorem coarseConditioning_flipSpecialX (ω : HardSample n) :
    coarseConditioning n (flipSpecialX n ω) = coarseConditioning n ω := by
  unfold coarseConditioning
  rw [show specialCoordinate n (flipSpecialX n ω) = specialCoordinate n ω by
      simp [specialCoordinate, flipSpecialX],
    xBeforeSpecial_flipSpecialX, yAfterSpecial_flipSpecialX]

open Classical in
/-- Flipping Alice's special bit bijects the two `X_T` branches inside every
`Y_T=false, coarse=c` fiber. -/
theorem card_specialYFalse_coarseConditioning_specialX_false_eq_true
    (c : Fin n × (Fin n → Bool) × (Fin n → Bool)) :
    Fintype.card {ω : HardSample n //
        ω ∈ ((specialY n) ⁻¹' {false}) ∩ ((coarseConditioning n) ⁻¹' {c}) ∩
          ((specialX n) ⁻¹' {false})} =
      Fintype.card {ω : HardSample n //
        ω ∈ ((specialY n) ⁻¹' {false}) ∩ ((coarseConditioning n) ⁻¹' {c}) ∩
          ((specialX n) ⁻¹' {true})} := by
  refine Fintype.card_congr
    { toFun := ?toFun
      invFun := ?invFun
      left_inv := ?left_inv
      right_inv := ?right_inv }
  · intro ω
    refine ⟨flipSpecialX n ω.1, ?_⟩
    rcases ω.2 with ⟨⟨hY, hC⟩, hX⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa [specialY_flipSpecialX] using hY
    · simpa [coarseConditioning_flipSpecialX] using hC
    · have hx : specialX n (flipSpecialX n ω.1) = true := by
        rw [specialX_flipSpecialX, hX]
        rfl
      simpa using hx
  · intro ω
    refine ⟨flipSpecialX n ω.1, ?_⟩
    rcases ω.2 with ⟨⟨hY, hC⟩, hX⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa [specialY_flipSpecialX] using hY
    · simpa [coarseConditioning_flipSpecialX] using hC
    · have hx : specialX n (flipSpecialX n ω.1) = false := by
        rw [specialX_flipSpecialX, hX]
        rfl
      simpa using hx
  · intro ω
    apply Subtype.ext
    exact flipSpecialX_flipSpecialX n ω.1
  · intro ω
    apply Subtype.ext
    exact flipSpecialX_flipSpecialX n ω.1

open Classical in
/-- In every `Y_T=false, coarse=c` fiber of the ambient hard distribution, each value of `X_T`
has half the mass. -/
theorem volume_measureReal_specialYFalse_inter_coarseConditioning_inter_specialX
    (b : Bool) (c : Fin n × (Fin n → Bool) × (Fin n → Bool)) :
    (volume : Measure (HardSample n)).real
        (((specialY n) ⁻¹' {false}) ∩ ((coarseConditioning n) ⁻¹' {c}) ∩
          ((specialX n) ⁻¹' {b})) =
      (1 / 2 : ℝ) *
        (volume : Measure (HardSample n)).real
          (((specialY n) ⁻¹' {false}) ∩ ((coarseConditioning n) ⁻¹' {c})) := by
  let Y0 : Set (HardSample n) := (specialY n) ⁻¹' {false}
  let C : Set (HardSample n) := (coarseConditioning n) ⁻¹' {c}
  let XF : Set (HardSample n) := (specialX n) ⁻¹' {false}
  let XT : Set (HardSample n) := (specialX n) ⁻¹' {true}
  have hfalse_true :
      (volume : Measure (HardSample n)).real (Y0 ∩ C ∩ XF) =
        (volume : Measure (HardSample n)).real (Y0 ∩ C ∩ XT) := by
    have hpre : (flipSpecialX n) ⁻¹' (Y0 ∩ C ∩ XT) = Y0 ∩ C ∩ XF := by
      ext ω
      simp [Y0, C, XF, XT, specialY_flipSpecialX, coarseConditioning_flipSpecialX,
        specialX_flipSpecialX]
    have hpre_measure :
        (volume : Measure (HardSample n)) ((flipSpecialX n) ⁻¹' (Y0 ∩ C ∩ XT)) =
          (volume : Measure (HardSample n)) (Y0 ∩ C ∩ XT) :=
      Measure.measure_preimage_of_map_eq_self
        (volume_measurePreserving_flipSpecialX n).map_eq
        MeasurableSet.of_discrete.nullMeasurableSet
    change ((volume : Measure (HardSample n)) (Y0 ∩ C ∩ XF)).toReal =
      ((volume : Measure (HardSample n)) (Y0 ∩ C ∩ XT)).toReal
    rw [← hpre, hpre_measure]
  have hunion : Y0 ∩ C = (Y0 ∩ C ∩ XF) ∪ (Y0 ∩ C ∩ XT) := by
    ext ω
    by_cases hx : specialX n ω = false
    · simp [Y0, C, XF, XT, hx]
    · have hxtrue : specialX n ω = true := by
        cases h : specialX n ω
        · exact False.elim (hx h)
        · rfl
      simp [Y0, C, XF, XT, hx]
  have hdisj : Disjoint (Y0 ∩ C ∩ XF) (Y0 ∩ C ∩ XT) := by
    rw [Set.disjoint_left]
    intro ω hF hT
    have hfalse : specialX n ω = false := by simpa [XF] using hF.2
    have htrue : specialX n ω = true := by simpa [XT] using hT.2
    rw [hfalse] at htrue
    simp at htrue
  have hsum :
      (volume : Measure (HardSample n)).real (Y0 ∩ C) =
        (volume : Measure (HardSample n)).real (Y0 ∩ C ∩ XF) +
          (volume : Measure (HardSample n)).real (Y0 ∩ C ∩ XT) := by
    simpa [← hunion] using
      (measureReal_union hdisj MeasurableSet.of_discrete :
        (volume : Measure (HardSample n)).real
            ((Y0 ∩ C ∩ XF) ∪ (Y0 ∩ C ∩ XT)) =
          (volume : Measure (HardSample n)).real (Y0 ∩ C ∩ XF) +
            (volume : Measure (HardSample n)).real (Y0 ∩ C ∩ XT))
  cases b
  · change (volume : Measure (HardSample n)).real (Y0 ∩ C ∩ XF) =
      (1 / 2 : ℝ) * (volume : Measure (HardSample n)).real (Y0 ∩ C)
    linarith
  · change (volume : Measure (HardSample n)).real (Y0 ∩ C ∩ XT) =
      (1 / 2 : ℝ) * (volume : Measure (HardSample n)).real (Y0 ∩ C)
    linarith

open Classical in
/-- The preceding ambient counting identity remains true after conditioning on `Y_T=false`. -/
theorem disjointSpecialYFalseMeasure_measureReal_specialX_inter_coarseConditioning
    (b : Bool) (c : Fin n × (Fin n → Bool) × (Fin n → Bool)) :
    (disjointSpecialYFalseMeasure n).real
        (((specialX n) ⁻¹' {b}) ∩ ((coarseConditioning n) ⁻¹' {c})) =
      (1 / 2 : ℝ) *
        (disjointSpecialYFalseMeasure n).real ((coarseConditioning n) ⁻¹' {c}) := by
  let Y0 : Set (HardSample n) := (specialY n) ⁻¹' {false}
  let Xb : Set (HardSample n) := (specialX n) ⁻¹' {b}
  let C : Set (HardSample n) := (coarseConditioning n) ⁻¹' {c}
  have hleft :
      (disjointSpecialYFalseMeasure n).real (Xb ∩ C) =
        ((disjointCondMeasure n).real Y0)⁻¹ *
          (disjointCondMeasure n).real (Y0 ∩ (Xb ∩ C)) := by
    rw [disjointSpecialYFalseMeasure]
    exact ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete _ (Xb ∩ C)
  have hright :
      (disjointSpecialYFalseMeasure n).real C =
        ((disjointCondMeasure n).real Y0)⁻¹ *
          (disjointCondMeasure n).real (Y0 ∩ C) := by
    rw [disjointSpecialYFalseMeasure]
    exact ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete _ C
  have hbranch_volume :
      (volume : Measure (HardSample n)).real (Y0 ∩ C ∩ Xb) =
        (1 / 2 : ℝ) * (volume : Measure (HardSample n)).real (Y0 ∩ C) := by
    simpa [Y0, C, Xb, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
      volume_measureReal_specialYFalse_inter_coarseConditioning_inter_specialX n b c
  have hbranch :
      (disjointCondMeasure n).real (Y0 ∩ C ∩ Xb) =
        (1 / 2 : ℝ) * (disjointCondMeasure n).real (Y0 ∩ C) := by
    rw [disjointCondMeasure]
    repeat rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
    have hY0C_subset_D : Y0 ∩ C ⊆ disjointEvent n := by
      intro ω hω
      exact mem_disjointEvent_of_specialY_eq_false n (by simpa [Y0] using hω.1)
    have hY0CX_subset_D : Y0 ∩ C ∩ Xb ⊆ disjointEvent n := by
      intro ω hω
      exact hY0C_subset_D ⟨hω.1.1, hω.1.2⟩
    rw [Set.inter_eq_right.mpr hY0CX_subset_D, Set.inter_eq_right.mpr hY0C_subset_D]
    rw [hbranch_volume]
    ring
  rw [hleft, hright]
  have hsets : Y0 ∩ (Xb ∩ C) = Y0 ∩ C ∩ Xb := by
    ext ω
    simp only [Set.mem_inter_iff]
    tauto
  rw [hsets, hbranch]
  ring

open Classical in
/-- Under `D ∧ Y_T=false`, the coarse data `T, X_<T, Y_>T` is independent of `X_T`.
This is the sampling independence used in Claim 6.21 before adding the transcript rectangle. -/
theorem mutualInfo_specialX_coarseConditioning_disjointSpecialYFalse_eq_zero :
    I[specialX n : coarseConditioning n ; disjointSpecialYFalseMeasure n] = 0 := by
  let μ : Measure (HardSample n) := disjointSpecialYFalseMeasure n
  haveI : IsProbabilityMeasure μ := by
    simpa [μ] using disjointSpecialYFalseMeasure_isProbabilityMeasure n
  apply (ProbabilityTheory.mutualInfo_eq_zero Measurable.of_discrete Measurable.of_discrete).mpr
  apply ProbabilityTheory.indepFun_of_measureReal_inter_preimage_singleton_eq_mul
    (μ := μ) (X := specialX n) (Y := coarseConditioning n)
    Measurable.of_discrete Measurable.of_discrete
  intro b c
  rw [show
      μ.real ((specialX n) ⁻¹' {b} ∩ (coarseConditioning n) ⁻¹' {c}) =
        (disjointSpecialYFalseMeasure n).real
          (((specialX n) ⁻¹' {b}) ∩ ((coarseConditioning n) ⁻¹' {c})) by rfl]
  rw [disjointSpecialYFalseMeasure_measureReal_specialX_inter_coarseConditioning]
  rw [disjointSpecialYFalseMeasure_measureReal_specialX_singleton]

open Classical in
/-- The full `Z=(M,coarse)` mutual information is the coarse Claim 6.21 information term,
because the coarse part alone is independent of `X_T` under `D ∧ Y_T=false`. -/
theorem mutualInfo_specialX_zVariable_eq_aliceCoarseInfoTermSpecialYFalse
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    I[specialX n : zVariable n p ; disjointSpecialYFalseMeasure n] =
      aliceCoarseInfoTermSpecialYFalse n p := by
  let μ : Measure (HardSample n) := disjointSpecialYFalseMeasure n
  haveI : IsProbabilityMeasure μ := by
    simpa [μ] using disjointSpecialYFalseMeasure_isProbabilityMeasure n
  let swappedZ : HardSample n → (Fin n × (Fin n → Bool) × (Fin n → Bool)) × p.Leaf :=
    fun ω => (coarseConditioning n ω, message n p ω)
  let swapZ :
      p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)) →
        (Fin n × (Fin n → Bool) × (Fin n → Bool)) × p.Leaf :=
    fun z => (z.2, z.1)
  have hswap_fun : swappedZ = swapZ ∘ zVariable n p := by
    funext ω
    simp [swappedZ, swapZ, zVariable, message]
  have hrec :
      I[specialX n : swappedZ ; μ] =
        I[specialX n : zVariable n p ; μ] := by
    rw [hswap_fun]
    exact ProbabilityTheory.mutualInfo_comp_right_of_injective
      (μ := μ) (X := specialX n) (Y := zVariable n p)
      Measurable.of_discrete Measurable.of_discrete
      swapZ Measurable.of_discrete
      (by
        intro z z' h
        rcases z with ⟨m, c⟩
        rcases z' with ⟨m', c'⟩
        simp only [Prod.ext_iff, swapZ] at h ⊢
        exact ⟨h.2, h.1⟩)
  have hchain :
      I[specialX n : swappedZ ; μ] =
        I[specialX n : coarseConditioning n ; μ] +
          I[specialX n : message n p | coarseConditioning n ; μ] := by
    simpa [swappedZ, μ] using
      ProbabilityTheory.mutualInfo_prod_right_eq_add
        (μ := disjointSpecialYFalseMeasure n)
        (X := specialX n) (Y := coarseConditioning n) (W := message n p)
        Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
  calc
    I[specialX n : zVariable n p ; disjointSpecialYFalseMeasure n]
        = I[specialX n : swappedZ ; μ] := by
          simpa [μ] using hrec.symm
    _ = I[specialX n : coarseConditioning n ; μ] +
          I[specialX n : message n p | coarseConditioning n ; μ] := hchain
    _ = aliceCoarseInfoTermSpecialYFalse n p := by
          rw [mutualInfo_specialX_coarseConditioning_disjointSpecialYFalse_eq_zero]
          simp [aliceCoarseInfoTermSpecialYFalse, μ]

open Classical in
/-- Textbook Claim 6.21 KL identification with the coarse `Z` conditioning:
the average Alice one-bit fiber KL is the conditional mutual information
`I(X_T : M | T,X_<T,Y_>T,Y_T=0,D)`. -/
theorem xFiberKL_integral_eq_aliceCoarseInfoTermSpecialYFalse
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    ∫ ω, xFiberKL n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n) =
      aliceCoarseInfoTermSpecialYFalse n p := by
  rw [integral_xFiberKL_disjointSpecialYFalse_eq_condKLDiv_zVariable]
  rw [condKLDiv_specialX_zVariable_eq_mutualInfo_zVariable]
  exact mutualInfo_specialX_zVariable_eq_aliceCoarseInfoTermSpecialYFalse n p

open Classical in
/-- Textbook Claim 6.21 identification of the average Alice one-bit fiber KL with the conditional
mutual information under `Y_T=false`.  This packages the step
`p(x_t | z) = p(x_t | z, y_t=0) = p(x_t | z, y_t=0, D)` coming from independence and the
rectangle property of the transcript. -/
theorem xFiberKL_integral_eq_aliceInfoTermSpecialYFalse
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    ∫ ω, xFiberKL n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n) =
      aliceInfoTermSpecialYFalse n p := by
  rw [aliceInfoTermSpecialYFalse_eq_aliceCoarseInfoTermSpecialYFalse]
  exact xFiberKL_integral_eq_aliceCoarseInfoTermSpecialYFalse n p

open Classical in
/-- Textbook Claim 6.21 reweighting:
`(2/3) I(X_T : M | T, X_<T, Y_≥T, Y_T=0, D) ≤
 I(X_T : M | T, X_<T, Y_≥T, D)`.

The factor is `Pr[Y_T=false | D] = 2/3`, and the event `Y_T=false` is determined by the
conditioning variable because `Y_≥T` contains `Y_T`. -/
theorem two_thirds_mul_aliceInfoTermSpecialYFalse_le_aliceInfoTerm
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    (2 / 3 : ℝ) * aliceInfoTermSpecialYFalse n p ≤ aliceInfoTerm n p := by
  let μ : Measure (HardSample n) := disjointCondMeasure n
  let Y0 : Set (HardSample n) := (specialY n) ⁻¹' {false}
  haveI : IsProbabilityMeasure μ := by
    simpa [μ] using disjointCondMeasure_isProbabilityMeasure n
  have hmass : μ.real Y0 = (2 / 3 : ℝ) := by
    simpa [μ, Y0] using disjointCondMeasure_measureReal_specialY_false n
  have hdet : Y0 = (aliceClaimConditioning n) ⁻¹' aliceClaimConditioningYFalseValues n := by
    simpa [Y0] using specialY_false_eq_preimage_aliceClaimConditioningYFalseValues n
  have h :=
    ProbabilityTheory.measureReal_mul_cond_condMutualInfo_le_condMutualInfo_of_event_eq_preimage
      (μ := μ)
      (X := specialX n) (Y := message n p) (Z := aliceClaimConditioning n)
      Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
      (A := Y0) (B := aliceClaimConditioningYFalseValues n)
      MeasurableSet.of_discrete hdet
  simpa [μ, Y0, hmass, aliceInfoTermSpecialYFalse, aliceInfoTerm,
    disjointSpecialYFalseMeasure] using h

open Classical in
/-- Textbook Claim 6.21, Alice information step under `D ∧ Y_T=false`: the average one-bit KL
cost is bounded by Alice's term from (6.6), with the `2/3` conditioning factor. -/
theorem claim621_x_fiberKL_disjointSpecialYFalse_le_three_halves_aliceInfoTerm
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    ∫ ω, xFiberKL n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n) ≤
      (3 / 2 : ℝ) * aliceInfoTerm n p := by
  rw [xFiberKL_integral_eq_aliceInfoTermSpecialYFalse]
  have h := two_thirds_mul_aliceInfoTermSpecialYFalse_le_aliceInfoTerm n p
  nlinarith

open Classical in
/-- Textbook Claim 6.21, Alice information step under `D ∧ Y_T=false`: the average one-bit KL
cost is bounded by the small total information assumption. -/
theorem claim621_x_fiberKL_disjointSpecialYFalse_le
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {γ : ℝ}
    (hγ : 0 < γ)
    (hinfo : claimInfo n p ≤ 2 * γ ^ 4 / 3) :
    ∫ ω, xFiberKL n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n) ≤
      2 * γ ^ 4 := by
  have hkl :=
    claim621_x_fiberKL_disjointSpecialYFalse_le_three_halves_aliceInfoTerm n p
  have halice : aliceInfoTerm n p ≤ claimInfo n p :=
    aliceInfoTerm_le_claimInfo n p
  have hclaim :
      (3 / 2 : ℝ) * aliceInfoTerm n p ≤ (3 / 2 : ℝ) * claimInfo n p :=
    mul_le_mul_of_nonneg_left halice (by norm_num)
  have hsmall : (3 / 2 : ℝ) * claimInfo n p ≤ γ ^ 4 := by
    have hmul := mul_le_mul_of_nonneg_left hinfo (by norm_num : (0 : ℝ) ≤ 3 / 2)
    nlinarith
  have hγ4_nonneg : 0 ≤ γ ^ 4 := by positivity
  linarith

open Classical in
/-- Textbook Claim 6.21, Alice Pinsker/information step under `D ∧ Y_T=false`: the squared
one-bit marginal distance has average at most `γ^4`. This is the KL-to-information comparison
from the displayed
`(2/3) I(X_T : M | T, X_<T, Y_≥T, Y_T=0, D) ≤ I(X_T : M | T, X_<T, Y_≥T, D)`. -/
theorem claim621_x_average_sq_distance_disjointSpecialYFalse_le
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {γ : ℝ}
    (hγ : 0 < γ)
    (hinfo : claimInfo n p ≤ 2 * γ ^ 4 / 3) :
    ∫ ω, (xDistance n p (zVariable n p ω)) ^ 2 ∂(disjointSpecialYFalseMeasure n) ≤
      γ ^ 4 := by
  have hpinsker :=
    two_mul_integral_xDistance_sq_le_integral_xFiberKL_disjointSpecialYFalse n p
  have hkl := claim621_x_fiberKL_disjointSpecialYFalse_le n p hγ hinfo
  nlinarith

open Classical in
/-- Alice marginal part of Claim 6.21: under the `(X_T,Y_T)=(0,0)` slice, the set of `Z` fibers
whose Alice special-bit marginal is farther than `γ` from uniform has mass at most `γ / 2`. -/
theorem claim621_x_bad_on_specialZeroZero_le
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {γ : ℝ}
    (hγ : 0 < γ)
    (hinfo : claimInfo n p ≤ 2 * γ ^ 4 / 3) :
    (volume : Measure (HardSample n)).real
      (specialZeroZero n ∩ {ω | γ < xDistance n p (zVariable n p ω)}) ≤ γ / 2 := by
  let μ : Measure (HardSample n) := volume
  let badX : Set (HardSample n) := {ω | γ < xDistance n p (zVariable n p ω)}
  have hsquared :=
    claim621_x_average_sq_distance_disjointSpecialYFalse_le n p hγ hinfo
  have havg :
      ∫ ω, xDistance n p (zVariable n p ω) ∂(disjointSpecialYFalseMeasure n) ≤
        γ ^ 2 :=
    disjointSpecialYFalseMeasure_integral_xDistance_le_of_integral_sq_le n p hsquared
  have hbad_y0 :
      (disjointSpecialYFalseMeasure n).real badX ≤ γ := by
    simpa [badX] using
      disjointSpecialYFalseMeasure_xDistance_bad_le_of_integral_le n p hγ havg
  have htransfer :
      (μ[|specialZeroZero n]).real badX ≤ 2 * γ := by
    have h :=
      volume_cond_specialZeroZero_measureReal_le_two_mul_disjointSpecialYFalseMeasure n badX
    have hbad_y0_two :
        2 * (disjointSpecialYFalseMeasure n).real badX ≤ 2 * γ := by
      nlinarith
    exact h.trans (by simpa [μ] using hbad_y0_two)
  have hcond_eq :
      (μ[|specialZeroZero n]).real badX =
        (μ.real (specialZeroZero n))⁻¹ * μ.real (specialZeroZero n ∩ badX) := by
    rw [ProbabilityTheory.cond_real_apply MeasurableSet.of_discrete]
  have hA : μ.real (specialZeroZero n) = (1 / 4 : ℝ) := by
    simpa [μ, Measure.real] using measureReal_specialZeroZero n
  change μ.real (specialZeroZero n ∩ badX) ≤ γ / 2
  rw [hcond_eq, hA] at htransfer
  norm_num at htransfer
  linarith

open Classical in
/-- Bob marginal part of Claim 6.21, symmetric to the Alice marginal estimate. -/
theorem claim621_y_bad_on_specialZeroZero_le
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {γ : ℝ}
    (hγ : 0 < γ)
    (hinfo : claimInfo n p ≤ 2 * γ ^ 4 / 3) :
    (volume : Measure (HardSample n)).real
      (specialZeroZero n ∩ {ω | γ < yDistance n p (zVariable n p ω)}) ≤ γ / 2 := by
  have hinfoDual : claimInfo n (dualProtocol n p) ≤ 2 * γ ^ 4 / 3 := by
    simpa [claimInfo_dualProtocol n p] using hinfo
  have h :=
    claim621_x_bad_on_specialZeroZero_le n (dualProtocol n p) hγ hinfoDual
  simpa [volume_specialZeroZero_inter_xDistance_dualProtocol_eq_yDistance n p γ] using h

open Classical in
/-- Claim 6.21 in the corrected transcription. If the corrected information from (6.6) is
`≤ 2γ^4 / 3`, then the set of `Z` fibers where the conditional law of `(X_T, Y_T)` is within
`2γ` of uniform has hard-distribution mass at least `(1 - 4γ) / 4`. -/
theorem textbook_claim_6_21
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {γ : ℝ}
    (hγ : 0 < γ)
    (hinfo : claimInfo n p ≤ 2 * γ ^ 4 / 3) :
    (1 / 4 : ℝ) * (1 - 4 * γ) ≤
      (volume : Measure (HardSample n)).real (goodZEvent n p γ) := by
  let μ : Measure (HardSample n) := volume
  let A : Set (HardSample n) := specialZeroZero n
  let badX : Set (HardSample n) := {ω | γ < xDistance n p (zVariable n p ω)}
  let badY : Set (HardSample n) := {ω | γ < yDistance n p (zVariable n p ω)}
  have hxBad : μ.real (A ∩ badX) ≤ γ / 2 := by
    simpa [μ, A, badX] using claim621_x_bad_on_specialZeroZero_le n p hγ hinfo
  have hyBad : μ.real (A ∩ badY) ≤ γ / 2 := by
    simpa [μ, A, badY] using claim621_y_bad_on_specialZeroZero_le n p hγ hinfo
  have hA : μ.real A = (1 / 4 : ℝ) := by
    simpa [μ, A, Measure.real] using measureReal_specialZeroZero n
  have hcover : A ⊆ (goodZEvent n p γ ∪ (A ∩ badX)) ∪ (A ∩ badY) := by
    intro ω hωA
    by_cases hx : γ < xDistance n p (zVariable n p ω)
    · exact Or.inl (Or.inr ⟨hωA, hx⟩)
    · by_cases hy : γ < yDistance n p (zVariable n p ω)
      · exact Or.inr ⟨hωA, hy⟩
      · have hxle : xDistance n p (zVariable n p ω) ≤ γ := le_of_not_gt hx
        have hyle : yDistance n p (zVariable n p ω) ≤ γ := le_of_not_gt hy
        exact Or.inl (Or.inl (mem_goodZEvent_of_xDistance_yDistance_le n p hxle hyle))
  have hmono :
      μ.real A ≤ μ.real ((goodZEvent n p γ ∪ (A ∩ badX)) ∪ (A ∩ badY)) :=
    measureReal_mono hcover
  have hunion_outer :
      μ.real ((goodZEvent n p γ ∪ (A ∩ badX)) ∪ (A ∩ badY)) ≤
        μ.real (goodZEvent n p γ ∪ (A ∩ badX)) + μ.real (A ∩ badY) :=
    measureReal_union_le _ _
  have hunion_inner :
      μ.real (goodZEvent n p γ ∪ (A ∩ badX)) ≤
        μ.real (goodZEvent n p γ) + μ.real (A ∩ badX) :=
    measureReal_union_le _ _
  have htotal :
      μ.real A ≤ μ.real (goodZEvent n p γ) + μ.real (A ∩ badX) + μ.real (A ∩ badY) := by
    linarith
  have hgood : (1 / 4 : ℝ) ≤ μ.real (goodZEvent n p γ) + γ := by
    linarith
  simpa [μ] using (by linarith : (1 / 4 : ℝ) * (1 - 4 * γ) ≤
    μ.real (goodZEvent n p γ))

open Classical in
/-- Intersecting with the defining `Z=z` fiber does not change probabilities under the
corresponding fiber measure. -/
theorem zFiberMeasure_inter_fiber
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)))
    (S : Set (HardSample n)) :
    (zFiberMeasure n p z).real (((zVariable n p) ⁻¹' {z}) ∩ S) =
      (zFiberMeasure n p z).real S := by
  rw [zFiberMeasure]
  rw [Measure.real]
  rw [ProbabilityTheory.cond_inter_self MeasurableSet.of_discrete]
  rfl

open Classical in
/-- Law of total probability over the finite `zVariable` fibers. -/
theorem measureReal_eq_sum_zFiberMeasure_real
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (S : Set (HardSample n)) :
    (volume : Measure (HardSample n)).real S =
      ∑ z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)),
        (volume : Measure (HardSample n)).real ((zVariable n p) ⁻¹' {z}) *
          (zFiberMeasure n p z).real S := by
  let μ : Measure (HardSample n) := volume
  let Z := zVariable n p
  have htotal := ProbabilityTheory.sum_meas_smul_cond_fiber (X := Z) Measurable.of_discrete μ
  have hS : (∑ z, μ (Z ⁻¹' {z}) • μ[|Z ← z]) S = μ S := by
    rw [htotal]
  change μ.real S =
      ∑ z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)),
        μ.real (Z ⁻¹' {z}) * (μ[|Z ← z]).real S
  rw [Measure.real]
  rw [← hS]
  simp only [Measure.real, Measure.coe_finset_sum, Finset.sum_apply, Measure.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro z _
    rw [ENNReal.toReal_mul]
  · intro z _
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)

/-- Protocol error probability decomposed over the finite `zVariable` fibers. -/
theorem protocolErrorEvent_measureReal_eq_sum_zFiberMeasure_real
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool) :
    (volume : Measure (HardSample n)).real (protocolErrorEvent n p) =
      ∑ z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)),
        (volume : Measure (HardSample n)).real ((zVariable n p) ⁻¹' {z}) *
          (zFiberMeasure n p z).real (protocolErrorEvent n p) :=
  measureReal_eq_sum_zFiberMeasure_real n p (protocolErrorEvent n p)

open Classical in
/-- The mass of `goodZEvent` is the sum of the masses of the good `zVariable` fibers. -/
theorem goodZEvent_measureReal_eq_sum_zFibers
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (γ : ℝ) :
    (volume : Measure (HardSample n)).real (goodZEvent n p γ) =
      ∑ z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool)),
        if goodZ n p γ z then
          (volume : Measure (HardSample n)).real ((zVariable n p) ⁻¹' {z})
        else 0 := by
  let μ : ProbabilityMeasure (HardSample n) := ⟨(volume : Measure (HardSample n)), inferInstance⟩
  simpa [goodZEvent, μ] using
    (FiniteMeasureSpace.probabilityMeasure_measureReal_preimage_eq_sum_fibers
      μ (zVariable n p) (goodZ n p γ))

open Classical in
/-- A good `z` gives the expected singleton-mass estimate for the conditional special-pair law. -/
theorem abs_conditionalSpecialPairLaw_singleton_sub_quarter_le
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {γ : ℝ}
    {z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))}
    (hgood : goodZ n p γ z)
    (hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0)
    (b : Bool × Bool) :
    |((conditionalSpecialPairLaw n p z hz : ProbabilityMeasure (Bool × Bool)) :
        Measure (Bool × Bool)).real {b} - (1 / 4 : ℝ)| ≤ 2 * γ := by
  have htv :=
    TVDistance.abs_measureReal_sub_le_tvDistance
      (conditionalSpecialPairLaw n p z hz) uniformBoolPair
      ⟨({b} : Set (Bool × Bool)), MeasurableSet.of_discrete⟩
  rw [uniformBoolPair_singleton] at htv
  have hgood' :
      tvDistance (conditionalSpecialPairLaw n p z hz) uniformBoolPair ≤ 2 * γ := by
    simpa [goodZ, zDistance, hz] using hgood
  exact htv.trans hgood'

/-- A good `z` gives a lower bound on each singleton mass of the conditional special-pair law. -/
theorem quarter_sub_two_mul_le_conditionalSpecialPairLaw_singleton
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {γ : ℝ}
    {z : p.Leaf × (Fin n × (Fin n → Bool) × (Fin n → Bool))}
    (hgood : goodZ n p γ z)
    (hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) ≠ 0)
    (b : Bool × Bool) :
    (1 / 4 : ℝ) - 2 * γ ≤
      ((conditionalSpecialPairLaw n p z hz : ProbabilityMeasure (Bool × Bool)) :
        Measure (Bool × Bool)).real {b} := by
  have h := abs_conditionalSpecialPairLaw_singleton_sub_quarter_le n p hgood hz b
  rw [abs_le] at h
  linarith

open Classical in
/-- On a good `Z` fiber, the conditional protocol-error probability is at least
`1 / 4 - 2 * γ`. If the protocol output on the fiber is `true`, then the `(true, true)` special
bit-pair witnesses errors; otherwise `(false, false)` witnesses errors. -/
theorem quarter_sub_two_mul_le_zFiberMeasure_protocolErrorEvent
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {γ : ℝ} {ω : HardSample n}
    (hgood : goodZ n p γ (zVariable n p ω))
    (hz : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {zVariable n p ω}) ≠ 0) :
    (1 / 4 : ℝ) - 2 * γ ≤
      (zFiberMeasure n p (zVariable n p ω)).real (protocolErrorEvent n p) := by
  haveI : IsFiniteMeasure (zFiberMeasure n p (zVariable n p ω)) := by
    rw [zFiberMeasure]
    infer_instance
  by_cases hrun : p.run (X n ω) (Y n ω) = true
  · have hmass :=
      quarter_sub_two_mul_le_conditionalSpecialPairLaw_singleton n p hgood hz (true, true)
    have hsubset :
        ((zVariable n p) ⁻¹' {zVariable n p ω}) ∩
            ((specialPair n) ⁻¹' {((true, true) : Bool × Bool)}) ⊆
          protocolErrorEvent n p := by
      intro ω' hω'
      have hzEq : zVariable n p ω' = zVariable n p ω := by
        simpa using hω'.1
      have hrun' : p.run (X n ω') (Y n ω') = true := by
        have hrunEq :=
          Deterministic.Protocol.run_eq_of_transcript_eq p (congrArg Prod.fst hzEq)
        simpa [input] using hrunEq.trans hrun
      have hbits : ω'.xT = true ∧ ω'.yT = true := by
        have hpair : specialPair n ω' = (true, true) := by
          simpa using hω'.2
        simpa [specialPair, specialX, specialY] using hpair
      have hnot_disj : ¬Disjoint (X n ω') (Y n ω') := by
        rw [disjoint_X_Y_iff]
        exact not_not_intro hbits
      simp [protocolErrorEvent, disjointness, hrun', hnot_disj]
    have hmono :
        (zFiberMeasure n p (zVariable n p ω)).real
            (((zVariable n p) ⁻¹' {zVariable n p ω}) ∩
              ((specialPair n) ⁻¹' {((true, true) : Bool × Bool)})) ≤
          (zFiberMeasure n p (zVariable n p ω)).real (protocolErrorEvent n p) :=
      measureReal_mono hsubset
    rw [zFiberMeasure_inter_fiber] at hmono
    rw [← conditionalSpecialPairLaw_singleton n p (zVariable n p ω) hz (true, true)] at hmono
    exact hmass.trans hmono
  · have hrun_false : p.run (X n ω) (Y n ω) = false := by
      cases h : p.run (X n ω) (Y n ω) <;> simp_all
    have hmass :=
      quarter_sub_two_mul_le_conditionalSpecialPairLaw_singleton n p hgood hz (false, false)
    have hsubset :
        ((zVariable n p) ⁻¹' {zVariable n p ω}) ∩
            ((specialPair n) ⁻¹' {((false, false) : Bool × Bool)}) ⊆
          protocolErrorEvent n p := by
      intro ω' hω'
      have hzEq : zVariable n p ω' = zVariable n p ω := by
        simpa using hω'.1
      have hrun' : p.run (X n ω') (Y n ω') = false := by
        have hrunEq :=
          Deterministic.Protocol.run_eq_of_transcript_eq p (congrArg Prod.fst hzEq)
        simpa [input] using hrunEq.trans hrun_false
      have hbits : ω'.xT = false ∧ ω'.yT = false := by
        have hpair : specialPair n ω' = (false, false) := by
          simpa using hω'.2
        simpa [specialPair, specialX, specialY] using hpair
      have hdisj : Disjoint (X n ω') (Y n ω') := by
        rw [disjoint_X_Y_iff]
        intro hboth
        rw [hbits.1] at hboth
        simp at hboth
      simp [protocolErrorEvent, disjointness, hrun', hdisj]
    have hmono :
        (zFiberMeasure n p (zVariable n p ω)).real
            (((zVariable n p) ⁻¹' {zVariable n p ω}) ∩
              ((specialPair n) ⁻¹' {((false, false) : Bool × Bool)})) ≤
          (zFiberMeasure n p (zVariable n p ω)).real (protocolErrorEvent n p) :=
      measureReal_mono hsubset
    rw [zFiberMeasure_inter_fiber] at hmono
    rw [← conditionalSpecialPairLaw_singleton n p (zVariable n p ω) hz (false, false)] at hmono
    exact hmass.trans hmono

open Classical in
/-- Averaging the good-fiber error lower bound over all good `Z` fibers gives an unconditional
error lower bound. -/
theorem goodZEvent_mul_quarter_sub_two_mul_le_protocolErrorEvent
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (γ : ℝ) :
    (volume : Measure (HardSample n)).real (goodZEvent n p γ) *
        ((1 / 4 : ℝ) - 2 * γ) ≤
      (volume : Measure (HardSample n)).real (protocolErrorEvent n p) := by
  rw [protocolErrorEvent_measureReal_eq_sum_zFiberMeasure_real]
  rw [goodZEvent_measureReal_eq_sum_zFibers]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro z _
  by_cases hgood : goodZ n p γ z
  · by_cases hz0 : (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {z}) = 0
    · have hz0_real :
          (volume : Measure (HardSample n)).real ((zVariable n p) ⁻¹' {z}) = 0 := by
        simp [Measure.real, hz0]
      simp [hgood, hz0_real]
    · have hfiber_nonneg :
          0 ≤ (volume : Measure (HardSample n)).real ((zVariable n p) ⁻¹' {z}) :=
        measureReal_nonneg
      have herror :
          (1 / 4 : ℝ) - 2 * γ ≤
            (zFiberMeasure n p z).real (protocolErrorEvent n p) := by
        rcases nonempty_of_measure_ne_zero hz0 with ⟨ω, hωmem⟩
        have hω : zVariable n p ω = z := by
          simpa using hωmem
        have hzω :
            (volume : Measure (HardSample n)) ((zVariable n p) ⁻¹' {zVariable n p ω}) ≠ 0 := by
          simpa [hω] using hz0
        have hbound :=
          quarter_sub_two_mul_le_zFiberMeasure_protocolErrorEvent n p
            (by simpa [hω] using hgood) hzω
        simpa [hω] using hbound
      have hmul := mul_le_mul_of_nonneg_left herror hfiber_nonneg
      simpa [hgood] using hmul
  · have hmul_nonneg :
        0 ≤ (volume : Measure (HardSample n)).real ((zVariable n p) ⁻¹' {z}) *
            (zFiberMeasure n p z).real (protocolErrorEvent n p) :=
      mul_nonneg measureReal_nonneg measureReal_nonneg
    simpa [hgood] using hmul_nonneg

open Classical in
/-- Local form of the final error calculation after Claim 6.21: the error mass inside the good
`Z` fibers is at least the good-fiber mass times `1 / 4 - 2γ`.  This is the step in the textbook
where the transcript output is fixed on each `Z=z` fiber and the good fiber has
`Pr[(X_T,Y_T)=(1,1)] ≥ 1 / 4 - 2γ`. -/
theorem protocolErrorEvent_measureReal_lower_bound_of_goodZEvent
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {γ : ℝ}
    (_hγ : 0 ≤ γ)
    (_hγ_small : γ ≤ 1 / 8) :
    (volume : Measure (HardSample n)).real (goodZEvent n p γ) *
        ((1 / 4 : ℝ) - 2 * γ) ≤
      (volume : Measure (HardSample n)).real (protocolErrorEvent n p) := by
  exact goodZEvent_mul_quarter_sub_two_mul_le_protocolErrorEvent n p γ

open Classical in
/-- The final error calculation after Claim 6.21, phrased using distributional error. -/
theorem distributionalError_lower_bound_of_goodZEvent
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    {γ : ℝ}
    (hγ : 0 ≤ γ)
    (hγ_small : γ ≤ 1 / 8) :
    (volume : Measure (HardSample n)).real (goodZEvent n p γ) *
        ((1 / 4 : ℝ) - 2 * γ) ≤
      p.distributionalError (inputDist n) (disjointness n) := by
  rw [distributionalError_inputDist_eq_protocolErrorEvent]
  exact protocolErrorEvent_measureReal_lower_bound_of_goodZEvent n p hγ hγ_small

/-- The concrete constant calculation used to turn Claim 6.21 into a fixed information lower
bound. -/
theorem textbook_error_lower_bound_at_one_over_sixty_four :
    ((1 / 4 : ℝ) * (1 - 4 * (1 / 64 : ℝ))) *
        ((1 / 4 : ℝ) - 2 * (1 / 64 : ℝ)) > 1 / 32 := by
  norm_num

open Classical in
/-- Textbook Claim 6.21 and the final error calculation: a deterministic protocol with
distributional error at most `1 / 32` must reveal a constant amount of the corrected information
from (6.6). -/
theorem fixed_error_claimInfo_lower_bound
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (herror : p.distributionalError (inputDist n) (disjointness n) ≤ 1 / 32) :
    (1 / 32768 : ℝ) ^ 2 < claimInfo n p := by
  by_contra hnot
  have hinfo_sq : claimInfo n p ≤ (1 / 32768 : ℝ) ^ 2 := le_of_not_gt hnot
  have hinfo : claimInfo n p ≤ 2 * (1 / 64 : ℝ) ^ 4 / 3 := by
    have hconst : (1 / 32768 : ℝ) ^ 2 ≤ 2 * (1 / 64 : ℝ) ^ 4 / 3 := by
      norm_num
    exact hinfo_sq.trans hconst
  have hgood :=
    textbook_claim_6_21 n p (γ := (1 / 64 : ℝ)) (by norm_num) hinfo
  have herror_lower :=
    distributionalError_lower_bound_of_goodZEvent n p
      (γ := (1 / 64 : ℝ)) (by norm_num) (by norm_num)
  have hfactor_nonneg : 0 ≤ (1 / 4 : ℝ) - 2 * (1 / 64 : ℝ) := by
    norm_num
  have hmul :
      ((1 / 4 : ℝ) * (1 - 4 * (1 / 64 : ℝ))) *
          ((1 / 4 : ℝ) - 2 * (1 / 64 : ℝ)) ≤
        (volume : Measure (HardSample n)).real (goodZEvent n p (1 / 64 : ℝ)) *
          ((1 / 4 : ℝ) - 2 * (1 / 64 : ℝ)) :=
    mul_le_mul_of_nonneg_right hgood hfactor_nonneg
  have hgt := textbook_error_lower_bound_at_one_over_sixty_four
  linarith

/-- Deterministic fixed-error disjointness lower bound from (6.6) and Lemma 6.20. -/
theorem deterministic_complexity_lower_bound_textbook
    (p : Deterministic.Protocol (Set (Fin n)) (Set (Fin n)) Bool)
    (herror : p.distributionalError (inputDist n) (disjointness n) ≤ 1 / 32) :
    ((1 / 32768 : ℝ) ^ 2) * (n : ℝ) / (3 * Real.log 2) ≤ p.complexity := by
  have hinfo_lt := fixed_error_claimInfo_lower_bound n p herror
  have hupper := claimInfo_le_average_info_upper n p
  have hmain :
      (1 / 32768 : ℝ) ^ 2 < 2 * (p.complexity * Real.log 2) / (n : ℝ) :=
    hinfo_lt.trans_le hupper
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast n.pos
  have hlog_pos : 0 < 3 * Real.log 2 := by
    positivity
  have hcomplexity_nonneg : 0 ≤ (p.complexity : ℝ) := by
    exact_mod_cast Nat.zero_le p.complexity
  rw [div_le_iff₀ hlog_pos]
  rw [lt_div_iff₀ hn_pos] at hmain
  nlinarith

/-- Public-coin fixed-error lower bound from the textbook deterministic distributional lower
bound via minimax. -/
theorem publicCoin_lower_bound_textbook
    {k : ℕ}
    (hk : (k : ℝ) <
      ((1 / 32768 : ℝ) ^ 2) * (n : ℝ) / (3 * Real.log 2)) :
    k < PublicCoin.communicationComplexity (disjointness n) (1 / 32 : ℝ) := by
  refine PublicCoin.minimax_lower_bound
    (f := disjointness n) (ε := (1 / 32 : ℝ)) (n := k) (μ := inputDist n) ?_
  intro p hp
  by_contra hnot
  have herror : p.distributionalError (inputDist n) (disjointness n) ≤ 1 / 32 :=
    le_of_not_gt hnot
  have hlower := deterministic_complexity_lower_bound_textbook n p herror
  have hcomplexity_real : (p.complexity : ℝ) ≤ k := by
    exact_mod_cast hp
  linarith

/-- Headline theorem: public-coin randomized communication complexity of disjointness is linear at
fixed error `1 / 32`, with a concrete conservative constant. -/
theorem publicCoin_communicationComplexity_disjointness_linear_lower_bound
    {k : ℕ}
    (hk : (k : ℝ) <
      ((1 / 32768 : ℝ) ^ 2) * (n : ℝ) / (3 * Real.log 2)) :
    k < PublicCoin.communicationComplexity (disjointness n) (1 / 32 : ℝ) :=
  publicCoin_lower_bound_textbook n hk

end RandomizedLowerBound

end Functions.Disjointness

end CommunicationComplexity
