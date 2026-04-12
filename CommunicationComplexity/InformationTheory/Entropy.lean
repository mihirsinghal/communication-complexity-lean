import PFR.ForMathlib.Entropy.Basic

/-!
# Entropy

This file imports the entropy definitions and basic API from `PFR.ForMathlib.Entropy.Basic`.

The main definitions live in the `ProbabilityTheory` namespace:

* `ProbabilityTheory.entropy`
* `ProbabilityTheory.condEntropy`
* `ProbabilityTheory.mutualInfo`

It also provides notations such as `H[X]`, `H[X ; μ]`, `H[X | Y]`, and `I[X : Y]`.
-/

namespace ProbabilityTheory

open MeasureTheory

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

/-- Entropy is bounded by the logarithm of any natural-number upper bound on the alphabet size. -/
theorem entropy_le_log_of_card_le [Fintype S] [Nonempty S] [MeasurableSingletonClass S]
    (X : Ω → S) (μ : Measure Ω) {N : ℕ}
    (hcard : Fintype.card S ≤ N) :
    H[X ; μ] ≤ Real.log N := by
  have hcard_pos : 0 < (Fintype.card S : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcard_cast : (Fintype.card S : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hcard
  exact (entropy_le_log_card X μ).trans (Real.log_le_log hcard_pos hcard_cast)

/-- Entropy is bounded by `c * log 2` when the alphabet has size at most `2 ^ c`. -/
theorem entropy_le_nat_mul_log_two_of_card_le_two_pow
    [Fintype S] [Nonempty S] [MeasurableSingletonClass S]
    (X : Ω → S) (μ : Measure Ω) {c : ℕ}
    (hcard : Fintype.card S ≤ 2 ^ c) :
    H[X ; μ] ≤ c * Real.log 2 := by
  simpa [Nat.cast_pow] using entropy_le_log_of_card_le X μ hcard

variable {T U : Type*} [MeasurableSpace T] [MeasurableSpace U]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  [Countable S] [Countable T] [Countable U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}

/-- Mutual information is bounded by the entropy of the left variable. -/
theorem mutualInfo_le_entropy_left
    (hX : Measurable X) (hY : Measurable Y)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    I[X : Y ; μ] ≤ H[X ; μ] := by
  rw [mutualInfo_eq_entropy_sub_condEntropy hX hY]
  linarith [condEntropy_nonneg X Y μ]

/-- Mutual information is bounded by the entropy of the right variable. -/
theorem mutualInfo_le_entropy_right
    (hX : Measurable X) (hY : Measurable Y)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    I[X : Y ; μ] ≤ H[Y ; μ] := by
  rw [mutualInfo_comm hX hY]
  exact mutualInfo_le_entropy_left hY hX

/-- Conditional mutual information is bounded by the left conditional entropy. -/
theorem condMutualInfo_le_condEntropy_left
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    I[X : Y | Z ; μ] ≤ H[X | Z ; μ] := by
  rw [condMutualInfo_eq' hX hY hZ]
  linarith [condEntropy_nonneg X (fun ω => (Y ω, Z ω)) μ]

/-- Conditional mutual information is bounded by the right conditional entropy. -/
theorem condMutualInfo_le_condEntropy_right
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    I[X : Y | Z ; μ] ≤ H[Y | Z ; μ] := by
  rw [condMutualInfo_comm hX hY Z μ]
  exact condMutualInfo_le_condEntropy_left hY hX hZ

/-- Conditional mutual information is bounded by the entropy of the left variable. -/
theorem condMutualInfo_le_entropy_left
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    I[X : Y | Z ; μ] ≤ H[X ; μ] :=
  (condMutualInfo_le_condEntropy_left hX hY hZ).trans
    (condEntropy_le_entropy hX hZ)

/-- Conditional mutual information is bounded by the entropy of the right variable. -/
theorem condMutualInfo_le_entropy_right
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    I[X : Y | Z ; μ] ≤ H[Y ; μ] :=
  (condMutualInfo_le_condEntropy_right hX hY hZ).trans
    (condEntropy_le_entropy hY hZ)

end ProbabilityTheory
