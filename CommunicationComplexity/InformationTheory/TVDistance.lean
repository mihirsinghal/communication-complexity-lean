import CommunicationComplexity.FiniteProbabilitySpace
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.Tactic

/-!
# Total Variation Distance

This file defines total variation distance between probability measures and relates it to the
usual finite sum formula on finite measurable spaces.
-/

open MeasureTheory

namespace CommunicationComplexity

/-- The signed difference between two probability measures. -/
noncomputable def signedMeasureDiff {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : ProbabilityMeasure Ω) : SignedMeasure Ω :=
  (μ : Measure Ω).toSignedMeasure - (ν : Measure Ω).toSignedMeasure

/-- Total variation distance between probability measures, defined using the total variation of
the signed measure `μ - ν`. -/
noncomputable def tvDistance {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : ProbabilityMeasure Ω) : ℝ :=
  (1 / 2 : ℝ) * (signedMeasureDiff μ ν).totalVariation.real Set.univ

/-- Total variation distance between probability measures, defined as the supremum over
measurable events. -/
noncomputable def tvDistanceSup {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : ProbabilityMeasure Ω) : ℝ :=
  sSup (Set.range fun S : {S : Set Ω // MeasurableSet S} =>
    |(μ : Measure Ω).real (S : Set Ω) - (ν : Measure Ω).real (S : Set Ω)|)

namespace TVDistance

private lemma signedMeasure_apply_eq_posPart_sub_negPart
    {Ω : Type*} [MeasurableSpace Ω] (s : SignedMeasure Ω)
    {S : Set Ω} (hS : MeasurableSet S) :
    s S =
      s.toJordanDecomposition.posPart.real S -
        s.toJordanDecomposition.negPart.real S := by
  conv_lhs => rw [← SignedMeasure.toSignedMeasure_toJordanDecomposition s]
  rw [JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_sub_apply hS]

private lemma signedMeasureDiff_univ
    {Ω : Type*} [MeasurableSpace Ω] (μ ν : ProbabilityMeasure Ω) :
    signedMeasureDiff μ ν Set.univ = 0 := by
  rw [signedMeasureDiff, Measure.toSignedMeasure_sub_apply MeasurableSet.univ]
  simp

private lemma jordan_posPart_real_univ_eq_negPart_real_univ
    {Ω : Type*} [MeasurableSpace Ω] (μ ν : ProbabilityMeasure Ω) :
    (signedMeasureDiff μ ν).toJordanDecomposition.posPart.real Set.univ =
      (signedMeasureDiff μ ν).toJordanDecomposition.negPart.real Set.univ := by
  have h := signedMeasure_apply_eq_posPart_sub_negPart (signedMeasureDiff μ ν) MeasurableSet.univ
  rw [signedMeasureDiff_univ μ ν] at h
  linarith

private lemma totalVariation_real_univ
    {Ω : Type*} [MeasurableSpace Ω] (s : SignedMeasure Ω) :
    s.totalVariation.real Set.univ =
      s.toJordanDecomposition.posPart.real Set.univ +
        s.toJordanDecomposition.negPart.real Set.univ := by
  rw [SignedMeasure.totalVariation, measureReal_add_apply]

private lemma half_totalVariation_real_univ_eq_posPart_real_univ
    {Ω : Type*} [MeasurableSpace Ω] (μ ν : ProbabilityMeasure Ω) :
    (1 / 2 : ℝ) * (signedMeasureDiff μ ν).totalVariation.real Set.univ =
      (signedMeasureDiff μ ν).toJordanDecomposition.posPart.real Set.univ := by
  rw [totalVariation_real_univ]
  rw [jordan_posPart_real_univ_eq_negPart_real_univ μ ν]
  ring

private lemma event_abs_signedMeasureDiff_le_half_totalVariation
    {Ω : Type*} [MeasurableSpace Ω] (μ ν : ProbabilityMeasure Ω)
    (S : {S : Set Ω // MeasurableSet S}) :
    |signedMeasureDiff μ ν (S : Set Ω)| ≤
      (1 / 2 : ℝ) * (signedMeasureDiff μ ν).totalVariation.real Set.univ := by
  let P := (signedMeasureDiff μ ν).toJordanDecomposition.posPart
  let N := (signedMeasureDiff μ ν).toJordanDecomposition.negPart
  have hPN : P.real Set.univ = N.real Set.univ := by
    simpa [P, N] using jordan_posPart_real_univ_eq_negPart_real_univ μ ν
  have hPmono : P.real (S : Set Ω) ≤ P.real Set.univ := measureReal_mono (Set.subset_univ _)
  have hNmono : N.real (S : Set Ω) ≤ N.real Set.univ := measureReal_mono (Set.subset_univ _)
  have hPnonneg : 0 ≤ P.real (S : Set Ω) := measureReal_nonneg
  have hNnonneg : 0 ≤ N.real (S : Set Ω) := measureReal_nonneg
  have hbound :
      |P.real (S : Set Ω) - N.real (S : Set Ω)| ≤ P.real Set.univ := by
    rw [abs_le]
    constructor <;> linarith
  rw [half_totalVariation_real_univ_eq_posPart_real_univ μ ν]
  rw [signedMeasure_apply_eq_posPart_sub_negPart (signedMeasureDiff μ ν) S.property]
  simpa [P, N] using hbound

private lemma event_abs_measureReal_sub_le_half_totalVariation
    {Ω : Type*} [MeasurableSpace Ω] (μ ν : ProbabilityMeasure Ω)
    (S : {S : Set Ω // MeasurableSet S}) :
    |(μ : Measure Ω).real (S : Set Ω) - (ν : Measure Ω).real (S : Set Ω)| ≤
      (1 / 2 : ℝ) * (signedMeasureDiff μ ν).totalVariation.real Set.univ := by
  rw [← Measure.toSignedMeasure_sub_apply S.property]
  exact event_abs_signedMeasureDiff_le_half_totalVariation μ ν S

private lemma exists_event_abs_signedMeasureDiff_eq_half_totalVariation
    {Ω : Type*} [MeasurableSpace Ω] (μ ν : ProbabilityMeasure Ω) :
    ∃ S : {S : Set Ω // MeasurableSet S},
      |signedMeasureDiff μ ν (S : Set Ω)| =
        (1 / 2 : ℝ) * (signedMeasureDiff μ ν).totalVariation.real Set.univ := by
  let s := signedMeasureDiff μ ν
  obtain ⟨S, hS, -, -, hPzero, hNzero⟩ :=
    s.toJordanDecomposition.exists_compl_positive_negative
  refine ⟨⟨Sᶜ, hS.compl⟩, ?_⟩
  let P := s.toJordanDecomposition.posPart
  let N := s.toJordanDecomposition.negPart
  have hPzero_real : P.real S = 0 := by
    rw [measureReal_def, show P S = 0 by simpa [P] using hPzero, ENNReal.toReal_zero]
  have hPcompl : P.real Sᶜ = P.real Set.univ := by
    rw [measureReal_compl hS, hPzero_real]
    ring
  have hNcompl : N.real Sᶜ = 0 := by
    rw [measureReal_def, hNzero, ENNReal.toReal_zero]
  have hnonneg : 0 ≤ P.real Set.univ := measureReal_nonneg
  rw [signedMeasure_apply_eq_posPart_sub_negPart s hS.compl]
  rw [half_totalVariation_real_univ_eq_posPart_real_univ μ ν]
  simp [s, P, N, hPcompl, hNcompl, abs_of_nonneg hnonneg]

private lemma exists_event_abs_measureReal_sub_eq_half_totalVariation
    {Ω : Type*} [MeasurableSpace Ω] (μ ν : ProbabilityMeasure Ω) :
    ∃ S : {S : Set Ω // MeasurableSet S},
      |(μ : Measure Ω).real (S : Set Ω) - (ν : Measure Ω).real (S : Set Ω)| =
        (1 / 2 : ℝ) * (signedMeasureDiff μ ν).totalVariation.real Set.univ := by
  obtain ⟨S, hS⟩ := exists_event_abs_signedMeasureDiff_eq_half_totalVariation μ ν
  refine ⟨S, ?_⟩
  rw [← Measure.toSignedMeasure_sub_apply S.property]
  exact hS

open Classical in
/-- The total-variation-mass definition agrees with the supremum-over-events definition. -/
theorem tvDistance_eq_tvDistanceSup
    {Ω : Type*} [MeasurableSpace Ω] (μ ν : ProbabilityMeasure Ω) :
    tvDistance μ ν = tvDistanceSup μ ν := by
  let rhs : ℝ := (1 / 2 : ℝ) * (signedMeasureDiff μ ν).totalVariation.real Set.univ
  have hset_le (S : {S : Set Ω // MeasurableSet S}) :
      |(μ : Measure Ω).real (S : Set Ω) - (ν : Measure Ω).real (S : Set Ω)| ≤ rhs := by
    simpa [rhs] using event_abs_measureReal_sub_le_half_totalVariation μ ν S
  have hrhs_nonneg : 0 ≤ rhs := by
    dsimp [rhs]
    positivity
  have hupper : tvDistanceSup μ ν ≤ rhs := by
    rw [tvDistanceSup]
    exact Real.sSup_le (by rintro _ ⟨S, rfl⟩; exact hset_le S) hrhs_nonneg
  obtain ⟨Smax, hSmax⟩ := exists_event_abs_measureReal_sub_eq_half_totalVariation μ ν
  have hbdd :
      BddAbove (Set.range fun S : {S : Set Ω // MeasurableSet S} =>
        |(μ : Measure Ω).real (S : Set Ω) - (ν : Measure Ω).real (S : Set Ω)|) := by
    exact ⟨rhs, by rintro _ ⟨S, rfl⟩; exact hset_le S⟩
  have hlower : rhs ≤ tvDistanceSup μ ν := by
    rw [tvDistanceSup]
    dsimp [rhs]
    rw [← hSmax]
    exact le_csSup hbdd (Set.mem_range_self Smax)
  rw [tvDistance]
  exact le_antisymm (by simpa [rhs] using hlower) (by simpa [rhs] using hupper)

/-- The total variation distance bounds the probability gap of every measurable event. -/
theorem abs_measureReal_sub_le_tvDistance
    {Ω : Type*} [MeasurableSpace Ω] (μ ν : ProbabilityMeasure Ω)
    (S : {S : Set Ω // MeasurableSet S}) :
    |(μ : Measure Ω).real (S : Set Ω) - (ν : Measure Ω).real (S : Set Ω)| ≤
      tvDistance μ ν := by
  rw [tvDistance]
  exact event_abs_measureReal_sub_le_half_totalVariation μ ν S

open Classical in
private lemma sum_indicator_le_sum_posPart
    {α : Type*} [Fintype α] (a : α → ℝ) (S : Set α) :
    (∑ x : α, if x ∈ S then a x else 0) ≤
      ∑ x : α, if 0 ≤ a x then a x else 0 := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : x ∈ S
  · by_cases ha : 0 ≤ a x
    · simp [hx, ha]
    · simp [hx, ha, le_of_not_ge ha]
  · by_cases ha : 0 ≤ a x <;> simp [hx, ha]

open Classical in
private lemma sum_posPart_eq_half_sum_abs
    {α : Type*} [Fintype α] (a : α → ℝ)
    (hsum : ∑ x : α, a x = 0) :
    (∑ x : α, if 0 ≤ a x then a x else 0) =
      (1 / 2 : ℝ) * ∑ x : α, |a x| := by
  have habs :
      (∑ x : α, |a x|) =
        ∑ x : α, ((2 : ℝ) * (if 0 ≤ a x then a x else 0) - a x) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases ha : 0 ≤ a x
    · simp [ha, abs_of_nonneg ha]
      ring
    · have hle : a x ≤ 0 := le_of_not_ge ha
      simp [ha, abs_of_nonpos hle]
  have hsum_abs :
      (∑ x : α, |a x|) =
        (2 : ℝ) * ∑ x : α, if 0 ≤ a x then a x else 0 := by
    rw [habs, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum]
    ring
  linarith

open Classical in
private lemma abs_sum_indicator_le_half_sum_abs
    {α : Type*} [Fintype α] (a : α → ℝ)
    (hsum : ∑ x : α, a x = 0) (S : Set α) :
    |∑ x : α, if x ∈ S then a x else 0| ≤
      (1 / 2 : ℝ) * ∑ x : α, |a x| := by
  let posPart : ℝ := ∑ x : α, if 0 ≤ a x then a x else 0
  have hposPart : posPart = (1 / 2 : ℝ) * ∑ x : α, |a x| := by
    simp [posPart, sum_posPart_eq_half_sum_abs a hsum]
  have hupper :
      (∑ x : α, if x ∈ S then a x else 0) ≤ posPart := by
    simpa [posPart] using sum_indicator_le_sum_posPart a S
  have hcomplUpper :
      (∑ x : α, if x ∈ Sᶜ then a x else 0) ≤ posPart := by
    simpa [posPart] using sum_indicator_le_sum_posPart a Sᶜ
  have hdecomp :
      (∑ x : α, a x) =
        (∑ x : α, if x ∈ S then a x else 0) +
          ∑ x : α, if x ∈ Sᶜ then a x else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ S <;> simp [hx]
  have hlower :
      -posPart ≤ ∑ x : α, if x ∈ S then a x else 0 := by
    linarith
  rw [hposPart] at hupper hlower
  exact abs_le.mpr ⟨hlower, hupper⟩

open Classical in
private lemma abs_sum_pos_indicator_eq_half_sum_abs
    {α : Type*} [Fintype α] (a : α → ℝ)
    (hsum : ∑ x : α, a x = 0) :
    |∑ x : α, if 0 ≤ a x then a x else 0| =
      (1 / 2 : ℝ) * ∑ x : α, |a x| := by
  have hnonneg : 0 ≤ ∑ x : α, if 0 ≤ a x then a x else 0 := by
    apply Finset.sum_nonneg
    intro x _
    by_cases hx : 0 ≤ a x <;> simp [hx]
  rw [abs_of_nonneg hnonneg, sum_posPart_eq_half_sum_abs a hsum]

private def singletonMassDiff
    {Ω : Type*} [MeasurableSpace Ω] (μ ν : ProbabilityMeasure Ω) (ω : Ω) : ℝ :=
  (μ : Measure Ω).real ({ω} : Set Ω) - (ν : Measure Ω).real ({ω} : Set Ω)

open Classical in
private lemma measureReal_sub_eq_sum_indicator_singletonMassDiff
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (μ ν : ProbabilityMeasure Ω) (S : Set Ω) :
    (μ : Measure Ω).real S - (ν : Measure Ω).real S =
      ∑ ω : Ω, if ω ∈ S then singletonMassDiff μ ν ω else 0 := by
  rw [FiniteMeasureSpace.probabilityMeasure_measureReal_eq_sum_singletons μ S,
    FiniteMeasureSpace.probabilityMeasure_measureReal_eq_sum_singletons ν S,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hω : ω ∈ S <;> simp [singletonMassDiff, hω]

private lemma sum_singletonMassDiff_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (μ ν : ProbabilityMeasure Ω) :
    ∑ ω : Ω, singletonMassDiff μ ν ω = 0 := by
  classical
  simp_rw [singletonMassDiff]
  rw [Finset.sum_sub_distrib]
  have hμ :=
    FiniteMeasureSpace.probabilityMeasure_measureReal_eq_sum_singletons μ (Set.univ : Set Ω)
  have hν :=
    FiniteMeasureSpace.probabilityMeasure_measureReal_eq_sum_singletons ν (Set.univ : Set Ω)
  simp only [Set.mem_univ, ↓reduceIte] at hμ hν
  rw [← hμ, ← hν]
  simp

open Classical in
/-- On a finite measurable space, total variation distance is half the `ℓ¹` distance between
the singleton masses. -/
theorem tvDistanceSup_eq_half_sum
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (μ ν : ProbabilityMeasure Ω) :
    tvDistanceSup μ ν =
      (1 / 2 : ℝ) *
        ∑ ω : Ω, |(μ : Measure Ω).real ({ω} : Set Ω) -
          (ν : Measure Ω).real ({ω} : Set Ω)| := by
  let rhs : ℝ :=
    (1 / 2 : ℝ) *
      ∑ ω : Ω, |(μ : Measure Ω).real ({ω} : Set Ω) -
        (ν : Measure Ω).real ({ω} : Set Ω)|
  have hsum : ∑ ω : Ω, singletonMassDiff μ ν ω = 0 :=
    sum_singletonMassDiff_eq_zero μ ν
  have hset_le (S : {S : Set Ω // MeasurableSet S}) :
      |(μ : Measure Ω).real (S : Set Ω) - (ν : Measure Ω).real (S : Set Ω)| ≤ rhs := by
    rw [measureReal_sub_eq_sum_indicator_singletonMassDiff μ ν (S : Set Ω)]
    exact abs_sum_indicator_le_half_sum_abs (singletonMassDiff μ ν) hsum (S : Set Ω)
  have hrhs_nonneg : 0 ≤ rhs := by
    dsimp [rhs]
    positivity
  have hupper : tvDistanceSup μ ν ≤ rhs := by
    rw [tvDistanceSup]
    exact Real.sSup_le (by rintro _ ⟨S, rfl⟩; exact hset_le S) hrhs_nonneg
  let Spos : {S : Set Ω // MeasurableSet S} :=
    ⟨{ω | 0 ≤ singletonMassDiff μ ν ω}, MeasurableSet.of_discrete⟩
  have hpos_event :
      |(μ : Measure Ω).real (Spos : Set Ω) - (ν : Measure Ω).real (Spos : Set Ω)| = rhs := by
    rw [measureReal_sub_eq_sum_indicator_singletonMassDiff μ ν (Spos : Set Ω)]
    change |∑ ω : Ω, if 0 ≤ singletonMassDiff μ ν ω then singletonMassDiff μ ν ω else 0| =
      rhs
    rw [abs_sum_pos_indicator_eq_half_sum_abs (singletonMassDiff μ ν) hsum]
    rfl
  have hbdd :
      BddAbove (Set.range fun S : {S : Set Ω // MeasurableSet S} =>
        |(μ : Measure Ω).real (S : Set Ω) - (ν : Measure Ω).real (S : Set Ω)|) := by
    exact ⟨rhs, by rintro _ ⟨S, rfl⟩; exact hset_le S⟩
  have hlower : rhs ≤ tvDistanceSup μ ν := by
    rw [tvDistanceSup]
    rw [← hpos_event]
    exact le_csSup hbdd (Set.mem_range_self Spos)
  exact le_antisymm hupper hlower

open Classical in
/-- On a finite measurable space, total variation distance is half the `ℓ¹` distance between
the singleton masses. -/
theorem tvDistance_eq_half_sum
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (μ ν : ProbabilityMeasure Ω) :
    tvDistance μ ν =
      (1 / 2 : ℝ) *
        ∑ ω : Ω, |(μ : Measure Ω).real ({ω} : Set Ω) -
          (ν : Measure Ω).real ({ω} : Set Ω)| := by
  rw [tvDistance_eq_tvDistanceSup, tvDistanceSup_eq_half_sum]

end TVDistance

end CommunicationComplexity
