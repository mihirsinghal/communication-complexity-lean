import CommunicationComplexity.FiniteProbabilitySpace
import Mathlib.InformationTheory.KullbackLeibler.Basic

open MeasureTheory

open scoped ENNReal

/-!
# KL Divergence

This file imports Mathlib's Kullback-Leibler divergence development for use in the project.
-/

namespace CommunicationComplexity

open Classical in
/-- On a finite measurable space, the Kullback-Leibler divergence between finite measures is the
finite sum of the log-likelihood ratio against the singleton masses, with Mathlib's finite-measure
correction term. -/
private theorem klDiv_eq_sum_llr_of_ac
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ≪ ν) :
    InformationTheory.klDiv μ ν =
      ENNReal.ofReal
        (∑ ω : Ω, μ.real ({ω} : Set Ω) * llr μ ν ω + ν.real Set.univ - μ.real Set.univ) := by
  have h_int : Integrable (llr μ ν) μ := Integrable.of_finite
  rw [InformationTheory.klDiv_of_ac_of_integrable h_ac h_int]
  congr 1
  rw [MeasureTheory.integral_fintype (llr μ ν) h_int]
  simp [smul_eq_mul]

open Classical in
/-- On a finite measurable space, the Kullback-Leibler divergence between finite measures is `∞`
exactly in the displayed formula when some singleton has zero `ν`-mass and nonzero `μ`-mass;
otherwise it is the finite sum of the log-likelihood ratio against the singleton masses, with
Mathlib's finite-measure correction term. -/
theorem FiniteMeasureSpace.klDiv_eq_sum_llr
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    InformationTheory.klDiv μ ν =
      if ∃ ω, ν ({ω} : Set Ω) = 0 ∧ μ ({ω} : Set Ω) ≠ 0 then ∞
      else ENNReal.ofReal
        (∑ ω : Ω, μ.real ({ω} : Set Ω) * llr μ ν ω + ν.real Set.univ - μ.real Set.univ) := by
  by_cases hbad : ∃ ω, ν ({ω} : Set Ω) = 0 ∧ μ ({ω} : Set Ω) ≠ 0
  · rw [if_pos hbad]
    apply InformationTheory.klDiv_of_not_ac
    intro h_ac
    rw [FiniteMeasureSpace.absolutelyContinuous_iff_forall_singletons] at h_ac
    rcases hbad with ⟨ω, hν, hμ⟩
    exact hμ (h_ac ω hν)
  · rw [if_neg hbad]
    have h_ac : μ ≪ ν := by
      rw [FiniteMeasureSpace.absolutelyContinuous_iff_forall_singletons]
      intro ω hν
      by_contra hμ
      exact hbad ⟨ω, hν, hμ⟩
    exact klDiv_eq_sum_llr_of_ac μ ν h_ac

open Classical in
/-- On a finite measurable space, the Kullback-Leibler divergence between probability measures is
`∞` if some singleton has zero `ν`-mass and nonzero `μ`-mass; otherwise it is a finite sum over
the PMFs. -/
theorem FiniteMeasureSpace.probabilityMeasure_klDiv_eq_sum_llr
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (μ ν : ProbabilityMeasure Ω) :
    InformationTheory.klDiv (μ : Measure Ω) (ν : Measure Ω) =
      if ∃ ω, (ν : Measure Ω).toPMF ω = 0 ∧ (μ : Measure Ω).toPMF ω ≠ 0 then ∞
      else
      ENNReal.ofReal (∑ ω : Ω,
        ((μ : Measure Ω).toPMF ω).toReal * llr (μ : Measure Ω) (ν : Measure Ω) ω) := by
  rw [FiniteMeasureSpace.klDiv_eq_sum_llr (μ : Measure Ω) (ν : Measure Ω)]
  simp [Measure.toPMF_apply, Measure.real]

open Classical in
/-- On a finite measurable space, the Kullback-Leibler divergence between PMFs is `∞` if some
point has zero `q`-mass and nonzero `p`-mass; otherwise it is a finite sum over the PMFs. -/
theorem FiniteMeasureSpace.pmf_klDiv_eq_sum_llr
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (p q : PMF Ω) :
    InformationTheory.klDiv p.toMeasure q.toMeasure =
      if ∃ ω, q ω = 0 ∧ p ω ≠ 0 then ∞
      else ENNReal.ofReal (∑ ω : Ω, (p ω).toReal * llr p.toMeasure q.toMeasure ω) := by
  simpa [PMF.toProbabilityMeasure] using
    (FiniteMeasureSpace.probabilityMeasure_klDiv_eq_sum_llr
      p.toProbabilityMeasure q.toProbabilityMeasure)

open Classical in
private theorem rnDeriv_toReal_eq_singleton_ratio
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ≪ ν) (ω : Ω)
    (hν : ν ({ω} : Set Ω) ≠ 0) :
    (μ.rnDeriv ν ω).toReal = μ.real ({ω} : Set Ω) / ν.real ({ω} : Set Ω) := by
  have hset := Measure.setIntegral_toReal_rnDeriv h_ac ({ω} : Set Ω)
  rw [MeasureTheory.integral_singleton] at hset
  change ν.real ({ω} : Set Ω) * (μ.rnDeriv ν ω).toReal =
    μ.real ({ω} : Set Ω) at hset
  have hνreal : ν.real ({ω} : Set Ω) ≠ 0 := by
    rwa [MeasureTheory.measureReal_ne_zero_iff (μ := ν) (s := ({ω} : Set Ω))]
  rw [eq_div_iff hνreal]
  rw [mul_comm]
  exact hset

open Classical in
private theorem singleton_mass_mul_llr_eq_log_ratio
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ≪ ν) (ω : Ω) :
    μ.real ({ω} : Set Ω) * llr μ ν ω =
      μ.real ({ω} : Set Ω) *
        Real.log (μ.real ({ω} : Set Ω) / ν.real ({ω} : Set Ω)) := by
  by_cases hμ : μ ({ω} : Set Ω) = 0
  · have hμreal : μ.real ({ω} : Set Ω) = 0 := by
      simp [Measure.real, hμ]
    simp [hμreal]
  · have hν : ν ({ω} : Set Ω) ≠ 0 := by
      intro hν
      exact hμ (h_ac hν)
    simp [llr_def, rnDeriv_toReal_eq_singleton_ratio h_ac ω hν]

open Classical in
/-- On a finite measurable space, the Kullback-Leibler divergence between finite measures is `∞`
if some singleton has zero `ν`-mass and nonzero `μ`-mass; otherwise it is the finite sum of
`μ {ω} * log (μ {ω} / ν {ω})`, with Mathlib's finite-measure correction term. -/
theorem FiniteMeasureSpace.klDiv_eq_sum_log
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    InformationTheory.klDiv μ ν =
      if ∃ ω, ν ({ω} : Set Ω) = 0 ∧ μ ({ω} : Set Ω) ≠ 0 then ∞
      else ENNReal.ofReal
        (∑ ω : Ω,
          μ.real ({ω} : Set Ω) *
            Real.log (μ.real ({ω} : Set Ω) / ν.real ({ω} : Set Ω)) +
            ν.real Set.univ - μ.real Set.univ) := by
  rw [FiniteMeasureSpace.klDiv_eq_sum_llr μ ν]
  split_ifs with hbad
  · rfl
  · have h_ac : μ ≪ ν := by
      rw [FiniteMeasureSpace.absolutelyContinuous_iff_forall_singletons]
      intro ω hν
      by_contra hμ
      exact hbad ⟨ω, hν, hμ⟩
    congr 1
    congr 2
    apply Finset.sum_congr rfl
    intro ω _
    exact singleton_mass_mul_llr_eq_log_ratio h_ac ω

open Classical in
/-- On a finite measurable space, the Kullback-Leibler divergence between probability measures is
`∞` if some singleton has zero `ν`-mass and nonzero `μ`-mass; otherwise it is the finite sum of
`p ω * log (p ω / q ω)`, where `p` and `q` are the PMFs of the two measures. -/
theorem FiniteMeasureSpace.probabilityMeasure_klDiv_eq_sum_log
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (μ ν : ProbabilityMeasure Ω) :
    InformationTheory.klDiv (μ : Measure Ω) (ν : Measure Ω) =
      if ∃ ω, (ν : Measure Ω).toPMF ω = 0 ∧ (μ : Measure Ω).toPMF ω ≠ 0 then ∞
      else ENNReal.ofReal (∑ ω : Ω,
        ((μ : Measure Ω).toPMF ω).toReal *
          Real.log (((μ : Measure Ω).toPMF ω).toReal /
            ((ν : Measure Ω).toPMF ω).toReal)) := by
  rw [FiniteMeasureSpace.klDiv_eq_sum_log (μ : Measure Ω) (ν : Measure Ω)]
  simp [Measure.toPMF_apply, Measure.real]

open Classical in
/-- On a finite space, KL divergence from `μ` to a probability measure with full support is
finite. -/
theorem FiniteMeasureSpace.probabilityMeasure_klDiv_ne_top_of_forall_toPMF_ne_zero
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (μ ν : ProbabilityMeasure Ω)
    (hν : ∀ ω, (ν : Measure Ω).toPMF ω ≠ 0) :
    InformationTheory.klDiv (μ : Measure Ω) (ν : Measure Ω) ≠ ∞ := by
  rw [FiniteMeasureSpace.probabilityMeasure_klDiv_eq_sum_log μ ν]
  rw [if_neg]
  · exact ENNReal.ofReal_ne_top
  · rintro ⟨ω, hνω, -⟩
    exact hν ω hνω

open Classical in
/-- On a finite measurable space, the Kullback-Leibler divergence between PMFs is `∞` if some
point has zero `q`-mass and nonzero `p`-mass; otherwise it is
`∑ ω, p ω * log (p ω / q ω)`. -/
theorem FiniteMeasureSpace.pmf_klDiv_eq_sum_log
    {Ω : Type*} [MeasurableSpace Ω] [FiniteMeasureSpace Ω]
    (p q : PMF Ω) :
    InformationTheory.klDiv p.toMeasure q.toMeasure =
      if ∃ ω, q ω = 0 ∧ p ω ≠ 0 then ∞
      else ENNReal.ofReal (∑ ω : Ω,
        (p ω).toReal * Real.log ((p ω).toReal / (q ω).toReal)) := by
  simpa [PMF.toProbabilityMeasure] using
    (FiniteMeasureSpace.probabilityMeasure_klDiv_eq_sum_log
      p.toProbabilityMeasure q.toProbabilityMeasure)

end CommunicationComplexity
