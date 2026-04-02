import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory

namespace CommunicationComplexity

class FiniteProbabilitySpace (Ω : Type*) where
  toMeasureSpace : MeasureSpace Ω
  fintype :
    Fintype Ω
  discrete :
    @DiscreteMeasurableSpace Ω toMeasureSpace.toMeasurableSpace
  prob :
    @IsProbabilityMeasure Ω
      toMeasureSpace.toMeasurableSpace toMeasureSpace.volume

attribute [instance] FiniteProbabilitySpace.toMeasureSpace
attribute [instance] FiniteProbabilitySpace.fintype
attribute [instance] FiniteProbabilitySpace.discrete
attribute [instance] FiniteProbabilitySpace.prob

/-- Helper for bundling already-existing instances locally. -/
def FiniteProbabilitySpace.of
    (Ω : Type*)
    [m : MeasureSpace Ω]
    [Fintype Ω]
    [DiscreteMeasurableSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)] :
    FiniteProbabilitySpace Ω :=
{ toMeasureSpace := m
  fintype := inferInstance
  discrete := inferInstance
  prob := inferInstance }

noncomputable instance instProd (Ω₁ Ω₂ : Type*)
    [FiniteProbabilitySpace Ω₁] [FiniteProbabilitySpace Ω₂] :
    FiniteProbabilitySpace (Ω₁ × Ω₂) :=
  FiniteProbabilitySpace.of (Ω₁ × Ω₂)

open Classical in
noncomputable instance instPi
    {ι : Type*} [Fintype ι] (Ω : ι → Type*)
    [∀ i, FiniteProbabilitySpace (Ω i)] :
    FiniteProbabilitySpace ((i : ι) → Ω i) :=
  FiniteProbabilitySpace.of ((i : ι) → Ω i)

open Classical in
/-- On a finite discrete type with the uniform measure on `Set.univ`,
the real-valued measure of a set is its cardinality divided by the size
of the ambient type. -/
theorem uniformOn_univ_measureReal_eq_card_filter
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω]
    [DiscreteMeasurableSpace Ω] (S : Set Ω) :
    ((ProbabilityTheory.uniformOn Set.univ : Measure Ω) S).toReal =
      ((Finset.univ.filter fun ω : Ω => ω ∈ S).card : ℝ) / Fintype.card Ω := by
  rw [ProbabilityTheory.uniformOn_univ, ENNReal.toReal_div,
    Measure.count_apply MeasurableSet.of_discrete,
    Set.encard_eq_coe_toFinset_card]
  simp [ENat.toENNReal_coe, ENNReal.toReal_natCast]

namespace FiniteProbabilitySpace

/-- You usually won't need this theorem explicitly, because of the instance below. -/
theorem nonempty
    {Ω : Type*} [FiniteProbabilitySpace Ω] : Nonempty Ω :=
  MeasureTheory.nonempty_of_isProbabilityMeasure (volume : Measure Ω)

instance (priority := 100) instNonempty
    (Ω : Type*) [FiniteProbabilitySpace Ω] : Nonempty Ω :=
  FiniteProbabilitySpace.nonempty (Ω := Ω)

def toPMF (Ω : Type*) [FiniteProbabilitySpace Ω] : PMF Ω :=
  (volume : Measure Ω).toPMF

open Classical in
theorem measure_eq {Ω : Type*} [FiniteProbabilitySpace Ω] (S : Set Ω) :
    volume S = ∑ ω : S, toPMF Ω ω := by
  have hμ : (toPMF Ω).toMeasure = (volume : Measure Ω) := by
    simp only [toPMF, Measure.toPMF_toMeasure]
  rw [← hμ]
  rw [PMF.toMeasure_apply (p := toPMF Ω) (s := S) MeasurableSet.of_discrete]
  rw [← tsum_subtype S (toPMF Ω), tsum_fintype]

/-- The singleton masses of a finite probability space sum to `1` along
any finite enumeration. -/
theorem hasSum_measure_singletons
    {Ω α : Type*} [FiniteProbabilitySpace Ω] [Finite α]
    (e : Ω ≃ α) :
    HasSum (fun a : α => volume ({e.symm a} : Set Ω)) 1 := by
  have huniv : (Set.univ : Set Ω) = ⋃ a : α, {e.symm a} := by
    ext x
    simp
  rw [show 1 = volume (Set.univ : Set Ω) from measure_univ.symm]
  rw [huniv]
  rw [measure_iUnion
    (fun a b hab => Set.disjoint_singleton.mpr (e.symm.injective.ne hab))
    (fun _ => MeasurableSet.of_discrete)]
  exact ENNReal.summable.hasSum

theorem pmf_prod {Ω₁ Ω₂ : Type*}
    [FiniteProbabilitySpace Ω₁] [FiniteProbabilitySpace Ω₂] :
    ∀ x y, toPMF (Ω₁ × Ω₂) (x, y) = (toPMF Ω₁ x) * (toPMF Ω₂ y) := by
  intro x y
  -- toPMF Ω (x,y) = volume {(x,y)} = volume ({x} ×ˢ {y}) = volume {x} * volume {y}
  simp only [toPMF, Measure.toPMF_apply]
  rw [show ({(x, y)} : Set (Ω₁ × Ω₂)) = {x} ×ˢ {y} from by ext; simp [Prod.ext_iff]]
  rw [show (volume : Measure (Ω₁ × Ω₂)) = volume.prod volume from rfl]
  rw [Measure.prod_prod]

/-- The real-valued measure of a measurable rectangle in a product
finite probability space factors as the product of the two measures. -/
theorem measureReal_prod
    {Ω₁ Ω₂ : Type*} [FiniteProbabilitySpace Ω₁] [FiniteProbabilitySpace Ω₂]
    (A : Set Ω₁) (B : Set Ω₂) :
    (volume (A ×ˢ B : Set (Ω₁ × Ω₂))).toReal =
      (volume A).toReal * (volume B).toReal := by
  rw [show (volume : Measure (Ω₁ × Ω₂)) = volume.prod volume from rfl]
  rw [Measure.prod_prod, ENNReal.toReal_mul]

/-- The real-valued measure of a finite disjoint union is the sum of
the real-valued measures of its parts. -/
theorem measureReal_iUnion_fintype
    {Ω ι : Type*} [FiniteProbabilitySpace Ω] [Fintype ι]
    (A : ι → Set Ω) (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) :
    (volume (⋃ i, A i)).toReal = ∑ i, (volume (A i)).toReal := by
  rw [measure_iUnion hdisj (fun _ => MeasurableSet.of_discrete),
    tsum_fintype, ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]

/-- The real-valued measure of the preimage of a finite set splits as
a sum over singleton fibers. -/
theorem measureReal_preimage_finset
    {Ξ Ω : Type*} [FiniteProbabilitySpace Ξ]
    [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (φ : Ξ → Ω) (T : Finset Ω) :
    (volume (φ ⁻¹' (↑T : Set Ω) : Set Ξ)).toReal =
      ∑ a ∈ T, (volume (φ ⁻¹' ({a} : Set Ω) : Set Ξ)).toReal := by
  rw [show (φ ⁻¹' (↑T : Set Ω) : Set Ξ) = ⋃ a ∈ T, φ ⁻¹' ({a} : Set Ω) from by
    ext ξ
    simp]
  rw [measure_biUnion_finset
    (fun a _ b _ h => Disjoint.preimage _ (Set.disjoint_singleton.mpr h))
    (fun _ _ => MeasurableSet.of_discrete)]
  rw [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]

/-- The real-valued measure of a finite set splits as a sum over its singleton parts. -/
theorem measureReal_finset
    {Ω : Type*} [FiniteProbabilitySpace Ω] (T : Finset Ω) :
    (volume (↑T : Set Ω)).toReal = ∑ a ∈ T, (volume ({a} : Set Ω)).toReal := by
  simpa using measureReal_preimage_finset (Ξ := Ω) (Ω := Ω) id T

/-- On a finite probability space, integrating a real-valued function is a finite weighted sum. -/
theorem integral_eq_pmf_sum {Ω : Type*} [FiniteProbabilitySpace Ω]
    (f : Ω → ℝ) :
    ∫ ω, f ω = ∑ ω : Ω, (toPMF Ω ω).toReal * f ω := by
  rw [MeasureTheory.integral_fintype f (Integrable.of_finite)]; congr 1

/-- Integrating a function over a coordinate of a finite product space is the same as
integrating it over the original finite probability space. -/
theorem integral_comp_eval
    {ι Ω : Type*} [Fintype ι] [FiniteProbabilitySpace Ω]
    (i : ι) (f : Ω → ℝ) :
    ∫ ωs : (j : ι) → Ω, f (ωs i) = ∫ ω, f ω := by
  let ν : Measure ((j : ι) → Ω) := Measure.pi fun _ : ι => (volume : Measure Ω)
  have hmap := measurePreserving_eval (μ := fun (_ : ι) => (volume : Measure Ω)) i
  have h1 :
      ∫ ωs : (j : ι) → Ω, f (ωs i) ∂ν =
        ∫ ω, f ω ∂(Measure.map (Function.eval i) ν) :=
    (integral_map (measurable_pi_apply i).aemeasurable
      Measurable.of_discrete.aestronglyMeasurable).symm
  simpa [ν, hmap.map_eq] using h1

/-- The real-valued measure of a cylinder set in a finite product probability space is the
product of the real-valued measures of its coordinate slices. -/
theorem measureReal_pi_univ
    {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, FiniteProbabilitySpace (Ω i)]
    (s : ∀ i, Set (Ω i)) :
    (volume (Set.pi Set.univ s : Set ((i : ι) → Ω i))).toReal =
      ∏ i, (volume (s i)).toReal := by
  change (Measure.pi (fun i => (volume : Measure (Ω i))) (Set.pi Set.univ s)).toReal = _
  rw [Measure.pi_pi, ENNReal.toReal_prod]

/-- The real-valued measure of a set is the integral of its indicator. -/
theorem measureReal_eq_integral_indicator_one
    {Ω : Type*} [FiniteProbabilitySpace Ω] (S : Set Ω) :
    (volume S).toReal = ∫ ω, Set.indicator S (1 : Ω → ℝ) ω := by
  rw [MeasureTheory.integral_indicator_one MeasurableSet.of_discrete]
  simp [Measure.real]

open Classical in
/-- The real-valued measure of a set is the integral of the corresponding `0/1` function. -/
theorem measureReal_eq_integral_indicator
    {Ω : Type*} [FiniteProbabilitySpace Ω] (S : Set Ω) :
    (volume S).toReal = ∫ ω, if ω ∈ S then (1 : ℝ) else 0 := by
  have hfun : Set.indicator S (1 : Ω → ℝ) = fun ω => if ω ∈ S then (1 : ℝ) else 0 := by
    funext ω
    by_cases hω : ω ∈ S <;> simp [hω]
  rw [measureReal_eq_integral_indicator_one, hfun]

/-- The weights of a finite probability space sum to `1`. -/
theorem pmf_toReal_sum_eq_one {Ω : Type*} [FiniteProbabilitySpace Ω] :
    ∑ ω : Ω, (toPMF Ω ω).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun _ _ => (PMF.apply_lt_top _ _).ne)]
  conv_lhs => rw [show ∑ ω : Ω, toPMF Ω ω = ∑' ω : Ω, toPMF Ω ω from
    (tsum_fintype _).symm]
  rw [PMF.tsum_coe]; simp

/-- Each weight in a finite probability space is nonnegative. -/
theorem pmf_toReal_nonneg {Ω : Type*} [FiniteProbabilitySpace Ω] (ω : Ω) :
    0 ≤ (toPMF Ω ω).toReal := ENNReal.toReal_nonneg

/-- Some point in a finite probability space has positive probability mass. -/
theorem exists_pmf_toReal_pos {Ω : Type*} [FiniteProbabilitySpace Ω] :
    ∃ ω : Ω, 0 < (toPMF Ω ω).toReal := by
  by_contra h; push_neg at h
  have : ∑ ω : Ω, (toPMF Ω ω).toReal = 0 :=
    Finset.sum_eq_zero (fun ω _ => le_antisymm (h ω) ENNReal.toReal_nonneg)
  linarith [pmf_toReal_sum_eq_one (Ω := Ω)]

/-- If f(x) ≤ c everywhere under a probability measure, then ∫ f ≤ c. -/
theorem integral_le_of_le {Ω : Type*} [FiniteProbabilitySpace Ω]
    {f : Ω → ℝ} {c : ℝ} (hf : ∀ ω, f ω ≤ c) :
    ∫ ω, f ω ≤ c := by
  rw [integral_eq_pmf_sum]
  calc ∑ ω, (toPMF Ω ω).toReal * f ω
      ≤ ∑ ω, (toPMF Ω ω).toReal * c :=
        Finset.sum_le_sum (fun ω _ =>
          mul_le_mul_of_nonneg_left (hf ω) (pmf_toReal_nonneg (Ω := Ω) ω))
    _ = c := by rw [← Finset.sum_mul, pmf_toReal_sum_eq_one (Ω := Ω), one_mul]

/-- If f(x) > c everywhere under a probability measure on a nonempty type,
then ∫ f > c. -/
theorem lt_integral_of_lt {Ω : Type*} [FiniteProbabilitySpace Ω]
    {f : Ω → ℝ} {c : ℝ} (hf : ∀ ω, c < f ω) :
    c < ∫ ω, f ω := by
  rw [integral_eq_pmf_sum]
  obtain ⟨ω₀, hω₀⟩ := exists_pmf_toReal_pos (Ω := Ω)
  calc c = ∑ ω, (toPMF Ω ω).toReal * c := by
        rw [← Finset.sum_mul, pmf_toReal_sum_eq_one (Ω := Ω), one_mul]
    _ < ∑ ω, (toPMF Ω ω).toReal * f ω :=
        Finset.sum_lt_sum
          (fun ω _ => mul_le_mul_of_nonneg_left (hf ω).le (pmf_toReal_nonneg (Ω := Ω) ω))
          ⟨ω₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hf ω₀) hω₀⟩

end FiniteProbabilitySpace

end CommunicationComplexity
