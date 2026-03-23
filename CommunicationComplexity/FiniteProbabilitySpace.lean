import Mathlib.Data.Fintype.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.ProbabilityMassFunction.Basic

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

namespace FiniteProbabilitySpace

/-- You usually won't need this theorem explicitly, because of the instance below. -/
theorem nonempty
    (Ω : Type*) [FiniteProbabilitySpace Ω] : Nonempty Ω :=
  MeasureTheory.nonempty_of_isProbabilityMeasure (volume : Measure Ω)

instance (priority := 100) instNonempty
    (Ω : Type*) [FiniteProbabilitySpace Ω] : Nonempty Ω :=
  FiniteProbabilitySpace.nonempty Ω

def toPMF (Ω : Type*) [FiniteProbabilitySpace Ω] : PMF Ω :=
  (volume : Measure Ω).toPMF

open Classical in
theorem measure_eq (Ω : Type*) [FiniteProbabilitySpace Ω] (S : Set Ω) :
    volume S = ∑ ω : S, toPMF Ω ω := by
  have hμ : (toPMF Ω).toMeasure = (volume : Measure Ω) := by
    simp only [toPMF, Measure.toPMF_toMeasure]
  rw [← hμ]
  rw [PMF.toMeasure_apply (p := toPMF Ω) (s := S) MeasurableSet.of_discrete]
  rw [← tsum_subtype S (toPMF Ω), tsum_fintype]

end FiniteProbabilitySpace

end CommunicationComplexity
