import Mathlib.Data.Fintype.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

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

/-- You usually won't need this theorem explicitly, because of the instance below. -/
theorem FiniteProbabilitySpace.nonempty
    (Ω : Type*) [FiniteProbabilitySpace Ω] : Nonempty Ω :=
  MeasureTheory.nonempty_of_isProbabilityMeasure (volume : Measure Ω)

instance (priority := 100) FiniteProbabilitySpace.instNonempty
    (Ω : Type*) [FiniteProbabilitySpace Ω] : Nonempty Ω :=
  FiniteProbabilitySpace.nonempty Ω

end CommunicationComplexity
