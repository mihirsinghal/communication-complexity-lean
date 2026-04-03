import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Measure.Prod
import CommunicationComplexity.FiniteProbabilitySpace

namespace CommunicationComplexity

abbrev CoinTape (n : ℕ) := Fin n → Bool

open MeasureTheory ProbabilityTheory

/-- The uniform probability measure on `CoinTape n`. Every outcome
of `n` independent fair coin flips is equally likely. -/
noncomputable instance coinTapeMeasure (n : ℕ) : MeasureSpace (CoinTape n) where
  volume := uniformOn Set.univ

instance coinTapeIsProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (volume : Measure (CoinTape n)) := by
  change IsProbabilityMeasure (uniformOn Set.univ)
  infer_instance

noncomputable instance coinTapeFiniteProbabilitySpace (n : ℕ) :
    FiniteProbabilitySpace (CoinTape n) :=
  FiniteProbabilitySpace.of (CoinTape n)

end CommunicationComplexity
