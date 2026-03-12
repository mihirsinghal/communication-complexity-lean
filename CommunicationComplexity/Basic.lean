import Mathlib
import CommunicationComplexity.Det.Basic
import CommunicationComplexity.Det.Generalized
import CommunicationComplexity.Rand.Basic

open MeasureTheory

noncomputable def deterministic_communication_complexity {X Y α} (f : X → Y → α) : ℕ :=
  sInf { n | ∃ p : DetProtocol X Y α, p.computes f ∧ p.complexity ≤ n }

noncomputable def randomized_communication_complexity {X Y α} (f : X → Y → α) (ε : ℝ) : ℕ :=
  sInf { n | ∃ (Ω_X Ω_Y : Type*) (mX : MeasureSpace Ω_X) (mY : MeasureSpace Ω_Y)
    (_ : @MeasureTheory.IsProbabilityMeasure Ω_X mX.toMeasurableSpace mX.volume)
    (_ : @MeasureTheory.IsProbabilityMeasure Ω_Y mY.toMeasurableSpace mY.volume)
    (p : @RandProtocol Ω_X Ω_Y mX mY _ _ X Y α),
    p.approx_computes f ε ∧ p.complexity ≤ n }
