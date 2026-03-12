import Mathlib
import CommunicationComplexity.Det.Basic
import CommunicationComplexity.Det.Generalized
import CommunicationComplexity.Rand.Basic

noncomputable def deterministic_communication_complexity {X Y α} (f : X → Y → α) : ℕ :=
  sInf { n | ∃ p : DetProtocol X Y α, p.computes f ∧ p.complexity ≤ n }

noncomputable def randomized_communication_complexity {X Y α} (f : X → Y → α) (ε : ℝ) : ℕ :=
  sInf { n | ∃ p : RandProtocol _ _ X Y α, p.approx_computes f ε ∧ p.complexity ≤ n }
