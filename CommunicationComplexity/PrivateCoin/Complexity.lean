import CommunicationComplexity.Deterministic.Complexity
import CommunicationComplexity.PrivateCoin.Basic
import CommunicationComplexity.PrivateCoin.FiniteMessage
import CommunicationComplexity.PrivateCoin.GeneralFiniteMessage

namespace CommunicationComplexity

open MeasureTheory ProbabilityTheory

namespace PrivateCoin

open Classical in
/-- The `ε`-error randomized communication complexity of `f`,
defined as the minimum worst-case number of bits exchanged over all
coin-flip randomized protocols that compute `f` with error at most
`ε` on every input. -/
noncomputable def communicationComplexity
    {X Y α} (f : X → Y → α) (ε : ℝ) : ENat :=
  ⨅ (nX : ℕ) (nY : ℕ)
    (p : Protocol nX nY X Y α)
    (_ : p.approx_computes f ε),
    (p.complexity : ENat)

open Classical in
theorem communicationComplexity_le_iff
    {X Y α} (f : X → Y → α) (ε : ℝ) (n : ℕ) :
    communicationComplexity f ε ≤ n ↔
      ∃ (nX nY : ℕ) (p : Protocol nX nY X Y α),
        p.approx_computes f ε ∧
        p.complexity ≤ n := by
  unfold communicationComplexity
  simp only [Internal.enat_iInf_le_coe_iff, Nat.cast_le, exists_prop]

open Classical in
theorem le_communicationComplexity_iff
    {X Y α} (f : X → Y → α) (ε : ℝ) (n : ℕ) :
    (n : ENat) ≤ communicationComplexity f ε ↔
      ∀ (nX nY : ℕ) (p : Protocol nX nY X Y α),
        p.approx_computes f ε →
        n ≤ p.complexity := by
  unfold communicationComplexity
  simp only [le_iInf_iff, Nat.cast_le]

open Classical in
theorem communicationComplexity_le_iff_finiteMessage
    {X Y α} (f : X → Y → α) (ε : ℝ) (n : ℕ) :
    communicationComplexity f ε ≤ n ↔
      ∃ (nX nY : ℕ)
        (p : FiniteMessage.Protocol nX nY X Y α),
        (∀ x y,
          (volume {ω : CoinTape nX × CoinTape nY |
            p.run x y ω.1 ω.2 ≠ f x y}).toReal
            ≤ ε) ∧
        p.complexity ≤ n := by
  rw [communicationComplexity_le_iff]
  constructor
  · rintro ⟨nX, nY, p, hp, hc⟩
    obtain ⟨P, hP_run, hP_comp⟩ :=
      FiniteMessage.Protocol.ofProtocol_equiv p
    refine ⟨nX, nY, P, ?_, hP_comp ▸ hc⟩
    intro x y; simp_rw [hP_run]; exact hp x y
  · rintro ⟨nX, nY, p, hp, hc⟩
    obtain ⟨P, hP_run, hP_comp⟩ :=
      FiniteMessage.Protocol.toProtocol p
    refine ⟨nX, nY, P, ?_, hP_comp ▸ hc⟩
    intro x y; simp_rw [hP_run]; exact hp x y

open Classical in
/-- If a general finite-message protocol ε'-computes f with ε' < ε,
then the private-coin communication complexity at error ε is at most
the protocol's complexity. -/
theorem communicationComplexity_le_of_generalFiniteMessage
    {X Y α} {Ω_X Ω_Y : Type*} [Fintype Ω_X] [Fintype Ω_Y]
    [MeasureSpace Ω_X] [DiscreteMeasurableSpace Ω_X]
    [MeasureSpace Ω_Y] [DiscreteMeasurableSpace Ω_Y]
    [IsProbabilityMeasure (volume : Measure Ω_X)]
    [IsProbabilityMeasure (volume : Measure Ω_Y)]
    (f : X → Y → α) (ε ε' : ℝ) (hε : ε' < ε)
    (p : PrivateCoin.GeneralFiniteMessage.Protocol Ω_X Ω_Y X Y α)
    (hp : p.approx_computes f ε') :
    PrivateCoin.communicationComplexity f ε ≤ p.complexity := by
  rw [PrivateCoin.communicationComplexity_le_iff_finiteMessage]
  -- Convert approx_computes to approx_satisfies
  rw [PrivateCoin.GeneralFiniteMessage.Protocol.approx_computes_eq_approx_satisfies] at hp
  -- Apply the key theorem: get a coin-flip FiniteMessage protocol
  obtain ⟨nX, nY, q, hq, hc⟩ :=
    PrivateCoin.GeneralFiniteMessage.Protocol.approx_satisfies_finiteMessage
      p _ ε' ε hε hp
  exact ⟨nX, nY, q, fun x y => hq x y, le_of_eq hc⟩

end PrivateCoin

end CommunicationComplexity
