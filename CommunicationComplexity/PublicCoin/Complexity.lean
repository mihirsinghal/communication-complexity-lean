import CommunicationComplexity.Deterministic.Complexity
import CommunicationComplexity.PublicCoin.Basic
import CommunicationComplexity.PublicCoin.FiniteMessage
import CommunicationComplexity.PublicCoin.GeneralFiniteMessage

namespace CommunicationComplexity

open MeasureTheory ProbabilityTheory

namespace PublicCoin

open Classical in
/-- The `ε`-error public-coin randomized communication complexity of `f`,
defined as the minimum worst-case number of bits exchanged over all
public-coin randomized protocols that compute `f` with error at most
`ε` on every input. -/
noncomputable def communicationComplexity
    {X Y α} (f : X → Y → α) (ε : ℝ) : ENat :=
  ⨅ (n : ℕ)
    (p : Protocol n X Y α)
    (_ : p.approx_computes f ε),
    (p.complexity : ENat)

theorem communicationComplexity_le_iff
    {X Y α} (f : X → Y → α) (ε : ℝ) (m : ℕ) :
    communicationComplexity f ε ≤ m ↔
      ∃ (n : ℕ) (p : Protocol n X Y α),
        p.approx_computes f ε ∧
        p.complexity ≤ m := by
  unfold communicationComplexity
  simp only [Internal.enat_iInf_le_coe_iff, Nat.cast_le, exists_prop]

theorem le_communicationComplexity_iff
    {X Y α} (f : X → Y → α) (ε : ℝ) (m : ℕ) :
    (m : ENat) ≤ communicationComplexity f ε ↔
      ∀ (n : ℕ) (p : Protocol n X Y α),
        p.approx_computes f ε →
        m ≤ p.complexity := by
  unfold communicationComplexity
  simp only [le_iInf_iff, Nat.cast_le]

/-- Communication complexity is monotone in ε: allowing more error can
only make computation easier. -/
theorem communicationComplexity_mono
    {X Y α} (f : X → Y → α) {ε ε' : ℝ} (h : ε' ≤ ε) :
    communicationComplexity f ε ≤ communicationComplexity f ε' := by
  match hm : communicationComplexity f ε' with
  | ⊤ => exact le_top
  | (m : ℕ) =>
    obtain ⟨n, p, hp, hc⟩ := (communicationComplexity_le_iff f ε' m).mp (le_of_eq hm)
    exact (communicationComplexity_le_iff f ε m).mpr
      ⟨n, p, fun x y => le_trans (hp x y) h, hc⟩

theorem communicationComplexity_le_iff_finiteMessage
    {X Y α} (f : X → Y → α) (ε : ℝ) (m : ℕ) :
    communicationComplexity f ε ≤ m ↔
      ∃ (n : ℕ)
        (p : FiniteMessage.Protocol n X Y α),
        (∀ x y,
          (volume {ω : CoinTape n |
            p.run x y ω ≠ f x y}).toReal
            ≤ ε) ∧
        p.complexity ≤ m := by
  rw [communicationComplexity_le_iff]
  constructor
  · rintro ⟨n, p, hp, hc⟩
    obtain ⟨P, hP_run, hP_comp⟩ :=
      FiniteMessage.Protocol.ofProtocol_equiv p
    refine ⟨n, P, ?_, hP_comp ▸ hc⟩
    intro x y; simp_rw [hP_run]; exact hp x y
  · rintro ⟨n, p, hp, hc⟩
    obtain ⟨P, hP_run, hP_comp⟩ :=
      FiniteMessage.Protocol.toProtocol p
    refine ⟨n, P, ?_, hP_comp ▸ hc⟩
    intro x y; simp_rw [hP_run]; exact hp x y

/-- If a general public-coin finite-message protocol ε'-computes f
with ε' < ε, then the public-coin communication complexity at error ε
is at most the protocol's complexity. -/
theorem communicationComplexity_le_of_generalFiniteMessage
    {X Y α} {Ω : Type*} [Fintype Ω]
    [MeasureSpace Ω] [DiscreteMeasurableSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    (f : X → Y → α) (ε ε' : ℝ) (hε : ε' < ε)
    (p : PublicCoin.GeneralFiniteMessage.Protocol Ω X Y α)
    (hp : p.approx_computes f ε') :
    PublicCoin.communicationComplexity f ε ≤ p.complexity := by
  rw [PublicCoin.communicationComplexity_le_iff_finiteMessage]
  rw [PublicCoin.GeneralFiniteMessage.Protocol.approx_computes_eq_approx_satisfies] at hp
  obtain ⟨n, q, hq, hc⟩ :=
    PublicCoin.GeneralFiniteMessage.Protocol.approx_satisfies_finiteMessage
      p _ ε' ε hε hp
  exact ⟨n, q, fun x y => hq x y, le_of_eq hc⟩

end PublicCoin

end CommunicationComplexity
