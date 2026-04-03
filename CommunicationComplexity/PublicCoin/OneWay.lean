import CommunicationComplexity.Deterministic.OneWay
import CommunicationComplexity.PublicCoin.Complexity
import CommunicationComplexity.PublicCoin.FiniteMessage
import CommunicationComplexity.PublicCoin.CoinApproximation
import CommunicationComplexity.FiniteProbabilitySpace
import CommunicationComplexity.CoinTape
import Mathlib.Data.ENat.Lattice

namespace CommunicationComplexity
namespace PublicCoin
namespace OneWay

open MeasureTheory ProbabilityTheory

abbrev Protocol (Ω : Type*) (X Y α : Type*) :=
  CommunicationComplexity.Deterministic.OneWay.Protocol (Ω × X) (Ω × Y) α

namespace Protocol

variable {Ω X Y α : Type*}

/-- Execute a one-way public-coin protocol on inputs `x`, `y` with
shared randomness `ω`. -/
def rrun (p : Protocol Ω X Y α) (x : X) (y : Y) (ω : Ω) : α :=
  p.decode (p.send (ω, x)) (ω, y)

/-- A one-way public-coin protocol `ε`-computes `f` if for every input
pair `(x, y)`, the error probability over shared randomness is at most `ε`. -/
noncomputable def ApproxComputes
    [MeasureSpace Ω]
    (p : Protocol Ω X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y,
    (volume {ω : Ω | p.rrun x y ω ≠ f x y}).toReal ≤ ε

end Protocol

/-- The `ε`-error one-way public-coin communication complexity of `f`,
defined as the minimum one-way message cost over all shared-randomness
protocols that compute `f` with error at most `ε` on every input. -/
noncomputable def communicationComplexity
    {X Y α} (f : X → Y → α) (ε : ℝ) : ENat :=
  ⨅ (n : ℕ)
    (p : Protocol (CoinTape n) X Y α)
    (_ : Protocol.ApproxComputes p f ε),
    (p.cost : ENat)

theorem communicationComplexity_le_iff
    {X Y α} (f : X → Y → α) (ε : ℝ) (m : ℕ) :
    communicationComplexity f ε ≤ m ↔
      ∃ (n : ℕ) (p : Protocol (CoinTape n) X Y α),
        Protocol.ApproxComputes p f ε ∧
        p.cost ≤ m := by
  unfold communicationComplexity
  simp only [Internal.enat_iInf_le_coe_iff, Nat.cast_le, exists_prop]

theorem le_communicationComplexity_iff
    {X Y α} (f : X → Y → α) (ε : ℝ) (m : ℕ) :
    (m : ENat) ≤ communicationComplexity f ε ↔
      ∀ (n : ℕ) (p : Protocol (CoinTape n) X Y α),
        Protocol.ApproxComputes p f ε →
        m ≤ p.cost := by
  unfold communicationComplexity
  simp only [le_iInf_iff, Nat.cast_le]

theorem communicationComplexity_mono
    {X Y α} (f : X → Y → α) {ε ε' : ℝ} (h : ε' ≤ ε) :
    communicationComplexity f ε ≤ communicationComplexity f ε' := by
  match hm : communicationComplexity f ε' with
  | ⊤ => exact le_top
  | (m : ℕ) =>
    obtain ⟨n, p, hp, hc⟩ :=
      (communicationComplexity_le_iff f ε' m).mp (le_of_eq hm)
    exact (communicationComplexity_le_iff f ε m).mpr
      ⟨n, p, fun x y => le_trans (hp x y) h, hc⟩

end OneWay
end PublicCoin
end CommunicationComplexity
