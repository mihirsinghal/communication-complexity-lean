import CommunicationComplexity.PublicCoin.Basic
import CommunicationComplexity.PublicCoin.FiniteMessage
import CommunicationComplexity.PrivateCoin.CoinApproximation

/-!
# Public Coin Approximation

A public-coin finite-message protocol over an arbitrary finite
probability space Ω can be approximated by one over CoinTape n.
-/

open MeasureTheory

namespace CommunicationComplexity

namespace PublicCoin

/-- Approximate a public-coin finite-message protocol over an arbitrary
finite probability space by one over CoinTape. Given `δ > 0`, produces
`n` and a CoinTape-based protocol with the same complexity. -/
noncomputable def FiniteMessage.Protocol.toCoinTape
    {Ω : Type*} [Finite Ω]
    [MeasureSpace Ω] [DiscreteMeasurableSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {X Y α : Type*}
    (p : FiniteMessage.Protocol Ω X Y α)
    (δ : ℝ) (hδ : 0 < δ) :
    Σ (n : ℕ), FiniteMessage.Protocol (CoinTape n) X Y α :=
  let data := Internal.single_coin_approx (Ω := Ω) δ hδ
  let n := data.choose
  let φ := data.choose_spec.choose
  ⟨n, p.comap (Prod.map φ id) (Prod.map φ id)⟩

@[simp]
theorem FiniteMessage.Protocol.toCoinTape_complexity
    {Ω : Type*} [Finite Ω]
    [MeasureSpace Ω] [DiscreteMeasurableSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {X Y α : Type*}
    (p : FiniteMessage.Protocol Ω X Y α)
    (δ : ℝ) (hδ : 0 < δ) :
    (p.toCoinTape δ hδ).2.complexity = p.complexity := by
  simp [FiniteMessage.Protocol.toCoinTape]

/-- The CoinTape approximation of a public-coin protocol preserves
ApproxSatisfies up to the given slack δ. -/
theorem FiniteMessage.Protocol.toCoinTape_approxSatisfies
    {Ω : Type*} [Finite Ω]
    [MeasureSpace Ω] [DiscreteMeasurableSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    {X Y α : Type*}
    (p : FiniteMessage.Protocol Ω X Y α)
    (Q : X → Y → α → Prop)
    (ε δ : ℝ) (hδ : 0 < δ)
    (hp : p.ApproxSatisfies Q ε) :
    (p.toCoinTape δ hδ).2.ApproxSatisfies Q (ε + δ) := by
  intro x y
  simp only [FiniteMessage.Protocol.toCoinTape]
  set data := Internal.single_coin_approx (Ω := Ω) δ hδ
  set φ := data.choose_spec.choose
  have happrox := data.choose_spec.choose_spec
  -- The error set under the new protocol is the preimage under φ
  let S := {ω : Ω | ¬Q x y (p.rrun x y ω)}
  have hset : {ω : CoinTape data.choose |
      ¬Q x y (FiniteMessage.Protocol.rrun
        (p.comap (Prod.map φ id) (Prod.map φ id)) x y ω)} =
      φ ⁻¹' S := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage, S,
      FiniteMessage.Protocol.rrun,
      Deterministic.FiniteMessage.Protocol.comap_run, Prod.map,
      Function.id_def]
  rw [hset]
  calc (volume (φ ⁻¹' S : Set (CoinTape data.choose))).toReal
      ≤ (volume S).toReal + δ := happrox S
    _ ≤ ε + δ := by linarith [hp x y]

end PublicCoin

end CommunicationComplexity
