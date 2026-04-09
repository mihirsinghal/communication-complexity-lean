import CommunicationComplexity.PublicCoin.Complexity
import CommunicationComplexity.Comparison
import CommunicationComplexity.FiniteProbabilitySpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn

namespace CommunicationComplexity

open MeasureTheory

namespace Deterministic

namespace Protocol

variable {X Y α : Type*}

/-- The distributional error of a deterministic protocol with respect
to a distribution `μ` on `X × Y`: the probability that the protocol
output disagrees with `f`. -/
noncomputable def distributionalError
    (p : Protocol X Y α)
    (μ : FiniteProbabilitySpace (X × Y))
    (f : X → Y → α) : ℝ := by
  letI := μ
  exact (volume {xy : X × Y | p.run xy.1 xy.2 ≠ f xy.1 xy.2}).toReal

/-- The distributional failure probability of a deterministic protocol
with respect to a correctness predicate `Q`. -/
noncomputable def distributionalFailure
    (p : Protocol X Y α)
    (μ : FiniteProbabilitySpace (X × Y))
    (Q : X → Y → α → Prop) : ℝ := by
  letI := μ
  exact (volume {xy : X × Y | ¬Q xy.1 xy.2 (p.run xy.1 xy.2)}).toReal

end Protocol

end Deterministic

namespace PublicCoin

private lemma failureIntegral_swap
    {X Y α : Type*} {m : ℕ} [μ : FiniteProbabilitySpace (X × Y)]
    (p : Protocol (CoinTape m) X Y α)
    (f : X → Y → α) :
    ∫ ω, (volume {xy : X × Y | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2}).toReal =
      ∫ xy : X × Y, (volume {ω : CoinTape m | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2}).toReal := by
  -- Rewrite each probability as an integral of the corresponding failure indicator,
  -- then swap the order of integration.
  have hg_eq : ∀ ω, (volume {xy : X × Y | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2}).toReal =
      ∫ xy : X × Y,
        Set.indicator {xy : X × Y | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2}
          (fun _ => (1 : ℝ)) xy := by
    intro ω
    apply FiniteProbabilitySpace.measureReal_eq_integral_indicator_one
  have hh_eq : ∀ xy : X × Y,
      (volume {ω : CoinTape m | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2}).toReal =
        ∫ ω : CoinTape m,
          Set.indicator {ω : CoinTape m | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2}
            (fun _ => (1 : ℝ)) ω := by
    intro xy
    apply FiniteProbabilitySpace.measureReal_eq_integral_indicator_one
  simp_rw [hg_eq, hh_eq]
  simpa [Set.indicator_apply] using
    (MeasureTheory.integral_integral_swap (Integrable.of_finite) :
      ∫ xy : X × Y, ∫ ω : CoinTape m,
        Set.indicator {ω : CoinTape m | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2}
          (fun _ => (1 : ℝ)) ω =
      ∫ ω : CoinTape m, ∫ xy : X × Y,
        Set.indicator {xy : X × Y | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2}
          (fun _ => (1 : ℝ)) xy).symm

private lemma failureIntegral_swap_satisfies
    {X Y α : Type*} {m : ℕ} [μ : FiniteProbabilitySpace (X × Y)]
    (p : Protocol (CoinTape m) X Y α)
    (Q : X → Y → α → Prop) :
    ∫ ω, (volume {xy : X × Y | ¬Q xy.1 xy.2 (p.rrun xy.1 xy.2 ω)}).toReal =
      ∫ xy : X × Y, (volume {ω : CoinTape m | ¬Q xy.1 xy.2 (p.rrun xy.1 xy.2 ω)}).toReal := by
  have hg_eq : ∀ ω,
      (volume {xy : X × Y | ¬Q xy.1 xy.2 (p.rrun xy.1 xy.2 ω)}).toReal =
        ∫ xy : X × Y,
          Set.indicator {xy : X × Y | ¬Q xy.1 xy.2 (p.rrun xy.1 xy.2 ω)}
            (fun _ => (1 : ℝ)) xy := by
    intro ω
    apply FiniteProbabilitySpace.measureReal_eq_integral_indicator_one
  have hh_eq : ∀ xy : X × Y,
      (volume {ω : CoinTape m | ¬Q xy.1 xy.2 (p.rrun xy.1 xy.2 ω)}).toReal =
        ∫ ω : CoinTape m,
          Set.indicator {ω : CoinTape m | ¬Q xy.1 xy.2 (p.rrun xy.1 xy.2 ω)}
            (fun _ => (1 : ℝ)) ω := by
    intro xy
    apply FiniteProbabilitySpace.measureReal_eq_integral_indicator_one
  simp_rw [hg_eq, hh_eq]
  simpa [Set.indicator_apply] using
    (MeasureTheory.integral_integral_swap (Integrable.of_finite) :
      ∫ xy : X × Y, ∫ ω : CoinTape m,
        Set.indicator {ω : CoinTape m | ¬Q xy.1 xy.2 (p.rrun xy.1 xy.2 ω)}
          (fun _ => (1 : ℝ)) ω =
      ∫ ω : CoinTape m, ∫ xy : X × Y,
        Set.indicator {xy : X × Y | ¬Q xy.1 xy.2 (p.rrun xy.1 xy.2 ω)}
          (fun _ => (1 : ℝ)) xy).symm

open Classical in
/-- Yao's minimax principle (one direction): if there exists a joint
distribution μ over X × Y such that every deterministic protocol of
complexity ≤ n fails with probability > ε under μ, then the public-coin
randomized communication complexity of f at error ε is greater than n. -/
theorem minimax_lower_bound
    {X Y α : Type*}
    (f : X → Y → α) (ε : ℝ) (n : ℕ)
    (μ : FiniteProbabilitySpace (X × Y))
    (h : ∀ (p : Deterministic.Protocol X Y α),
      p.complexity ≤ n →
      p.distributionalError μ f > ε) :
    n < communicationComplexity f ε := by
  -- Prove by contradiction: suppose CC(f, ε) ≤ n
  rw [show (n : ENat) < communicationComplexity f ε ↔
    ¬(communicationComplexity f ε ≤ n) from not_le.symm]
  intro hle
  -- Get a randomized protocol p with complexity ≤ n and error ≤ ε
  obtain ⟨m, p, hp, hc⟩ := (communicationComplexity_le_iff f ε n).mp hle
  -- By h, each p.toDeterministic ω has failure prob > ε under μ
  have hdet_fail : ∀ ω : CoinTape m,
      (volume {xy : X × Y | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2}).toReal > ε := by
    intro ω
    have h1 := h (p.toDeterministic ω) (by simp [hc])
    simpa [Deterministic.Protocol.distributionalError, Protocol.toDeterministic_run] using h1
  -- Use μ as the ambient finite probability space on X × Y.
  letI : FiniteProbabilitySpace (X × Y) := μ
  -- g(ω) = vol_μ({(x,y) | p fails with randomness ω}), satisfies g(ω) > ε
  set g : CoinTape m → ℝ := fun ω =>
    (volume {xy : X × Y | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2}).toReal
  have hg_gt : ∀ ω, ε < g ω := hdet_fail
  -- h(x,y) = vol_CoinTape({ω | p fails on (x,y)}), satisfies h(x,y) ≤ ε
  set h' : X × Y → ℝ := fun xy =>
    (volume {ω : CoinTape m | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2}).toReal
  have hh_le : ∀ xy : X × Y, h' xy ≤ ε := fun ⟨x, y⟩ => hp x y
  -- Lower bound: ∫_ω g(ω) > ε (since g > ε pointwise)
  have h_lower : ε < ∫ ω, g ω :=
    FiniteProbabilitySpace.lt_integral_of_lt hg_gt
  -- Upper bound: ∫_{(x,y)} h(x,y) ≤ ε (since h ≤ ε pointwise)
  have h_upper : ∫ xy : X × Y, h' xy ≤ ε :=
    FiniteProbabilitySpace.integral_le_of_le hh_le
  -- Fubini: average first over randomness or first over inputs.
  have h_fubini : ∫ ω, g ω = ∫ xy : X × Y, h' xy := by
    simpa [g, h'] using failureIntegral_swap (p := p) (f := f)
  linarith

/-- Predicate version of Yao's minimax principle, stated directly for
protocols. If every deterministic protocol of complexity at most `n`
violates `Q` with distributional probability greater than `ε`, then no
public-coin protocol of complexity at most `n` can `ε`-satisfy `Q`. -/
theorem protocol_lower_bound_satisfies
    {X Y α : Type*}
    (Q : X → Y → α → Prop) (ε : ℝ) (n : ℕ)
    (μ : FiniteProbabilitySpace (X × Y))
    (h : ∀ (p : Deterministic.Protocol X Y α),
      p.complexity ≤ n →
      p.distributionalFailure μ Q > ε) :
    ∀ {m : ℕ} (p : Protocol (CoinTape m) X Y α),
      p.ApproxSatisfies Q ε →
      n < p.complexity := by
  intro m p hp
  by_contra hnp
  have hc : p.complexity ≤ n := Nat.not_lt.mp hnp
  have hdet_fail : ∀ ω : CoinTape m,
      (volume {xy : X × Y | ¬Q xy.1 xy.2 (p.rrun xy.1 xy.2 ω)}).toReal > ε := by
    intro ω
    have h1 := h (p.toDeterministic ω) (by simpa [hc])
    simpa [Deterministic.Protocol.distributionalFailure, Protocol.toDeterministic_run] using h1
  letI : FiniteProbabilitySpace (X × Y) := μ
  set g : CoinTape m → ℝ := fun ω =>
    (volume {xy : X × Y | ¬Q xy.1 xy.2 (p.rrun xy.1 xy.2 ω)}).toReal
  have hg_gt : ∀ ω, ε < g ω := hdet_fail
  set h' : X × Y → ℝ := fun xy =>
    (volume {ω : CoinTape m | ¬Q xy.1 xy.2 (p.rrun xy.1 xy.2 ω)}).toReal
  have hh_le : ∀ xy : X × Y, h' xy ≤ ε := fun ⟨x, y⟩ => hp x y
  have h_lower : ε < ∫ ω, g ω :=
    FiniteProbabilitySpace.lt_integral_of_lt hg_gt
  have h_upper : ∫ xy : X × Y, h' xy ≤ ε :=
    FiniteProbabilitySpace.integral_le_of_le hh_le
  have h_fubini : ∫ ω, g ω = ∫ xy : X × Y, h' xy := by
    simpa [g, h'] using failureIntegral_swap_satisfies (p := p) (Q := Q)
  linarith

end PublicCoin

end CommunicationComplexity
