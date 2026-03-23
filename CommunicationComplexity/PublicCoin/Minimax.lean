import CommunicationComplexity.PublicCoin.Complexity
import CommunicationComplexity.Comparison
import CommunicationComplexity.FiniteProbabilitySpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn

namespace CommunicationComplexity

open MeasureTheory

namespace PublicCoin

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
      (volume {xy : X × Y | p.run xy.1 xy.2 ≠ f xy.1 xy.2}).toReal > ε) :
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
    simp only [Protocol.toDeterministic_run] at h1; exact h1
  -- Use μ as the measure on X × Y
  letI : MeasureSpace (X × Y) := μ.toMeasureSpace
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
    FiniteProbabilitySpace.lt_integral_of_lt (CoinTape m) hg_gt
  -- Upper bound: ∫_{(x,y)} h(x,y) ≤ ε (since h ≤ ε pointwise)
  have h_upper : ∫ xy : X × Y, h' xy ≤ ε :=
    FiniteProbabilitySpace.integral_le_of_le (X × Y) hh_le
  -- Fubini: both integrals equal the same double sum, just in different order.
  -- On a FiniteProbabilitySpace, ∫ f = ∑ ω, (toPMF ω).toReal * f(ω).
  -- So ∫_ω g(ω) = ∑_ω ct(ω) * ∑_{xy} μ(xy) * 1_{fail}
  --             = ∑_{xy} μ(xy) * ∑_ω ct(ω) * 1_{fail}  [Finset.sum_comm]
  --             = ∫_{xy} h'(xy)
  -- We use MeasureTheory.integral_fintype to convert.
  have h_fubini : ∫ ω, g ω = ∫ xy : X × Y, h' xy := by
    -- Express g(ω) and h'(xy) as integrals of the same indicator
    -- g(ω) = ∫_{xy} 1_{fail(ω,xy)} dμ  and  h'(xy) = ∫_ω 1_{fail(ω,xy)} dCT
    -- Then ∫_ω g(ω) = ∫_ω ∫_{xy} F dμ dCT and ∫_{xy} h'(xy) = ∫_{xy} ∫_ω F dCT dμ
    -- These are equal by MeasureTheory.integral_integral_swap (Fubini for Bochner integrals).
    -- Step 1: g(ω) = ∫_{xy} (indicator of fail), h'(xy) = ∫_ω (indicator of fail)
    have hg_eq : ∀ ω, g ω = ∫ xy : X × Y,
        Set.indicator {xy : X × Y | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2} (fun _ => (1 : ℝ)) xy := by
      intro ω; simp only [g]
      -- vol(S).toReal = ∫ S.indicator 1
      symm; rw [MeasureTheory.integral_indicator MeasurableSet.of_discrete]
      simp [Measure.real]
    have hh_eq : ∀ xy : X × Y, h' xy = ∫ ω : CoinTape m,
        Set.indicator
          {ω : CoinTape m | p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2}
          (1 : CoinTape m → ℝ) ω := by
      intro ⟨x, y⟩; simp only [h']
      symm; rw [MeasureTheory.integral_indicator MeasurableSet.of_discrete]
      simp [Measure.real]
    -- Step 1': Rewrite g and h' using measureReal
    -- g(ω) = (volume S_ω).toReal = measureReal S_ω
    -- For now, express directly: g(ω) = ∫ indicator and h'(xy) = ∫ indicator
    -- using the fact that for finite discrete spaces, vol(S).toReal = ∫ 1_S
    have hg_ind : ∀ ω, g ω = ∫ xy : X × Y,
        if p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2 then (1 : ℝ) else 0 := by
      intro ω
      rw [hg_eq ω]
      congr 1; ext xy; simp [Set.indicator_apply]
    have hh_ind : ∀ xy : X × Y, h' xy = ∫ ω : CoinTape m,
        if p.rrun xy.1 xy.2 ω ≠ f xy.1 xy.2 then (1 : ℝ) else 0 := by
      intro xy
      rw [hh_eq xy]
      congr 1; ext ω; simp [Set.indicator_apply]
    simp_rw [hg_ind, hh_ind]
    -- Step 2: Apply Fubini
    exact MeasureTheory.integral_integral_swap (Integrable.of_finite)
  linarith

end PublicCoin

end CommunicationComplexity
