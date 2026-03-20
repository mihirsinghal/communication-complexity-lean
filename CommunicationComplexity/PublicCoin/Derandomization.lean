import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.NNReal.Basic
import CommunicationComplexity.PublicCoin.FiniteMessage

/-!
# Derandomization via Chernoff + Union Bound

Given a public-coin protocol that ε-computes a function f, we show there
exist finitely many randomness values ω₁, ..., ωₜ such that for every
input (x, y), at most a c·ε fraction of the ωᵢ produce incorrect outputs.
-/

open MeasureTheory ProbabilityTheory

namespace CommunicationComplexity

namespace PublicCoin.FiniteMessage.Protocol

-- Hoeffding-based bound: if Y_i are iid [0,1]-valued with E[Y_i] ≤ ε,
-- then P[∑ Y_i ≥ c*ε*t] ≤ exp(-2*(c-1)²*ε²*t) for c > 1.
private theorem prob_many_events_le
    {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω'} [IsProbabilityMeasure μ]
    {t : ℕ} {Y : Fin t → Ω' → ℝ} {ε : ℝ} {c : ℝ}
    (hindep : iIndepFun Y μ)
    (hmeas : ∀ i, AEMeasurable (Y i) μ)
    (h01 : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ i, ∫ ω, Y i ω ∂μ ≤ ε)
    (hε : 0 ≤ ε) (hc : 1 < c)
    (ht : 0 < t) :
    μ.real {ω | c * ε * t ≤ ∑ i, Y i ω}
      ≤ Real.exp (-2 * (c - 1) ^ 2 * ε ^ 2 * t) := by
  -- Center the variables: X i ω = Y i ω - E[Y i]
  set X : Fin t → Ω' → ℝ := fun i ω => Y i ω - ∫ x, Y i x ∂μ
  -- Independence of centered family
  have hindepX : iIndepFun X μ :=
    hindep.comp (fun i (y : ℝ) => y - ∫ x, Y i x ∂μ)
      (fun i => measurable_id.sub measurable_const)
  -- Sub-Gaussianity with parameter (1/2)^2
  have hsubG : ∀ i : Fin t,
      HasSubgaussianMGF (X i) (((1 : NNReal) / 2) ^ 2) μ :=
    fun i => by convert hasSubgaussianMGF_of_mem_Icc (a := (0 : ℝ)) (b := 1) (hmeas i) (h01 i)
              using 2; simp
  -- Hoeffding tail bound for ∑ X_i with threshold (c-1)*ε*t
  have htail := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    (ι := Fin t) hindepX (s := Finset.univ)
    (c := fun _ => ((1 : NNReal) / 2) ^ 2)
    (fun i _ => hsubG i) (ε := (c - 1) * ε * ↑t)
    (by apply mul_nonneg
        · apply mul_nonneg <;> linarith
        · exact Nat.cast_nonneg _)
  -- Mean bound: ∑ E[Y_i] ≤ εt
  have hmean_sum : ∑ i : Fin t, ∫ x, Y i x ∂μ ≤ ε * ↑t := by
    calc ∑ i : Fin t, ∫ x, Y i x ∂μ
        ≤ ∑ _ : Fin t, ε := Finset.sum_le_sum (fun i _ => hmean i)
      _ = ε * ↑t := by simp [Finset.sum_const, mul_comm]
  -- Set inclusion: {∑ Y ≥ c*ε*t} ⊆ {∑ X ≥ (c-1)*ε*t}
  have hsubset : {ω | c * ε * ↑t ≤ ∑ i, Y i ω} ⊆
      {ω | (c - 1) * ε * ↑t ≤ ∑ i ∈ Finset.univ, X i ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hsub : ∑ i : Fin t, X i ω =
        ∑ i, Y i ω - ∑ i, ∫ x, Y i x ∂μ := by
      simp only [X, Finset.sum_sub_distrib]
    nlinarith [hsub, hmean_sum]
  -- Monotonicity + exponent simplification
  calc μ.real {ω | c * ε * ↑t ≤ ∑ i, Y i ω}
      ≤ μ.real {ω | (c - 1) * ε * ↑t ≤ ∑ i ∈ Finset.univ, X i ω} :=
        measureReal_mono hsubset
    _ ≤ _ := htail
    _ = Real.exp (-2 * (c - 1) ^ 2 * ε ^ 2 * ↑t) := by
        congr 1
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        push_cast
        have ht_pos : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        field_simp
        ring

variable {Ω X Y α : Type*}
  [Fintype X] [Fintype Y]

/-- The number of random samples needed for derandomization via
Chernoff + union bound: `⌈log(|X|·|Y|) / (2·(c-1)²·ε²)⌉₊ + 1`. -/
noncomputable def derandomizationSamples
    (X Y : Type*) [Fintype X] [Fintype Y]
    (ε c : ℝ) : ℕ :=
  ⌈Real.log (Fintype.card X * Fintype.card Y) /
    (2 * (c - 1) ^ 2 * ε ^ 2)⌉₊ + 1

open Classical in
/-- Chernoff + union bound derandomization: given a protocol that
ε-computes f with c > 1, there exist t = O(log(|X|·|Y|)/((c-1)²ε²))
randomness values such that for every input (x, y), at most a c·ε
fraction of them produce incorrect outputs. -/
theorem exists_good_randomness
    [MeasureSpace Ω] [DiscreteMeasurableSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    (p : Protocol Ω X Y α) (f : X → Y → α) (ε : ℝ) (c : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hc : 1 < c)
    (hp : p.ApproxComputes f ε) :
    ∃ (ωs : Fin (derandomizationSamples X Y ε c) → Ω),
      ∀ (x : X) (y : Y),
        ((Finset.univ.filter (fun i => p.rrun x y (ωs i) ≠ f x y)).card : ℝ) /
          (derandomizationSamples X Y ε c)
          ≤ c * ε := by
  set t := derandomizationSamples X Y ε c with ht_def
  have ht_pos : 0 < t := by simp [ht_def, derandomizationSamples]
  -- The key bound: exp(-2*(c-1)²*ε²*t) * |X| * |Y| < 1
  have ht_bound : Real.exp (-2 * (c - 1) ^ 2 * ε ^ 2 * ↑t) *
      (Fintype.card X * Fintype.card Y) < 1 := by
    set N : ℝ := ↑(Fintype.card X) * ↑(Fintype.card Y) with hN_def
    set D : ℝ := 2 * (c - 1) ^ 2 * ε ^ 2 with hD_def
    have hD_pos : 0 < D := by
      rw [hD_def]
      exact mul_pos (mul_pos (by linarith) (sq_pos_of_pos (by linarith))) (sq_pos_of_pos hε)
    suffices h : Real.exp (-D * ↑t) * N < 1 by
      have : -2 * (c - 1) ^ 2 * ε ^ 2 * ↑t = -D * ↑t := by rw [hD_def]; ring
      rwa [this]
    by_cases hN : N ≤ 0
    · nlinarith [Real.exp_pos (-D * ↑t)]
    · push_neg at hN
      have hL_lt : Real.log N / D < ↑t := by
        have h1 : Real.log N / D ≤ ↑⌈Real.log N / D⌉₊ := Nat.le_ceil _
        have h2 : ⌈Real.log N / D⌉₊ < t := by
          simp only [ht_def, derandomizationSamples, hN_def, hD_def]; omega
        linarith [Nat.cast_lt (α := ℝ).mpr h2]
      have hDt : Real.log N < D * ↑t := by
        rw [div_lt_iff₀ hD_pos] at hL_lt; linarith
      calc Real.exp (-D * ↑t) * N
          < Real.exp (-Real.log N) * N := by
            apply mul_lt_mul_of_pos_right _ hN
            exact Real.exp_strictMono (by linarith)
        _ = 1 := by
            rw [Real.exp_neg, Real.exp_log hN, inv_mul_cancel₀ (ne_of_gt hN)]
  -- Probabilistic existence on the product space Fin t → Ω
  have : ∃ (ωs : Fin t → Ω), ∀ (x : X) (y : Y),
      ((Finset.univ.filter (fun i => p.rrun x y (ωs i) ≠ f x y)).card : ℝ) / t
        ≤ c * ε := by
    -- For each (x,y), define indicator Y_i(ωs) = 1 if p.rrun x y (ωs i) ≠ f x y
    -- On product space (Fin t → Ω), these are independent across i
    -- Apply prob_many_events_le, then union bound
    -- Define the "bad" event for each (x,y)
    set bad : X → Y → Set (Fin t → Ω) :=
      fun x y => {ωs | c * ε * ↑t ≤
        ∑ i : Fin t, if p.rrun x y (ωs i) ≠ f x y then (1 : ℝ) else 0}
    -- Each bad event has small measure by prob_many_events_le
    set μ : Measure (Fin t → Ω) := volume with hμ_def
    have hbad_measure : ∀ x y,
        μ.real (bad x y) ≤
          Real.exp (-2 * (c - 1) ^ 2 * ε ^ 2 * ↑t) := by
      intro x y
      apply prob_many_events_le
        (Y := fun i (ωs : Fin t → Ω) =>
          if p.rrun x y (ωs i) ≠ f x y then (1 : ℝ) else 0)
      · -- Independence
        have hcoord : iIndepFun (fun i (ωs : Fin t → Ω) => ωs i)
            (volume : Measure (Fin t → Ω)) :=
          iIndepFun_pi (fun i => aemeasurable_id)
        exact hcoord.comp
          (fun i (ω : Ω) => if p.rrun x y ω ≠ f x y then (1 : ℝ) else 0)
          (fun i => Measurable.of_discrete)
      · -- Measurability
        intro i
        have : (fun ωs : Fin t → Ω =>
          if p.rrun x y (ωs i) ≠ f x y then (1 : ℝ) else 0) =
          (fun ω : Ω => if p.rrun x y ω ≠ f x y then (1 : ℝ) else 0) ∘
          (fun ωs => ωs i) := rfl
        rw [this]
        exact Measurable.of_discrete.aemeasurable.comp_measurable (measurable_pi_apply i)
      · -- [0,1]-valued
        intro i; exact Filter.Eventually.of_forall
          (fun ωs => by simp [Set.mem_Icc]; split <;> norm_num)
      · -- Mean bound: E[Y_i] = P[p.rrun x y ω ≠ f x y] ≤ ε
        intro i
        -- The integral over the product space equals the integral over Ω
        -- via measurePreserving_eval (marginal of product = volume)
        set g : Ω → ℝ := fun ω => if p.rrun x y ω ≠ f x y then 1 else 0
        have hmp := measurePreserving_eval
          (μ := fun (_ : Fin t) => (volume : Measure Ω)) i
        have : ∫ ωs, g (ωs i) ∂μ = ∫ ω, g ω ∂(volume : Measure Ω) := by
          set ν : Measure (Fin t → Ω) :=
            Measure.pi fun _ => (volume : Measure Ω)
          have h1 : ∫ (ωs : Fin t → Ω), g (ωs i) ∂ν =
              ∫ ω, g ω ∂(Measure.map (Function.eval i) ν) :=
            (integral_map (measurable_pi_apply i).aemeasurable
              Measurable.of_discrete.aestronglyMeasurable).symm
          simp only [hμ_def, hmp.map_eq] at h1 ⊢; exact h1
        rw [this]
        have hg_eq : g = Set.indicator {ω | p.rrun x y ω ≠ f x y} 1 := by
          ext ω; simp [g, Set.indicator_apply]
        rw [hg_eq, integral_indicator MeasurableSet.of_discrete, Pi.one_def,
          integral_const, smul_eq_mul, mul_one,
          measureReal_restrict_apply_univ]
        exact hp x y
      · linarith
      · exact hc
      · exact ht_pos
    -- Union bound
    have hunion : μ.real (⋃ x : X, ⋃ y : Y, bad x y) < 1 := by
      calc μ.real (⋃ x : X, ⋃ y : Y, bad x y)
          ≤ ∑ x : X, μ.real (⋃ y : Y, bad x y) :=
            measureReal_iUnion_fintype_le _
        _ ≤ ∑ x : X, ∑ y : Y, μ.real (bad x y) := by
            apply Finset.sum_le_sum; intro x _
            exact measureReal_iUnion_fintype_le _
        _ ≤ ∑ x : X, ∑ _y : Y,
              Real.exp (-2 * (c - 1) ^ 2 * ε ^ 2 * ↑t) := by
            apply Finset.sum_le_sum; intro x _
            exact Finset.sum_le_sum (fun y _ => hbad_measure x y)
        _ = (Fintype.card X * Fintype.card Y) *
              Real.exp (-2 * (c - 1) ^ 2 * ε ^ 2 * ↑t) := by
            simp [Finset.sum_const, mul_comm, mul_assoc]
        _ < 1 := by nlinarith [ht_bound]
    -- Therefore complement is nonempty: ∃ good ωs
    have hgood : ∃ ωs : Fin t → Ω, ωs ∉ ⋃ x : X, ⋃ y : Y, bad x y := by
      by_contra h
      push_neg at h
      have : ⋃ x : X, ⋃ y : Y, bad x y = Set.univ := Set.eq_univ_of_forall h
      rw [this, probReal_univ] at hunion
      linarith
    obtain ⟨ωs, hωs⟩ := hgood
    refine ⟨ωs, fun x y => ?_⟩
    -- ωs is not bad for any (x,y), so #{bad i}/t ≤ c*ε
    simp only [Set.mem_iUnion, not_exists, bad, Set.mem_setOf_eq, not_le] at hωs
    have hlt := hωs x y
    have hsum_eq : ∑ i : Fin t,
        (if p.rrun x y (ωs i) ≠ f x y then (1 : ℝ) else 0) =
        (Finset.univ.filter (fun i => p.rrun x y (ωs i) ≠ f x y)).card := by
      simp [Finset.card_filter]
    rw [hsum_eq] at hlt
    rw [div_le_iff₀ (by exact_mod_cast ht_pos : (0 : ℝ) < ↑t)]
    linarith
  obtain ⟨ωs, hωs⟩ := this
  exact ⟨ωs, hωs⟩

end PublicCoin.FiniteMessage.Protocol

end CommunicationComplexity
