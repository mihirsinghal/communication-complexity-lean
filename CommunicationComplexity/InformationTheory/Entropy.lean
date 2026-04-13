import PFR.ForMathlib.Entropy.Basic

/-!
# Entropy

This file imports the entropy definitions and basic API from `PFR.ForMathlib.Entropy.Basic`.

The main definitions live in the `ProbabilityTheory` namespace:

* `ProbabilityTheory.entropy`
* `ProbabilityTheory.condEntropy`
* `ProbabilityTheory.mutualInfo`

It also provides notations such as `H[X]`, `H[X ; μ]`, `H[X | Y]`, and `I[X : Y]`.
-/

namespace ProbabilityTheory

open MeasureTheory

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

/-- Entropy is bounded by the logarithm of any natural-number upper bound on the alphabet size. -/
theorem entropy_le_log_of_card_le [Fintype S] [Nonempty S] [MeasurableSingletonClass S]
    (X : Ω → S) (μ : Measure Ω) {N : ℕ}
    (hcard : Fintype.card S ≤ N) :
    H[X ; μ] ≤ Real.log N := by
  have hcard_pos : 0 < (Fintype.card S : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcard_cast : (Fintype.card S : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hcard
  exact (entropy_le_log_card X μ).trans (Real.log_le_log hcard_pos hcard_cast)

/-- Entropy is bounded by `c * log 2` when the alphabet has size at most `2 ^ c`. -/
theorem entropy_le_nat_mul_log_two_of_card_le_two_pow
    [Fintype S] [Nonempty S] [MeasurableSingletonClass S]
    (X : Ω → S) (μ : Measure Ω) {c : ℕ}
    (hcard : Fintype.card S ≤ 2 ^ c) :
    H[X ; μ] ≤ c * Real.log 2 := by
  simpa [Nat.cast_pow] using entropy_le_log_of_card_le X μ hcard

variable {T U : Type*} [MeasurableSpace T] [MeasurableSpace U]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
  [Countable S] [Countable T] [Countable U]
  {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}

/-- Mutual information is bounded by the entropy of the left variable. -/
theorem mutualInfo_le_entropy_left
    (hX : Measurable X) (hY : Measurable Y)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    I[X : Y ; μ] ≤ H[X ; μ] := by
  rw [mutualInfo_eq_entropy_sub_condEntropy hX hY]
  linarith [condEntropy_nonneg X Y μ]

/-- Mutual information is bounded by the entropy of the right variable. -/
theorem mutualInfo_le_entropy_right
    (hX : Measurable X) (hY : Measurable Y)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] :
    I[X : Y ; μ] ≤ H[Y ; μ] := by
  rw [mutualInfo_comm hX hY]
  exact mutualInfo_le_entropy_left hY hX

/-- Conditional mutual information is bounded by the left conditional entropy. -/
theorem condMutualInfo_le_condEntropy_left
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    I[X : Y | Z ; μ] ≤ H[X | Z ; μ] := by
  rw [condMutualInfo_eq' hX hY hZ]
  linarith [condEntropy_nonneg X (fun ω => (Y ω, Z ω)) μ]

/-- Conditional mutual information is bounded by the right conditional entropy. -/
theorem condMutualInfo_le_condEntropy_right
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    I[X : Y | Z ; μ] ≤ H[Y | Z ; μ] := by
  rw [condMutualInfo_comm hX hY Z μ]
  exact condMutualInfo_le_condEntropy_left hY hX hZ

/-- Conditional mutual information is bounded by the entropy of the left variable. -/
theorem condMutualInfo_le_entropy_left
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    I[X : Y | Z ; μ] ≤ H[X ; μ] :=
  (condMutualInfo_le_condEntropy_left hX hY hZ).trans
    (condEntropy_le_entropy μ hX hZ)

/-- Conditional mutual information is bounded by the entropy of the right variable. -/
theorem condMutualInfo_le_entropy_right
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    I[X : Y | Z ; μ] ≤ H[Y ; μ] :=
  (condMutualInfo_le_condEntropy_right hX hY hZ).trans
    (condEntropy_le_entropy μ hY hZ)

/-- Conditional data processing where the left-side postprocessing may depend on the
conditioning value. -/
theorem condMutualInfo_comp_left_le_of_comp_conditioning
    {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (f : U → S → V) :
    I[fun ω => f (Z ω) (X ω) : Y | Z ; μ] ≤ I[X : Y | Z ; μ] := by
  have hZX :
      I[fun ω => (Z ω, X ω) : Y | Z ; μ] = I[X : Y | Z ; μ] :=
    condMutualInfo_of_inj_map hX hY hZ
      (fun z x => (z, x)) (fun _ _ _ h => (Prod.ext_iff.1 h).2)
  have hle :
      I[fun ω => f (Z ω) (X ω) : Y | Z ; μ] ≤
        I[fun ω => (Z ω, X ω) : Y | Z ; μ] := by
    simpa [Function.comp_def] using
      condMutual_comp_comp_le (μ := μ)
        (X := fun ω => (Z ω, X ω)) (Y := Y) (Z := Z)
        (hX := hZ.prodMk hX) (hY := hY) (hZ := hZ)
        (f := fun zx => f zx.1 zx.2) (g := id) measurable_id
  exact hle.trans_eq hZX

variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
  {W : Ω → V}

/-- Adding a deterministic function of the conditioning variable to the conditioning variable does
not change conditional mutual information. -/
theorem condMutualInfo_conditioning_prod_function_eq
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) (f : U → V) :
    I[X : Y | (fun ω => (Z ω, f (Z ω))) ; μ] = I[X : Y | Z ; μ] := by
  simpa [Function.comp_def] using
    condMutualInfo_of_inj hX hY hZ μ
      (f := fun z => (z, f z)) (fun _ _ h => (Prod.ext_iff.1 h).1)

/-- Chain rule for conditional mutual information, splitting a pair on the left. -/
theorem condMutualInfo_prod_left_eq_add
    (hX : Measurable X) (hW : Measurable W) (hY : Measurable Y) (hZ : Measurable Z)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange W] [FiniteRange Y]
    [FiniteRange Z] :
    I[fun ω => (X ω, W ω) : Y | Z ; μ] =
      I[X : Y | Z ; μ] + I[W : Y | fun ω => (X ω, Z ω) ; μ] := by
  have hA :
      H[W | (fun ω => (X ω, (Y ω, Z ω))) ; μ] =
        H[W | (fun ω => (Y ω, (X ω, Z ω))) ; μ] := by
    let f : T × (S × U) → S × (T × U) := fun t => (t.2.1, (t.1, t.2.2))
    have hf : Function.Injective f := by
      intro a b h
      rcases a with ⟨aY, aX, aZ⟩
      rcases b with ⟨bY, bX, bZ⟩
      simp only [f, Prod.mk.injEq] at h ⊢
      exact ⟨h.2.1, h.1, h.2.2⟩
    have hf_meas : Measurable f := Measurable.of_discrete
    have hfY : Measurable (f ∘ fun ω => (Y ω, (X ω, Z ω))) :=
      hf_meas.comp (hY.prodMk (hX.prodMk hZ))
    simpa [f, Function.comp_def] using
      (condEntropy_of_injective' μ hW (hY.prodMk (hX.prodMk hZ)) f hf
        hfY)
  rw [condMutualInfo_eq' (hX.prodMk hW) hY hZ,
    condMutualInfo_eq' hX hY hZ,
    condMutualInfo_eq' hW hY (hX.prodMk hZ),
    cond_chain_rule' μ hX hW hZ,
    cond_chain_rule' μ hX hW (hY.prodMk hZ),
    hA]
  ring

/-- Chain rule for conditional mutual information, splitting a pair on the right. -/
theorem condMutualInfo_prod_right_eq_add
    (hX : Measurable X) (hY : Measurable Y) (hW : Measurable W) (hZ : Measurable Z)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange W]
    [FiniteRange Z] :
    I[X : (fun ω => (Y ω, W ω)) | Z ; μ] =
      I[X : Y | Z ; μ] + I[X : W | fun ω => (Y ω, Z ω) ; μ] := by
  rw [condMutualInfo_comm hX (hY.prodMk hW) Z μ,
    condMutualInfo_prod_left_eq_add hY hW hX hZ,
    condMutualInfo_comm hY hX Z μ,
    condMutualInfo_comm hW hX (fun ω => (Y ω, Z ω)) μ]

/-- Chain rule for mutual information, splitting a pair on the right. -/
theorem mutualInfo_prod_right_eq_add
    (hX : Measurable X) (hY : Measurable Y) (hW : Measurable W)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange W] :
    I[X : (fun ω => (Y ω, W ω)) ; μ] =
      I[X : Y ; μ] + I[X : W | Y ; μ] := by
  have hswap :
      H[X | (fun ω => (W ω, Y ω)) ; μ] =
        H[X | (fun ω => (Y ω, W ω)) ; μ] := by
    let swap : V × T → T × V := fun p => (p.2, p.1)
    have hswap_meas : Measurable (swap ∘ fun ω => (W ω, Y ω)) := by
      exact Measurable.of_discrete.comp (hW.prodMk hY)
    have h :=
      condEntropy_of_injective' μ hX (hW.prodMk hY) swap
        (fun a b h => by
          rcases a with ⟨aW, aY⟩
          rcases b with ⟨bW, bY⟩
          simp only [swap, Prod.mk.injEq] at h ⊢
          exact ⟨h.2, h.1⟩)
        hswap_meas
    simpa [swap, Function.comp_def] using h.symm
  rw [mutualInfo_eq_entropy_sub_condEntropy hX (hY.prodMk hW) μ,
    mutualInfo_eq_entropy_sub_condEntropy hX hY μ,
    condMutualInfo_eq' hX hW hY μ, hswap]
  ring

/-- Conditional entropy is unchanged when both variables are replaced by almost-everywhere equal
variables. -/
theorem condEntropy_congr_ae
    {X' : Ω → S} {Y' : Ω → T}
    [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange X'] [FiniteRange Y']
    (hX : Measurable X) (hY : Measurable Y) (hX' : Measurable X') (hY' : Measurable Y')
    (hXae : X =ᵐ[μ] X') (hYae : Y =ᵐ[μ] Y') :
    H[X | Y ; μ] = H[X' | Y' ; μ] := by
  have hpair :
      IdentDistrib (fun ω => (X ω, Y ω)) (fun ω => (X' ω, Y' ω)) μ μ :=
    IdentDistrib.of_ae_eq (hX.prodMk hY).aemeasurable (hXae.prodMk hYae)
  exact IdentDistrib.condEntropy_eq hX hY hX' hY' hpair

/-- Conditional mutual information is unchanged when the two measured variables are replaced by
almost-everywhere equal variables and the conditioning variable is unchanged. -/
theorem condMutualInfo_congr_ae_left_right
    {X' : Ω → S} {Y' : Ω → T}
    [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange X'] [FiniteRange Y']
    [FiniteRange Z]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hX' : Measurable X') (hY' : Measurable Y')
    (hXae : X =ᵐ[μ] X') (hYae : Y =ᵐ[μ] Y') :
    I[X : Y | Z ; μ] = I[X' : Y' | Z ; μ] := by
  rw [condMutualInfo_eq hX hY hZ, condMutualInfo_eq hX' hY' hZ]
  have hXcond :
      H[X | Z ; μ] = H[X' | Z ; μ] := by
    exact condEntropy_congr_ae hX hZ hX' hZ hXae (by rfl)
  have hYcond :
      H[Y | Z ; μ] = H[Y' | Z ; μ] := by
    exact condEntropy_congr_ae hY hZ hY' hZ hYae (by rfl)
  have hXYcond :
      H[fun ω => (X ω, Y ω) | Z ; μ] = H[fun ω => (X' ω, Y' ω) | Z ; μ] := by
    exact condEntropy_congr_ae (hX.prodMk hY) hZ (hX'.prodMk hY') hZ
      (hXae.prodMk hYae) (by rfl)
  rw [hXcond, hYcond, hXYcond]

/-- Conditional mutual information is unchanged when all three variables are replaced by
almost-everywhere equal variables. -/
theorem condMutualInfo_congr_ae
    {X' : Ω → S} {Y' : Ω → T} {Z' : Ω → U}
    [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    [FiniteRange X'] [FiniteRange Y'] [FiniteRange Z']
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hX' : Measurable X') (hY' : Measurable Y') (hZ' : Measurable Z')
    (hXae : X =ᵐ[μ] X') (hYae : Y =ᵐ[μ] Y') (hZae : Z =ᵐ[μ] Z') :
    I[X : Y | Z ; μ] = I[X' : Y' | Z' ; μ] := by
  rw [condMutualInfo_eq (μ := μ) hX hY hZ,
    condMutualInfo_eq (μ := μ) hX' hY' hZ']
  have hXcond :
      H[X | Z ; μ] = H[X' | Z' ; μ] := by
    exact condEntropy_congr_ae hX hZ hX' hZ' hXae hZae
  have hYcond :
      H[Y | Z ; μ] = H[Y' | Z' ; μ] := by
    exact condEntropy_congr_ae hY hZ hY' hZ' hYae hZae
  have hXYcond :
      H[fun ω => (X ω, Y ω) | Z ; μ] = H[fun ω => (X' ω, Y' ω) | Z' ; μ] := by
    exact condEntropy_congr_ae (hX.prodMk hY) hZ (hX'.prodMk hY') hZ'
      (hXae.prodMk hYae) hZae
  rw [hXcond, hYcond, hXYcond]

/-- Conditional mutual information is determined by the joint law of `(X, Y, Z)`. -/
theorem IdentDistrib.condMutualInfo_eq
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    {X' : Ω' → S} {Y' : Ω' → T} {Z' : Ω' → U}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    [FiniteRange X'] [FiniteRange Y'] [FiniteRange Z']
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hX' : Measurable X') (hY' : Measurable Y') (hZ' : Measurable Z')
    (h : IdentDistrib (fun ω => (X ω, Y ω, Z ω))
        (fun ω => (X' ω, Y' ω, Z' ω)) μ μ') :
    I[X : Y | Z ; μ] = I[X' : Y' | Z' ; μ'] := by
  rw [_root_.ProbabilityTheory.condMutualInfo_eq (μ := μ) hX hY hZ,
    _root_.ProbabilityTheory.condMutualInfo_eq (μ := μ') hX' hY' hZ']
  have hXZ :
      IdentDistrib (fun ω => (X ω, Z ω)) (fun ω => (X' ω, Z' ω)) μ μ' :=
    h.comp (Measurable.of_discrete (f := fun a : S × T × U => (a.1, a.2.2)))
  have hYZ :
      IdentDistrib (fun ω => (Y ω, Z ω)) (fun ω => (Y' ω, Z' ω)) μ μ' :=
    h.comp (Measurable.of_discrete (f := fun a : S × T × U => (a.2.1, a.2.2)))
  have hXYZ :
      IdentDistrib (fun ω => ((X ω, Y ω), Z ω))
          (fun ω => ((X' ω, Y' ω), Z' ω)) μ μ' :=
    h.comp (Measurable.of_discrete (f := fun a : S × T × U => ((a.1, a.2.1), a.2.2)))
  rw [IdentDistrib.condEntropy_eq hX hZ hX' hZ' hXZ,
    IdentDistrib.condEntropy_eq hY hZ hY' hZ' hYZ,
    IdentDistrib.condEntropy_eq (hX.prodMk hY) hZ (hX'.prodMk hY') hZ' hXYZ]

end ProbabilityTheory
