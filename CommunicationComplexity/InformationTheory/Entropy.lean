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

open MeasureTheory Measure Set

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

open Classical in
/-- Mutual information is unchanged by an injective recoding of the right variable. -/
theorem mutualInfo_comp_right_of_injective
    {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y]
    (hX : Measurable X) (hY : Measurable Y)
    (f : T → V) (hf : Measurable f) (hfinj : Function.Injective f) :
    I[X : f ∘ Y ; μ] = I[X : Y ; μ] := by
  rw [mutualInfo_eq_entropy_sub_condEntropy hX (hf.comp hY),
    mutualInfo_eq_entropy_sub_condEntropy hX hY]
  rw [condEntropy_of_injective' μ hX hY f hfinj (hf.comp hY)]

omit [Countable S] [Countable T] in
/-- If the left variable is almost surely constant, its mutual information with any finite
variable is zero. -/
theorem mutualInfo_eq_zero_of_ae_eq_const_left
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y]
    (hX : Measurable X) (hY : Measurable Y) (c : S)
    (hconst : X =ᵐ[μ] fun _ => c) :
    I[X : Y ; μ] = 0 := by
  have hindepConst : (fun _ : Ω => c) ⟂ᵢ[μ] Y :=
    indepFun_const_left c Y
  have hindep : X ⟂ᵢ[μ] Y :=
    IndepFun.congr hindepConst hconst.symm (by rfl)
  exact hindep.mutualInfo_eq_zero hX hY

/-- If the right variable is almost surely constant, its mutual information with any finite
variable is zero. -/
theorem mutualInfo_eq_zero_of_ae_eq_const_right
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y]
    (hX : Measurable X) (hY : Measurable Y) (c : T)
    (hconst : Y =ᵐ[μ] fun _ => c) :
    I[X : Y ; μ] = 0 := by
  rw [mutualInfo_comm hX hY]
  exact mutualInfo_eq_zero_of_ae_eq_const_left hY hX c hconst

open Classical in
/-- For finite alphabets, independence of two random variables follows from factorization on
singleton fibers. -/
theorem indepFun_of_measureReal_inter_preimage_singleton_eq_mul
    {Ω S T : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    [Finite S] [Finite T] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → S) (Y : Ω → T) (hX : Measurable X) (hY : Measurable Y)
    (h : ∀ x y,
      μ.real (X ⁻¹' {x} ∩ Y ⁻¹' {y}) =
        μ.real (X ⁻¹' {x}) * μ.real (Y ⁻¹' {y})) :
    IndepFun X Y μ := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]
  rw [Measure.ext_iff_measureReal_singleton_finiteSupport]
  rintro ⟨x, y⟩
  rw [MeasureTheory.map_measureReal_apply (hX.prodMk hY) MeasurableSet.of_discrete]
  rw [show (fun ω => (X ω, Y ω)) ⁻¹' ({(x, y)} : Set (S × T)) =
      X ⁻¹' ({x} : Set S) ∩ Y ⁻¹' ({y} : Set T) by
    ext ω
    simp [Prod.ext_iff]]
  rw [h x y]
  rw [show ({(x, y)} : Set (S × T)) = ({x} : Set S) ×ˢ ({y} : Set T) by
    ext z
    simp [Prod.ext_iff]]
  rw [MeasureTheory.measureReal_prod_prod]
  rw [MeasureTheory.map_measureReal_apply hX MeasurableSet.of_discrete]
  rw [MeasureTheory.map_measureReal_apply hY MeasurableSet.of_discrete]

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

/-- Conditional data processing where the right-side postprocessing may depend on the
conditioning value. -/
theorem condMutualInfo_comp_right_le_of_comp_conditioning
    {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (f : U → T → V) (hf : Measurable (Function.uncurry f)) :
    I[X : (fun ω => f (Z ω) (Y ω)) | Z ; μ] ≤ I[X : Y | Z ; μ] := by
  have hfZY : Measurable (fun ω => f (Z ω) (Y ω)) :=
    hf.comp (hZ.prodMk hY)
  rw [condMutualInfo_comm hX hfZY Z μ, condMutualInfo_comm hX hY Z μ]
  exact condMutualInfo_comp_left_le_of_comp_conditioning
    (μ := μ) (X := Y) (Y := X) (Z := Z)
    hY hX hZ f

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

/-- If a coarse conditioning variable is a deterministic function of a finer one, and the finer
conditioning variable carries no conditional information about `X` beyond the coarse variable,
then the finer conditioning can only increase `I[X : Y | -]`. -/
theorem condMutualInfo_comp_conditioning_le_of_condMutualInfo_eq_zero
    {W : Ω → V} (f : V → U)
    [IsZeroOrProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange W]
    (hX : Measurable X) (hY : Measurable Y) (hW : Measurable W) (hf : Measurable f)
    (hzero : I[X : W|f ∘ W;μ] = 0) :
    I[X : Y|f ∘ W;μ] ≤ I[X : Y|W;μ] := by
  let Z : Ω → U := f ∘ W
  have hZ : Measurable Z := hf.comp hW
  have hWZ :
      H[X | (fun ω => (W ω, Z ω)) ; μ] = H[X | W ; μ] := by
    let g : V → V × U := fun w => (w, f w)
    have hg : Function.Injective g := fun a b h => (Prod.ext_iff.1 h).1
    have hgW : Measurable (g ∘ W) := Measurable.of_discrete.comp hW
    simpa [g, Z, Function.comp_def] using
      condEntropy_of_injective' μ hX hW g hg hgW
  have hfirst : H[X | Z ; μ] = H[X | W ; μ] := by
    have hzero' : I[X : W | Z ; μ] = 0 := by
      simpa [Z] using hzero
    rw [condMutualInfo_eq' hX hW hZ μ, hWZ] at hzero'
    linarith
  have hsecond :
      H[X | (fun ω => (Y ω, W ω)) ; μ] ≤
        H[X | (fun ω => (Y ω, Z ω)) ; μ] := by
    let g : T × V → T × U := fun yw => (yw.1, f yw.2)
    have hg : Measurable g := Measurable.of_discrete
    simpa [g, Z, Function.comp_def] using
      condEntropy_comp_ge (μ := μ)
        (X := fun ω => (Y ω, W ω)) (Y := X)
        (hX := hY.prodMk hW) (hY := hX) g
  have hmain : I[X : Y | Z ; μ] ≤ I[X : Y | W ; μ] := by
    rw [condMutualInfo_eq' hX hY hZ μ,
      condMutualInfo_eq' hX hY hW μ]
    linarith
  simpa [Z, Function.comp_def] using hmain

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

/-- Conditional mutual information is unchanged by injective recodings of the right variable
and the conditioning variable. -/
theorem condMutualInfo_comp_right_conditioning_of_injective
    {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
    [MeasurableSingletonClass V] [MeasurableSingletonClass W]
    [Countable V] [Countable W]
    {f : T → V} {g : U → W}
    [IsProbabilityMeasure μ] [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hfmeas : Measurable f) (hgmeas : Measurable g)
    (hfinj : Function.Injective f) (hginj : Function.Injective g) :
    I[X : f ∘ Y | g ∘ Z ; μ] = I[X : Y | Z ; μ] := by
  have hY' : Measurable (f ∘ Y) := hfmeas.comp hY
  have hZ' : Measurable (g ∘ Z) := hgmeas.comp hZ
  rw [_root_.ProbabilityTheory.condMutualInfo_eq (μ := μ) hX hY' hZ',
    _root_.ProbabilityTheory.condMutualInfo_eq (μ := μ) hX hY hZ]
  have hXcond :
      H[X | g ∘ Z ; μ] = H[X | Z ; μ] :=
    condEntropy_of_injective' μ hX hZ g hginj hZ'
  have hYcond :
      H[f ∘ Y | g ∘ Z ; μ] = H[Y | Z ; μ] := by
    rw [condEntropy_comp_of_injective μ hY f hfinj]
    exact condEntropy_of_injective' μ hY hZ g hginj hZ'
  have hpaircond :
      H[(fun ω => (X ω, (f ∘ Y) ω)) | g ∘ Z ; μ] =
        H[(fun ω => (X ω, Y ω)) | Z ; μ] := by
    have hrec :
        H[(fun ω => (X ω, (f ∘ Y) ω)) | g ∘ Z ; μ] =
          H[(fun ω => (X ω, Y ω)) | g ∘ Z ; μ] := by
      change
        H[(fun p : S × T => (p.1, f p.2)) ∘ (fun ω => (X ω, Y ω)) |
            g ∘ Z ; μ] =
          H[(fun ω => (X ω, Y ω)) | g ∘ Z ; μ]
      exact condEntropy_comp_of_injective μ (hX.prodMk hY)
        (fun p : S × T => (p.1, f p.2))
        (by
          intro a b h
          exact Prod.ext (Prod.ext_iff.mp h).1 (hfinj (Prod.ext_iff.mp h).2))
    rw [hrec]
    exact condEntropy_of_injective' μ (hX.prodMk hY) hZ g hginj hZ'
  rw [hXcond, hYcond, hpaircond]

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- If `(X, Y)` and `(X', Y')` have the same joint law, then conditioning on the same measurable
event in the `Y`/`Y'` coordinate preserves the law of `X`/`X'`. This is the heterogeneous-codomain
version of `ProbabilityTheory.IdentDistrib.cond`. -/
theorem IdentDistrib.cond_of_pair
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    {X : Ω → A} {Y : Ω → B} {X' : Ω' → A} {Y' : Ω' → B}
    {s : Set B}
    (hs : MeasurableSet s) (hY : Measurable Y) (hY' : Measurable Y')
    (h : IdentDistrib (fun ω => (X ω, Y ω)) (fun ω => (X' ω, Y' ω)) μ μ') :
    IdentDistrib X X' (μ[|Y ⁻¹' s]) (μ'[|Y' ⁻¹' s]) where
  aemeasurable_fst :=
    (measurable_fst.aemeasurable.comp_aemeasurable h.aemeasurable_fst).mono_ac
      cond_absolutelyContinuous
  aemeasurable_snd :=
    (measurable_fst.aemeasurable.comp_aemeasurable h.aemeasurable_snd).mono_ac
      cond_absolutelyContinuous
  map_eq := by
    ext t ht
    have hXae : AEMeasurable X μ := by
      simpa only [Function.comp_def] using
        measurable_fst.aemeasurable.comp_aemeasurable h.aemeasurable_fst
    have hX'ae : AEMeasurable X' μ' := by
      simpa only [Function.comp_def] using
        measurable_fst.aemeasurable.comp_aemeasurable h.aemeasurable_snd
    rw [map_apply₀
        (hXae.mono_ac cond_absolutelyContinuous)
        ht.nullMeasurableSet,
      map_apply₀
        (hX'ae.mono_ac cond_absolutelyContinuous)
        ht.nullMeasurableSet,
      cond_apply (hY' hs), cond_apply (hY hs)]
    congr
    · simpa only [
        map_apply₀ (h.comp measurable_snd).aemeasurable_fst hs.nullMeasurableSet,
        map_apply₀ (h.comp measurable_snd).aemeasurable_snd hs.nullMeasurableSet] using
        congr_fun (congr_arg (⇑) (h.comp measurable_snd).map_eq) s
    · rw [inter_comm, inter_comm (Y' ⁻¹' _)]
      simpa only [
        map_apply₀ h.aemeasurable_fst (ht.prod hs).nullMeasurableSet,
        map_apply₀ h.aemeasurable_snd (ht.prod hs).nullMeasurableSet] using
        congr_fun (congr_arg (⇑) h.map_eq) (t ×ˢ s)

end ProbabilityTheory
