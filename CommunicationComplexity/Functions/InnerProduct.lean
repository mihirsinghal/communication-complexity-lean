import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Integral.Prod
import CommunicationComplexity.Helper
import CommunicationComplexity.CoinTape
import CommunicationComplexity.PublicCoin.Discrepancy
import CommunicationComplexity.Rectangle.Basic

namespace CommunicationComplexity

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators

namespace Functions.InnerProduct

noncomputable section

local instance boolInputFiniteProbabilitySpace (n : ℕ) :
    FiniteProbabilitySpace (BoolInput n) := by
  change FiniteProbabilitySpace (CoinTape n)
  infer_instance

/-- The coordinates on which both bit-vectors are `true`. -/
def overlap (x y : BoolInput n) : Finset (Fin n) :=
  Finset.univ.filter fun i : Fin n => x i && y i

/-- The mod-2 inner product of two `n`-bit vectors: it is `true` exactly when the number
of coordinates where both inputs are `true` is odd. -/
def innerProduct (n : ℕ) (x y : BoolInput n) : Bool :=
  ∑ i, (x i && y i)

@[simp] lemma innerProduct_zero_right (x : BoolInput n) :
    innerProduct n x (zeroInput n) = false := by
  unfold innerProduct zeroInput
  refine Finset.sum_eq_zero ?_
  intro i hi
  cases hxi : x i <;> decide

/-- Every `n`-bit input has uniform weight `2^{-n}`. -/
private lemma pmf_toReal_eq_two_pow_inv (x : BoolInput n) :
    (FiniteProbabilitySpace.toPMF (BoolInput n) x).toReal = (1 : ℝ) / 2 ^ n := by
  classical
  change (volume (Set.singleton x : Set (BoolInput n))).toReal = (1 : ℝ) / 2 ^ n
  change (((ProbabilityTheory.uniformOn Set.univ : Measure (BoolInput n)) (Set.singleton x)).toReal
    = (1 : ℝ) / 2 ^ n)
  rw [ProbabilityTheory.uniformOn_univ, ENNReal.toReal_div]
  have hcount : (Measure.count (Set.singleton x)).toReal = 1 := by
    unfold Set.singleton
    simp
  have hcard :
      (↑(Fintype.card (BoolInput n)) : ENNReal).toReal = 2 ^ n := by
    simp [BoolInput, Fintype.card_pi, Fintype.card_fin, Fintype.card_bool]
  rw [hcount]
  rw [hcard]

/-- Integrals against the uniform distribution on `BoolInput n` are averages over all inputs. -/
private lemma integral_eq_average_sum (f : BoolInput n → ℝ) :
    ∫ x, f x = ((1 : ℝ) / 2 ^ n) * ∑ x, f x := by
  rw [FiniteProbabilitySpace.integral_eq_pmf_sum]
  simp_rw [pmf_toReal_eq_two_pow_inv]
  rw [Finset.mul_sum]

/-- Flipping a coordinate where `y` has a `1` toggles the inner product. -/
lemma innerProduct_flipAt_eq_xor (x y : BoolInput n) (i : Fin n) (hyi : y i = true) :
    innerProduct n (flipAt i x) y = Bool.xor (innerProduct n x y) true := by
  classical
  have hflip :
      innerProduct n (flipAt i x) y = innerProduct n x y - x i + !x i := by
    calc
      innerProduct n (flipAt i x) y
        = Finset.sum (Finset.univ.erase i) (fun j : Fin n => flipAt i x j && y j) +
            (flipAt i x i && y i) := by
              unfold innerProduct
              simp [add_comm]
      _ = Finset.sum (Finset.univ.erase i) (fun j : Fin n => x j && y j) + !x i := by
            congr 1
            · refine Finset.sum_congr rfl ?_
              intro j hj
              have hji : j ≠ i := (Finset.mem_erase.mp hj).1
              simp [flipAt, hji]
            · simp [flipAt, hyi]
      _ = innerProduct n x y - x i + !x i := by
            rw [show innerProduct n x y =
                Finset.sum (Finset.univ.erase i) (fun j : Fin n => x j && y j) + x i by
                  unfold innerProduct
                  simp [hyi, add_comm]]
            cases hxi : x i <;> simp [hxi]
  rw [hflip]
  cases hsum : innerProduct n x y <;> cases hxi : x i <;> decide

/-- Orthogonality of Walsh characters for the inner product function. -/
private lemma sum_boolSign_innerProduct_eq_zero_of_exists_true
    (z : BoolInput n) {i : Fin n} (hzi : z i = true) :
    ∑ x : BoolInput n, boolSign (innerProduct n x z) = 0 := by
  let S : ℝ := ∑ x : BoolInput n, boolSign (innerProduct n x z)
  have hperm :
      S = ∑ x : BoolInput n, boolSign (innerProduct n (flipAt i x) z) := by
    unfold S
    symm
    exact Fintype.sum_bijective (flipAt i) (flipAt_bijective i)
      (fun x => boolSign (innerProduct n (flipAt i x) z))
      (fun x => boolSign (innerProduct n x z))
      (fun x => rfl)
  have hneg :
      (∑ x : BoolInput n, boolSign (innerProduct n (flipAt i x) z)) = -S := by
    unfold S
    have hpoint :
        ∀ x : BoolInput n,
          boolSign (innerProduct n (flipAt i x) z) = -boolSign (innerProduct n x z) := by
      intro x
      rw [innerProduct_flipAt_eq_xor x z i hzi, boolSign_xor]
      norm_num [boolSign]
    rw [show (∑ x : BoolInput n, boolSign (innerProduct n (flipAt i x) z)) =
      ∑ x : BoolInput n, -boolSign (innerProduct n x z) by
        refine Finset.sum_congr rfl ?_
        intro x hx
        exact hpoint x]
    simp
  have hEq : S = -S := hperm.trans hneg
  linarith

/-- The Walsh character for `z` sums to `2^n` at the zero vector and to `0` elsewhere. -/
private lemma sum_boolSign_innerProduct_eq_zeroInput_indicator
    (z : BoolInput n) :
    ∑ x : BoolInput n, boolSign (innerProduct n x z) =
      if z = zeroInput n then 2 ^ n else 0 := by
  by_cases hz : z = zeroInput n
  · subst hz
    simp [innerProduct_zero_right, boolSign]
  · obtain ⟨i, hzi⟩ := exists_true_of_ne_zeroInput hz
    simp [hz, sum_boolSign_innerProduct_eq_zero_of_exists_true z hzi]

/-- Coordinatewise xor of two Boolean inputs. -/
def xorInput (y z : BoolInput n) : BoolInput n :=
  fun i => Bool.xor (y i) (z i)

@[simp] private lemma xorInput_apply (y z : BoolInput n) (i : Fin n) :
    xorInput y z i = Bool.xor (y i) (z i) := rfl

@[simp] private lemma xorInput_eq_zeroInput_iff (y z : BoolInput n) :
    xorInput y z = zeroInput n ↔ y = z := by
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    cases hy : y i <;> cases hz : z i <;> simp [xorInput, zeroInput, hy, hz] at hi ⊢
  · intro h
    subst h
    funext i
    simp [xorInput, zeroInput]

/-- The Walsh character for inner product is multiplicative in the second argument under xor. -/
private lemma boolSign_innerProduct_mul_eq_xorInput
    (x y z : BoolInput n) :
    boolSign (innerProduct n x y) * boolSign (innerProduct n x z) =
      boolSign (innerProduct n x (xorInput y z)) := by
  rw [innerProduct, innerProduct, innerProduct, boolSign_sum, boolSign_sum, boolSign_sum]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro i hi
  cases hx : x i <;> cases hy : y i <;> cases hz : z i <;>
    simp [xorInput, boolSign, hy, hz]

/-- On the uniform distribution over `BoolInput n`, the square of an expectation is bounded by
the expectation of the square. -/
private lemma sq_integral_le_integral_sq
    (f : BoolInput n → ℝ) :
    (∫ x : BoolInput n, f x)^2 ≤ ∫ x : BoolInput n, (f x)^2 := by
  have hsq :
      (∫ x : BoolInput n, f x)^2 ≤ ∫ x : BoolInput n, (f x)^2 :=
    ConvexOn.map_integral_le
      (by simpa using (show ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) from
        Even.convexOn_pow (𝕜 := ℝ) (by decide : Even 2)))
      (by simpa using
        (show ContinuousOn (fun x : ℝ => x ^ 2) Set.univ from
          (continuous_pow 2).continuousOn))
      isClosed_univ
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
      Integrable.of_finite
      Integrable.of_finite
  simpa [pow_two] using hsq

/-- Summed orthogonality for Walsh characters. -/
private lemma sum_boolSign_innerProduct_mul_eq_indicator
    (y z : BoolInput n) :
    ∑ x : BoolInput n, boolSign (innerProduct n x y) * boolSign (innerProduct n x z) =
      if y = z then 2 ^ n else 0 := by
  calc
    ∑ x : BoolInput n, boolSign (innerProduct n x y) * boolSign (innerProduct n x z)
      = ∑ x : BoolInput n, boolSign (innerProduct n x (xorInput y z)) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          exact boolSign_innerProduct_mul_eq_xorInput x y z
    _ = if xorInput y z = zeroInput n then 2 ^ n else 0 :=
          sum_boolSign_innerProduct_eq_zeroInput_indicator (n := n) (xorInput y z)
    _ = if y = z then 2 ^ n else 0 := by
          simp [xorInput_eq_zeroInput_iff]

private lemma indicatorOne_sq
    (B : Set (BoolInput n)) (y : BoolInput n) :
    (Set.indicator B (1 : BoolInput n → ℝ) y)^2 =
      Set.indicator B (1 : BoolInput n → ℝ) y := by
  by_cases hy : y ∈ B <;> simp [hy, pow_two]

private lemma indicatorOne_le_one
    (B : Set (BoolInput n)) (y : BoolInput n) :
    Set.indicator B (1 : BoolInput n → ℝ) y ≤ 1 := by
  by_cases hy : y ∈ B <;> simp [hy]

open Classical in
private lemma sum_sq_eq_sum_prod
    {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    ∑ x : α, (∑ y : β, f x y)^2 =
      ∑ yz : β × β, ∑ x : α, f x yz.1 * f x yz.2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro _ _
  simp only [pow_two, Fintype.sum_mul_sum]
  rw [eq_comm]
  apply Fintype.sum_prod_type

private lemma sum_mul_mul
    {α : Type*} [Fintype α] (a b : ℝ) (f g : α → ℝ) :
    ∑ x : α, (a * f x) * (b * g x) = a * b * ∑ x : α, f x * g x := by
  conv =>
    enter [1, 2, x]
    equals (a * b) * (f x * g x) => ring
  rw [Finset.mul_sum]

private lemma sum_mul_ite_eq_diag
    {α : Type*} [Fintype α] [DecidableEq α] (h : α → α → ℝ) (c : ℝ) :
    ∑ yz : α × α, h yz.1 yz.2 * (if yz.1 = yz.2 then c else 0) =
      ∑ y : α, h y y * c := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro y hy
  simp

/-- A weighted orthogonality identity for a finite family of functions. -/
private lemma sum_sq_mul_of_orthogonal
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (φ : α → β → ℝ) (c : ℝ) (b : β → ℝ)
    (horth : ∀ y z, ∑ x : α, φ x y * φ x z = if y = z then c else 0) :
    ∑ x : α, (∑ y : β, b y * φ x y)^2 =
      ∑ y : β, (b y)^2 * c := by
  rw [sum_sq_eq_sum_prod]
  conv =>
    enter [1, 2, yz]
    rw [sum_mul_mul]
    rw [horth]
  rw [sum_mul_ite_eq_diag (fun y z => b y * b z)]
  refine Finset.sum_congr rfl ?_
  ring_nf
  simp

open Classical in
/-- Weighted orthogonality identity for Walsh characters of inner product. -/
private lemma sum_sq_mul_boolSign_innerProduct
    (b : BoolInput n → ℝ) :
    ∑ x : BoolInput n,
      (∑ y : BoolInput n, b y * boolSign (innerProduct n x y))^2 =
      ∑ y : BoolInput n, (b y)^2 * (2 ^ n : ℝ) := by
  refine sum_sq_mul_of_orthogonal
    (fun x y => boolSign (innerProduct n x y))
    (2 ^ n) b ?_
  intro y z
  simpa [mul_assoc] using sum_boolSign_innerProduct_mul_eq_indicator (n := n) y z

open Classical in
/-- The inner second moment appearing in the discrepancy calculation is at most `2^{-n}`. -/
private lemma sum_sq_indicator_mul_boolSign_innerProduct_le
    (B : Set (BoolInput n)) :
    ∑ x : BoolInput n,
      (∑ y : BoolInput n, Set.indicator B 1 y * boolSign (innerProduct n x y))^2 ≤
      (2 ^ n : ℝ)^2 := by
  rw [sum_sq_mul_boolSign_innerProduct (n := n) (b := Set.indicator B 1)]
  have hdiag_bound :
      ∑ y : BoolInput n, (Set.indicator B 1 y)^2 * (2 ^ n : ℝ) ≤
        ∑ y : BoolInput n, 1 * (2 ^ n : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro y hy
    rw [indicatorOne_sq B y]
    gcongr
    exact indicatorOne_le_one B y
  calc
    ∑ y : BoolInput n, (Set.indicator B 1 y)^2 * (2 ^ n : ℝ)
      ≤ ∑ y : BoolInput n, 1 * (2 ^ n : ℝ) := hdiag_bound
    _ = (2 ^ n : ℝ)^2 := by
      simp [BoolInput, Fintype.card_pi, Fintype.card_fin, Fintype.card_bool, pow_two]

open Classical in
private lemma integral_sq_indicator_mul_boolSign_innerProduct_eq
    (B : Set (BoolInput n)) :
    ∫ x : BoolInput n,
      (∫ y : BoolInput n,
        (if y ∈ B then (1 : ℝ) else 0) * boolSign (innerProduct n x y))^2 =
      ((1 : ℝ) / 2 ^ n)^3 *
        ∑ x : BoolInput n,
          (∑ y : BoolInput n,
            (Set.indicator B 1 y) * boolSign (innerProduct n x y))^2 := by
  let b : BoolInput n → ℝ := Set.indicator B 1
  have hinner :
      (fun x : BoolInput n =>
        (∫ y : BoolInput n,
          (if y ∈ B then (1 : ℝ) else 0) * boolSign (innerProduct n x y))^2) =
      fun x : BoolInput n =>
        (∫ y : BoolInput n, b y * boolSign (innerProduct n x y))^2 := by
      ext x
      have hpoint :
          (fun y : BoolInput n =>
            if y ∈ B then boolSign (innerProduct n x y) else 0) =
          fun y : BoolInput n =>
            b y * boolSign (innerProduct n x y) := by
              ext y
              simp [b, Set.indicator_apply]
      simpa using congrArg (fun F => (∫ y : BoolInput n, F y)^2) hpoint
  rw [hinner]
  rw [integral_eq_average_sum]
  simp_rw [integral_eq_average_sum]
  have hscale :
      ∑ x : BoolInput n,
        (((1 : ℝ) / 2 ^ n) *
          ∑ y : BoolInput n, b y * boolSign (innerProduct n x y))^2 =
      ((1 : ℝ) / 2 ^ n)^2 *
        ∑ x : BoolInput n,
          (∑ y : BoolInput n, b y * boolSign (innerProduct n x y))^2 := by
    simp_rw [mul_pow]
    rw [← Finset.mul_sum]
  rw [hscale]
  ring

open Classical in
/-- The inner second moment appearing in the discrepancy calculation is at most `2^{-n}`. -/
private lemma integral_sq_indicator_mul_boolSign_innerProduct_le
    (B : Set (BoolInput n)) :
    ∫ x : BoolInput n,
      (∫ y : BoolInput n,
        (if y ∈ B then (1 : ℝ) else 0) * boolSign (innerProduct n x y))^2 ≤
      (1 : ℝ) / 2 ^ n := by
  rw [integral_sq_indicator_mul_boolSign_innerProduct_eq]
  have hnonneg : 0 ≤ ((1 : ℝ) / 2 ^ n)^3 := by
    positivity
  have hmain :=
    mul_le_mul_of_nonneg_left
      (sum_sq_indicator_mul_boolSign_innerProduct_le (n := n) B) hnonneg
  have hpow : (2 : ℝ) ^ n ≠ 0 := by positivity
  calc
    ((1 : ℝ) / 2 ^ n)^3 *
        ∑ x : BoolInput n,
          (∑ y : BoolInput n, Set.indicator B 1 y * boolSign (innerProduct n x y))^2
      ≤ ((1 : ℝ) / 2 ^ n)^3 * (2 ^ n : ℝ)^2 := hmain
    _ = (1 : ℝ) / 2 ^ n := by
        field_simp [hpow]

open Classical in
private lemma discrepancy_prod_eq_integral
    (A B : Set (BoolInput n)) :
    discrepancy (innerProduct n) (A ×ˢ B : Set (BoolInput n × BoolInput n)) =
      ∫ x : BoolInput n,
        (if x ∈ A then (1 : ℝ) else 0) *
          ∫ y : BoolInput n,
            (if y ∈ B then (1 : ℝ) else 0) * boolSign (innerProduct n x y) := by
  rw [discrepancy]
  simp_rw [Set.mem_prod]
  rw [show (volume : Measure (BoolInput n × BoolInput n)) =
    (volume : Measure (BoolInput n)).prod (volume : Measure (BoolInput n)) from rfl]
  rw [MeasureTheory.integral_prod _ (Integrable.of_finite)]
  refine integral_congr_ae ?_
  filter_upwards with x
  by_cases hx : x ∈ A <;> simp [hx]

open Classical in
private lemma sq_discrepancy_prod_le
    (A B : Set (BoolInput n)) :
    (discrepancy (innerProduct n) (A ×ˢ B : Set (BoolInput n × BoolInput n)))^2 ≤
      (1 : ℝ) / 2 ^ n := by
  rw [discrepancy_prod_eq_integral]
  calc
    (∫ x : BoolInput n,
        (if x ∈ A then (1 : ℝ) else 0) *
          ∫ y : BoolInput n,
            (if y ∈ B then (1 : ℝ) else 0) * boolSign (innerProduct n x y))^2
      ≤ ∫ x : BoolInput n,
          ((if x ∈ A then (1 : ℝ) else 0) *
            ∫ y : BoolInput n,
              (if y ∈ B then (1 : ℝ) else 0) * boolSign (innerProduct n x y))^2 :=
        sq_integral_le_integral_sq (n := n) _
    _ ≤ ∫ x : BoolInput n,
          (∫ y : BoolInput n,
            (if y ∈ B then (1 : ℝ) else 0) * boolSign (innerProduct n x y))^2 := by
          refine MeasureTheory.integral_mono_ae (Integrable.of_finite) (Integrable.of_finite) ?_
          filter_upwards with x
          by_cases hx : x ∈ A
          · simp [hx]
          · simp only [hx, ite_mul, zero_mul, ite_pow, ne_eq, OfNat.ofNat_ne_zero,
              not_false_eq_true, zero_pow]
            positivity
    _ ≤ (1 : ℝ) / 2 ^ n :=
        integral_sq_indicator_mul_boolSign_innerProduct_le (n := n) B

open Classical in
/-- Every rectangle has discrepancy at most `2^{-n/2}` for the inner product function over the
uniform distribution on `BoolInput n × BoolInput n`. -/
theorem abs_discrepancy_le_of_isRectangle
    (R : Set (BoolInput n × BoolInput n)) (hR : Rectangle.IsRectangle R) :
    |discrepancy (innerProduct n) R| ≤ Real.sqrt ((1 : ℝ) / 2 ^ n) := by
  rcases hR with ⟨A, B, rfl⟩
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  simpa [sq_abs, Real.sq_sqrt (show 0 ≤ (1 : ℝ) / 2 ^ n by positivity)] using
    sq_discrepancy_prod_le (n := n) A B

open Classical in
/-- Public-coin lower bound for inner product from the discrepancy method. -/
theorem publicCoin_le_communicationComplexity_of_hbound
    (k n : ℕ) {ε : ℝ}
    (hbound : (2 : ℝ) ^ k * Real.sqrt ((1 : ℝ) / 2 ^ n) < 1 - 2 * ε) :
    k < PublicCoin.communicationComplexity (innerProduct n) ε := by
  refine PublicCoin.communicationComplexity_lower_bound_of_discrepancy
    (μ := inferInstance) (g := innerProduct n) (ε := ε)
    (γ := Real.sqrt ((1 : ℝ) / 2 ^ n)) (n := k) ?_ hbound
  intro R hR
  exact abs_discrepancy_le_of_isRectangle (n := n) R hR

end

end Functions.InnerProduct

end CommunicationComplexity
