import CommunicationComplexity.PrivateCoin.Basic
import CommunicationComplexity.FiniteProbabilitySpace
import CommunicationComplexity.PrivateCoin.FiniteMessage
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.ENNReal.Basic

/-!
# Coin Approximation

Any finite discrete probability space can be approximated by coin flips.
This is the key ingredient for showing that protocols over arbitrary
finite probability spaces can be simulated by CoinTape protocols.
-/

open MeasureTheory
open scoped ENNReal

namespace CommunicationComplexity

namespace Internal

def cdf {m : ℕ} (p : PMF (Fin m)) (n : ℕ) : ℝ≥0∞ :=
  ∑ j : Fin m, if j < n then p j else 0

@[simp] lemma cdf_zero {m : ℕ} (p : PMF (Fin m)) :
    cdf p 0 = 0 := by
  simp [cdf]

lemma cdf_succ {m : ℕ} (p : PMF (Fin m)) (n : Fin m) :
    cdf p (n + 1) = cdf p n + p n := by
  simp only [cdf]
  -- Split: ∑ (if j < n+1 ...) = ∑ (if j < n ...) + ∑ (if j = n ...)
  have key : ∀ j : Fin m,
      (if (j : ℕ) < (n : ℕ) + 1 then (p j : ℝ≥0∞) else 0) =
      (if (j : ℕ) < (n : ℕ) then p j else 0) +
      (if j = n then p n else 0) := by
    intro j
    split_ifs with h1 h2 <;> simp_all <;> omega
  simp_rw [key, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

lemma cdf_one {m : ℕ} (p : PMF (Fin m)) :
    cdf p m = 1 := by
  simp only [cdf, Fin.is_lt, ↓reduceIte]
  have hsum := PMF.tsum_coe p
  simp only [tsum_fintype] at hsum
  exact hsum

lemma cdf_mono {m : ℕ} (p : PMF (Fin m)) :
    Monotone (cdf p) := by
  intro i j hij
  unfold cdf
  apply Finset.sum_le_sum
  intro k _
  split_ifs with h1 h2 <;> first | exact le_refl _ | exact absurd (lt_of_lt_of_le h1 hij) h2 | exact zero_le _

noncomputable def invCdf {m : ℕ} [NeZero m] (p : PMF (Fin m)) (x : ℝ≥0∞) : Fin m :=
  (Finset.univ.filter (fun (i : Fin m) => cdf p i ≤ x)).max' (by
    unfold Finset.Nonempty
    have _ := NeZero.ne m
    refine ⟨(⟨0, by omega⟩ : Fin m), ?_⟩
    simp
  )

theorem invCdf_eq_iff {m : ℕ} [NeZero m] (p : PMF (Fin m)) (x : ℝ≥0∞) (hx : x < 1) (i : Fin m) :
    invCdf p x = i ↔ cdf p i ≤ x ∧ x < cdf p (i + 1) := by
  constructor
  · intro h
    unfold invCdf at h
    rw [Finset.max'_eq_iff] at h
    constructor
    · have h := h.1
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
      exact h
    · have h := h.2
      by_cases hi : i + 1 < m
      · specialize h ⟨i + 1, hi⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
        by_contra hcontra
        rw [not_lt] at hcontra
        specialize h hcontra
        rw [← Fin.val_fin_le] at h
        simp at h
      · have hi : i + 1 = m := by omega
        rw [hi, cdf_one]
        trivial
  · rintro ⟨hlo, hhi⟩
    unfold invCdf
    rw [Finset.max'_eq_iff]
    constructor
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hlo
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      have hlt := lt_of_le_of_lt hb hhi
      have hmono := Monotone.reflect_lt (cdf_mono p) hlt
      omega

noncomputable def uniformApprox {m : ℕ} [NeZero m] (p : PMF (Fin m)) (n : ℕ) [NeZero n] : (Fin n) → (Fin m) :=
  fun i => invCdf p ((i : ℝ≥0∞) / n)

/-- The number of naturals in [a, b) is at most ⌊b⌋ - ⌈a⌉ + 1 ≤ b - a + 1. -/
private lemma card_nat_in_Ico (n : ℕ) (a b : ℝ) (hab : a ≤ b) :
    ((Finset.univ.filter (fun j : Fin n =>
      a ≤ (j : ℝ) ∧ (j : ℝ) < b)).card : ℝ) ≤ b - a + 1 := by
  by_cases hS : (Finset.univ.filter (fun j : Fin n =>
      a ≤ (j : ℝ) ∧ (j : ℝ) < b)).card = 0
  · simp [hS]; linarith
  set S := Finset.univ.filter (fun j : Fin n => a ≤ (j : ℝ) ∧ (j : ℝ) < b)
  have hne : S.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hS)
  set jlo := (S.min' hne : ℕ)
  set jhi := (S.max' hne : ℕ)
  have hlo_mem := Finset.min'_mem S hne
  have hhi_mem := Finset.max'_mem S hne
  have hlo_ge : a ≤ jlo := ((Finset.mem_filter.mp hlo_mem).2).1
  have hhi_lt : (jhi : ℝ) < b := ((Finset.mem_filter.mp hhi_mem).2).2
  have hle : jlo ≤ jhi := (Finset.min'_le S _ hhi_mem)
  -- S maps injectively (via Fin.val) into Finset.Icc jlo jhi in ℕ
  have hcard_le : S.card ≤ jhi - jlo + 1 := by
    calc S.card
        = (Finset.image Fin.val S).card :=
          (Finset.card_image_of_injective _ Fin.val_injective).symm
      _ ≤ (Finset.Icc jlo jhi).card := by
          apply Finset.card_le_card
          intro k hk
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
          exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hj, Finset.le_max' _ _ hj⟩
      _ = jhi - jlo + 1 := by simp; omega
  calc (S.card : ℝ) ≤ (jhi - jlo + 1 : ℕ) := by exact_mod_cast hcard_le
    _ = (jhi : ℝ) - (jlo : ℝ) + 1 := by
        rw [Nat.cast_add, Nat.cast_sub hle]; simp
    _ ≤ b - a + 1 := by linarith

/-- The number of elements j ∈ Fin n with j/n ∈ [a, b) is at most
(b - a) * n + 1 when a ≤ b ≤ 1. -/
private lemma card_div_in_interval (n : ℕ) [NeZero n] (a b : ℝ≥0∞)
    (hab : a ≤ b) (hb : b ≤ 1) :
    (Finset.card (Finset.univ.filter (fun j : Fin n =>
      a ≤ (j : ℝ≥0∞) / n ∧ (j : ℝ≥0∞) / n < b)) : ℝ≥0∞) ≤
      (b - a) * n + 1 := by
  have ha_fin : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (hab.trans hb)
  have hb_fin : b ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hb
  have hab_real : a.toReal ≤ b.toReal := ENNReal.toReal_le_toReal ha_fin hb_fin |>.mpr hab
  -- The ENNReal set ⊆ the ℝ set
  have hsub : Finset.univ.filter (fun j : Fin n =>
      a ≤ (j : ℝ≥0∞) / n ∧ (j : ℝ≥0∞) / n < b) ⊆
    Finset.univ.filter (fun j : Fin n =>
      a.toReal * n ≤ (j : ℝ) ∧ (j : ℝ) < b.toReal * n) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    obtain ⟨h1, h2⟩ := hj
    constructor
    · -- a ≤ j/n → a * n ≤ j → a.toReal * n ≤ j (in ℝ)
      have h1' : a * n ≤ j := by
        rwa [ENNReal.le_div_iff_mul_le (by simp [NeZero.ne n]) (by simp)] at h1
      calc a.toReal * n = (a * n).toReal := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
        _ ≤ (j : ℝ≥0∞).toReal :=
            ENNReal.toReal_mono (by simp) h1'
        _ = j := by simp
    · -- j/n < b → j < b * n → j < b.toReal * n (in ℝ)
      have h2' : (j : ℝ≥0∞) < b * n := by
        rwa [ENNReal.div_lt_iff (by left; simp [NeZero.ne n]) (by left; simp)] at h2
      calc (j : ℝ) = (j : ℝ≥0∞).toReal := by simp
        _ < (b * n).toReal :=
            (ENNReal.toReal_lt_toReal (by simp)
              (ENNReal.mul_ne_top hb_fin (ENNReal.natCast_ne_top n))).mpr h2'
        _ = b.toReal * n := by rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
  -- Apply the ℝ counting lemma
  have hR := card_nat_in_Ico n (a.toReal * n) (b.toReal * n)
    (mul_le_mul_of_nonneg_right hab_real (Nat.cast_nonneg _))
  -- Combine: card (ENNReal set) ≤ (b.toReal - a.toReal) * n + 1 in ℝ
  have hcard_real : ((Finset.univ.filter (fun j : Fin n =>
      a ≤ (j : ℝ≥0∞) / n ∧ (j : ℝ≥0∞) / n < b)).card : ℝ) ≤
      (b.toReal - a.toReal) * n + 1 := by
    calc _ ≤ ((Finset.univ.filter (fun j : Fin n =>
        a.toReal * n ≤ (j : ℝ) ∧ (j : ℝ) < b.toReal * n)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ b.toReal * n - a.toReal * n + 1 := hR
      _ = (b.toReal - a.toReal) * n + 1 := by ring
  -- Convert ℝ bound to ENNReal
  -- hcard_real has b.toReal - a.toReal; rewrite to (b-a).toReal
  rw [show b.toReal - a.toReal = (b - a).toReal from
    (ENNReal.toReal_sub_of_le hab hb_fin).symm] at hcard_real
  calc ((Finset.univ.filter _).card : ℝ≥0∞)
      = ENNReal.ofReal ↑(Finset.univ.filter _).card := by rw [ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((b - a).toReal * n + 1) := ENNReal.ofReal_le_ofReal hcard_real
    _ = (b - a) * n + 1 := by
        rw [ENNReal.ofReal_add (mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)) (by norm_num),
          ENNReal.ofReal_one, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (tsub_le_self.trans hb)),
          ENNReal.ofReal_natCast]

theorem uniformApprox_approx {m : ℕ} [NeZero m] (p : PMF (Fin m)) (n : ℕ) [NeZero n] (i : Fin m) :
    (Finset.card {j : Fin n | uniformApprox p n j = i} : ℝ≥0∞) / (n : ℝ≥0∞) ≤ (p i) + 1 / (n : ℝ≥0∞) := by
  -- Characterize the preimage using invCdf_eq_iff
  have hset : Finset.univ.filter (fun j : Fin n => uniformApprox p n j = i) ⊆
      Finset.univ.filter (fun j : Fin n =>
        cdf p i ≤ (j : ℝ≥0∞) / n ∧ (j : ℝ≥0∞) / n < cdf p (i + 1)) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      uniformApprox] at hj ⊢
    have hlt : (j : ℝ≥0∞) / n < 1 := by
      rw [ENNReal.div_lt_iff (by simp [NeZero.ne n]) (by simp)]
      simp [show (j : ℕ) < n from j.isLt]
    exact (invCdf_eq_iff p _ hlt i).mp hj
  -- Bound cardinality of the preimage
  have hcard := Finset.card_le_card hset
  -- Rewrite LHS to use the filter form
  have hcard_eq : Finset.card {j : Fin n | uniformApprox p n j = i} =
      (Finset.univ.filter (fun j : Fin n => uniformApprox p n j = i)).card := by
    rfl
  -- Use the interval counting lemma
  have hcdf_le : cdf p i ≤ cdf p (i + 1) := cdf_mono p (Nat.le_succ _)
  have hcdf_le1 : cdf p (i + 1) ≤ 1 := by
    calc cdf p (i + 1) ≤ cdf p m := cdf_mono p (by omega)
      _ = 1 := cdf_one p
  have hint := card_div_in_interval n (cdf p i) (cdf p (i + 1)) hcdf_le hcdf_le1
  -- cdf p (i+1) - cdf p i = p i
  have hdiff : cdf p (↑i + 1) - cdf p i = p i := by
    rw [cdf_succ]
    exact ENNReal.add_sub_cancel_left
      (ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans (cdf_mono p (Nat.le_succ _)) hcdf_le1))
  rw [hdiff] at hint
  -- Combine: card / n ≤ (p i * n + 1) / n = p i + 1/n
  rw [hcard_eq]
  calc ((Finset.univ.filter (fun j : Fin n => uniformApprox p n j = i)).card : ℝ≥0∞) / n
      ≤ ((Finset.univ.filter _).card : ℝ≥0∞) / n :=
        ENNReal.div_le_div_right (by exact_mod_cast hcard) n
    _ ≤ (p i * n + 1) / n := ENNReal.div_le_div_right hint n
    _ = p i + 1 / n := by
        rw [ENNReal.add_div]
        congr 1
        rw [mul_comm, mul_div_assoc]
        exact ENNReal.mul_div_cancel
          (Nat.cast_ne_zero.mpr (NeZero.ne n)) (ENNReal.natCast_ne_top n)


/-- For any finite type `Ω` with a probability measure and any `δ > 0`,
there exist `n` and `φ : CoinTape n → Ω` such that for any set `S`,
the pushforward measure exceeds the true measure by at most `δ`. -/
theorem single_coin_approx
    {Ω : Type*} [FiniteProbabilitySpace Ω]
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (n : ℕ) (φ : CoinTape n → Ω),
      ∀ (S : Set Ω),
        (volume (φ ⁻¹' S : Set (CoinTape n))).toReal ≤
        (volume S).toReal + δ := by
  haveI : Nonempty Ω := nonempty_of_isProbabilityMeasure volume
  classical
  -- Strategy: inverse CDF construction.
  set k := Fintype.card Ω with hk_def
  have hk_pos : 0 < k := Fintype.card_pos
  -- Step 1: Choose n large enough that k / 2^n ≤ δ
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (k : ℝ) / 2 ^ n ≤ δ := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
      (div_pos hδ (Nat.cast_pos.mpr hk_pos)) (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨n, le_of_lt ?_⟩
    have hmul : (1 / 2 : ℝ) ^ n * k < δ := by
      rwa [lt_div_iff₀ (Nat.cast_pos.mpr hk_pos)] at hn
    calc (k : ℝ) / 2 ^ n = (1 / 2) ^ n * k := by
          rw [one_div, inv_pow, inv_mul_eq_div]
      _ < δ := hmul
  use n
  -- Step 2: Set up notation
  set N := Fintype.card (CoinTape n) with hN_def
  have hN_pos : 0 < N := Fintype.card_pos
  have hN_eq : N = 2 ^ n := by
    simp [N, Fintype.card_fin]
  set e := Fintype.equivFin Ω
  set eC := Fintype.equivFin (CoinTape n)
  set w : Fin k → ℕ := fun j =>
    Nat.floor ((volume ({e.symm j} : Set Ω)).toReal * N) with hw_def
  set cumW : ℕ → ℕ := fun m =>
    ∑ i ∈ Finset.range m, if h : i < k then w ⟨i, h⟩ else 0 with hcumW_def
  set binIdx : ℕ → Fin k := fun i =>
    ⟨min ((Finset.range k).filter (fun j => cumW (j + 1) ≤ i)).card (k - 1),
     by omega⟩ with hbinIdx_def
  refine ⟨fun ω => e.symm (binIdx (eC ω).val), fun S => ?_⟩
  set φ := fun ω => e.symm (binIdx (eC ω).val)
  have hw_le : ∀ j : Fin k, (w j : ℝ) ≤ (volume ({e.symm j} : Set Ω)).toReal * N := by
    intro j
    exact Nat.floor_le (by positivity)
  have hprob_sum : ∑ j : Fin k, (volume ({e.symm j} : Set Ω)).toReal = 1 := by
    have h1 : ∑ j : Fin k, volume ({e.symm j} : Set Ω) = volume (Set.univ : Set Ω) := by
      rw [← measure_biUnion_finset]
      · congr 1; ext x; simp only [Finset.mem_univ, Set.iUnion_true,
          Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_univ, iff_true]
        exact ⟨e x, (e.symm_apply_apply x).symm⟩
      · intro i _ j _ hij
        exact Set.disjoint_singleton.mpr (e.symm.injective.ne hij)
      · intro j _; exact MeasurableSet.of_discrete
    rw [← ENNReal.toReal_sum (fun j _ => (measure_lt_top _ _).ne)]
    rw [h1, measure_univ, ENNReal.toReal_one]
  have hsum_le : ∑ j : Fin k, w j ≤ N := by
    suffices h : (∑ j : Fin k, w j : ℝ) ≤ N by exact_mod_cast h
    calc (∑ j : Fin k, w j : ℝ)
        = ∑ j : Fin k, (w j : ℝ) := by rfl
      _ ≤ ∑ j : Fin k, (volume ({e.symm j} : Set Ω)).toReal * N :=
          Finset.sum_le_sum (fun j _ => hw_le j)
      _ = (∑ j : Fin k, (volume ({e.symm j} : Set Ω)).toReal) * N := by
          rw [Finset.sum_mul]
      _ = 1 * N := by rw [hprob_sum]
      _ = N := one_mul _
  have hdeficit : N - ∑ j : Fin k, w j ≤ k := by
    by_contra h; push_neg at h
    have hN_bound : N ≤ ∑ j : Fin k, w j + k := by
      suffices (N : ℝ) ≤ ∑ j : Fin k, (w j : ℝ) + k by exact_mod_cast this
      calc (N : ℝ)
          = ∑ j : Fin k, (volume ({e.symm j} : Set Ω)).toReal * N := by
            rw [← Finset.sum_mul, hprob_sum, one_mul]
        _ ≤ ∑ j : Fin k, ((w j : ℝ) + 1) := by
            apply Finset.sum_le_sum; intro j _
            linarith [Nat.lt_floor_add_one
              ((volume ({e.symm j} : Set Ω)).toReal * N)]
        _ = ∑ j : Fin k, (w j : ℝ) + ∑ j : Fin k, (1 : ℝ) := by
            rw [← Finset.sum_add_distrib]
        _ = ∑ j : Fin k, (w j : ℝ) + k := by simp
    omega
  have hcumW_mono : ∀ a b, a ≤ b → cumW a ≤ cumW b :=
    fun a b h => Finset.sum_le_sum_of_subset (Finset.range_mono h)
  have hcumW_step : ∀ j : Fin k, cumW (↑j + 1) = cumW ↑j + w j := by
    intro j; simp [cumW, Finset.sum_range_succ, j.isLt]
  have hcumW_k : cumW k = ∑ j : Fin k, w j := by
    simp only [cumW]
    rw [← Fin.sum_univ_eq_sum_range
      (fun i => if h : i < k then w ⟨i, h⟩ else 0)]
    apply Finset.sum_congr rfl
    intro ⟨i, hi⟩ _
    simp [hi]
  have hcumW_le_N : ∀ j : Fin k, cumW (↑j + 1) ≤ N :=
    fun j => le_trans (hcumW_mono _ _ (by omega)) (hcumW_k ▸ hsum_le)
  have hbinIdx_eq : ∀ (j : Fin k) (i : ℕ),
      cumW ↑j ≤ i → i < cumW (↑j + 1) → binIdx i = j := by
    intro j i hlo hhi
    ext; simp only [binIdx]
    have hfilt : (Finset.range k).filter (fun m => cumW (m + 1) ≤ i) =
        Finset.range j.val := by
      ext m; simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨_, hm⟩
        by_contra h; push_neg at h
        have : cumW (j.val + 1) ≤ cumW (m + 1) := hcumW_mono _ _ (by omega)
        omega
      · intro hm; exact ⟨by omega, le_trans (hcumW_mono _ _ (by omega)) hlo⟩
    rw [hfilt, Finset.card_range]
    omega
  have hfib_ge : ∀ j : Fin k,
      w j ≤ (Finset.univ.filter (fun ω : CoinTape n =>
        binIdx (eC ω).val = j)).card := by
    intro j
    let f : Fin (w j) → CoinTape n := fun i =>
      eC.symm ⟨cumW j.val + i.val, by
        have := hcumW_le_N j; rw [hcumW_step] at this; omega⟩
    have hf_inj : Function.Injective f := by
      intro a b hab; ext
      have := congrArg (fun ω => (eC ω).val) hab
      simp only [f, Equiv.apply_symm_apply] at this; omega
    have hf_mem : ∀ i, f i ∈ Finset.univ.filter (fun ω : CoinTape n =>
        binIdx (eC ω).val = j) := by
      intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, f]
      simp only [Equiv.apply_symm_apply]
      exact hbinIdx_eq j _ (by omega) (by rw [hcumW_step]; omega)
    calc w j = Fintype.card (Fin (w j)) := (Fintype.card_fin _).symm
      _ = (Finset.univ.image f).card :=
          (Finset.card_image_of_injective _ hf_inj).symm
      _ ≤ (Finset.univ.filter _).card :=
          Finset.card_le_card (fun ω hω => by
            obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hω; exact hf_mem i)
  have hfiber_bound : ∀ S : Set Ω,
      (Finset.univ.filter (fun ω : CoinTape n => φ ω ∈ S)).card ≤
      (Finset.univ.filter (fun j : Fin k => e.symm j ∈ S)).sum w +
      (N - ∑ j : Fin k, w j) := by
    intro S
    set filt := Finset.univ.filter (fun j : Fin k => e.symm j ∈ S)
    set filtC := Finset.univ.filter (fun j : Fin k => e.symm j ∉ S)
    have hdisj : Disjoint filt filtC :=
      Finset.disjoint_filter.mpr (fun j _ h1 h2 => h2 h1)
    have hunion : filt ∪ filtC = Finset.univ := by
      ext j; simp only [filt, filtC, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and, iff_true]; exact em _
    set g : CoinTape n → Fin k := fun ω => binIdx (eC ω).val
    have hphi_g : ∀ ω : CoinTape n,
        (φ ω ∈ S) ↔ (g ω ∈ filt) := by
      intro ω; simp only [φ, g, filt, Finset.mem_filter, Finset.mem_univ, true_and]
    have hLHS_eq : Finset.univ.filter (fun ω : CoinTape n => φ ω ∈ S) =
        Finset.univ.filter (fun ω => g ω ∈ filt) := by
      ext ω; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hphi_g ω
    rw [show (Finset.univ.filter (fun ω : CoinTape n => φ ω ∈ S)).card =
        (Finset.univ.filter (fun ω => g ω ∈ filt)).card from congrArg _ hLHS_eq]
    rw [← Finset.sum_card_fiberwise_eq_card_filter]
    have htotal : ∑ j : Fin k,
        (Finset.univ.filter (fun ω : CoinTape n => g ω = j)).card = N := by
      have h := (Finset.card_eq_sum_card_fiberwise
        (f := g) (s := Finset.univ) (t := Finset.univ)
        (fun ω _ => Finset.mem_coe.mpr (Finset.mem_univ _))).symm
      rwa [Finset.card_univ] at h
    have htotal_split :
        ∑ j ∈ filt, (Finset.univ.filter (fun ω : CoinTape n => g ω = j)).card +
        ∑ j ∈ filtC, (Finset.univ.filter (fun ω : CoinTape n => g ω = j)).card = N := by
      rw [← Finset.sum_union hdisj, hunion]; exact htotal
    have hcomp_ge : filt.sum w + filtC.sum w = ∑ j : Fin k, w j := by
      rw [← Finset.sum_union hdisj, hunion]
    have hfiltC_ge : filtC.sum w ≤
        ∑ j ∈ filtC, (Finset.univ.filter (fun ω : CoinTape n => g ω = j)).card := by
      apply Finset.sum_le_sum; intro j _; exact hfib_ge j
    omega
  have hvol_coinTape : ∀ (T : Set (CoinTape n)),
      (volume T).toReal =
      (Finset.univ.filter (fun ω : CoinTape n => ω ∈ T)).card / N := by
    intro T
    change (ProbabilityTheory.uniformOn Set.univ T).toReal = _
    rw [ProbabilityTheory.uniformOn_univ]
    rw [ENNReal.toReal_div]
    congr 1
    rw [Measure.count_apply MeasurableSet.of_discrete,
      Set.encard_eq_coe_toFinset_card T]
    simp only [ENat.toENNReal_coe, ENNReal.toReal_natCast]
    congr 1; congr 1; ext x; simp [Set.mem_toFinset]
  have hvol_sum : ∀ (S : Set Ω),
      (volume S).toReal =
      ∑ j ∈ Finset.univ.filter (fun j : Fin k => e.symm j ∈ S),
        (volume ({e.symm j} : Set Ω)).toReal := by
    intro S
    have hS_eq : S = ⋃ j ∈ Finset.univ.filter (fun j : Fin k => e.symm j ∈ S),
        ({e.symm j} : Set Ω) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_iUnion, Set.mem_singleton_iff]
      exact ⟨fun hx => ⟨e x, by rwa [e.symm_apply_apply], (e.symm_apply_apply x).symm⟩,
             fun ⟨j, hj, hjx⟩ => hjx ▸ hj⟩
    conv_lhs => rw [hS_eq]
    rw [measure_biUnion_finset
      (fun i _ j _ hij => Set.disjoint_singleton.mpr (e.symm.injective.ne hij))
      (fun j _ => MeasurableSet.of_discrete),
      ENNReal.toReal_sum (fun j _ => (measure_lt_top _ _).ne)]
  calc (volume (φ ⁻¹' S : Set (CoinTape n))).toReal
      = (Finset.univ.filter (fun ω : CoinTape n => ω ∈ φ ⁻¹' S)).card / N := by
          exact hvol_coinTape _
    _ = (Finset.univ.filter (fun ω : CoinTape n => φ ω ∈ S)).card / N := by
          simp only [Set.mem_preimage]
    _ ≤ ((Finset.univ.filter (fun j : Fin k => e.symm j ∈ S)).sum w +
         (N - ∑ j : Fin k, w j)) / N := by
          exact div_le_div_of_nonneg_right (by exact_mod_cast hfiber_bound S)
            (by positivity)
    _ ≤ ((volume S).toReal * N + k) / N := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          have h_wt : (((Finset.univ.filter
              (fun j : Fin k => e.symm j ∈ S)).sum w : ℕ) : ℝ) ≤
              (volume S).toReal * N := by
            calc (((Finset.univ.filter _).sum w : ℕ) : ℝ)
                = ∑ j ∈ Finset.univ.filter (fun j : Fin k => e.symm j ∈ S),
                    (w j : ℝ) := by norm_cast
              _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin k => e.symm j ∈ S),
                    (volume ({e.symm j} : Set Ω)).toReal * N :=
                  Finset.sum_le_sum (fun j _ => hw_le j)
              _ = (∑ j ∈ Finset.univ.filter (fun j : Fin k => e.symm j ∈ S),
                    (volume ({e.symm j} : Set Ω)).toReal) * N := by
                  rw [Finset.sum_mul]
              _ = (volume S).toReal * N := by rw [hvol_sum S]
          have hdef_real : (N : ℝ) - ∑ j : Fin k, (w j : ℝ) ≤ k := by
            rw [← Nat.cast_sum, ← Nat.cast_sub hsum_le]
            exact_mod_cast hdeficit
          have h1 : (((Finset.univ.filter (fun j : Fin k => e.symm j ∈ S)).sum w : ℕ) : ℝ) =
              ∑ x ∈ Finset.univ.filter (fun j : Fin k => e.symm j ∈ S), (w x : ℝ) := by
            push_cast; rfl
          have h2 : ((∑ j : Fin k, w j : ℕ) : ℝ) = ∑ j : Fin k, (w j : ℝ) := by
            push_cast; rfl
          linarith
    _ = (volume S).toReal + k / N := by
          field_simp
    _ ≤ (volume S).toReal + δ := by
          have : (k : ℝ) / N ≤ δ := by
            rw [hN_eq]; push_cast; exact hn
          linarith

/-- The uniform distribution on a product of finite types can be approximated
by coin flips: for any `δ > 0`, there exist `nX`, `nY` and maps
`φ_X`, `φ_Y` such that for any set `S ⊆ Ω_X × Ω_Y`, the
pushforward measure of `S` under `(φ_X, φ_Y)` exceeds the true
measure by at most `δ`. -/
private theorem product_coin_approx
    {Ω_X Ω_Y : Type*}
    [FiniteProbabilitySpace Ω_X] [FiniteProbabilitySpace Ω_Y]
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (nX nY : ℕ) (φ_X : CoinTape nX → Ω_X)
      (φ_Y : CoinTape nY → Ω_Y),
      ∀ (S : Set (Ω_X × Ω_Y)),
        (volume (Prod.map φ_X φ_Y ⁻¹' S :
          Set (CoinTape nX × CoinTape nY))).toReal ≤
        (volume S).toReal + δ := by
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  obtain ⟨nX, φ_X, hX⟩ := @single_coin_approx Ω_X _ (δ / 2) hδ2
  obtain ⟨nY, φ_Y, hY⟩ := @single_coin_approx Ω_Y _ (δ / 2) hδ2
  refine ⟨nX, nY, φ_X, φ_Y, fun S => ?_⟩
  set S_a : Ω_X → Set Ω_Y := fun a => Prod.mk a ⁻¹' S with hS_a_def
  set pX : Ω_X → ℝ := fun a =>
    (volume (φ_X ⁻¹' {a} : Set (CoinTape nX))).toReal with hpX_def
  set qX : Ω_X → ℝ := fun a =>
    (volume ({a} : Set Ω_X)).toReal with hqX_def
  set pY : Ω_Y → ℝ := fun b =>
    (volume (φ_Y ⁻¹' {b} : Set (CoinTape nY))).toReal with hpY_def
  set qY : Ω_Y → ℝ := fun b =>
    (volume ({b} : Set Ω_Y)).toReal with hqY_def
  have hpX_nn : ∀ a, 0 ≤ pX a := fun a => ENNReal.toReal_nonneg
  have hqX_nn : ∀ a, 0 ≤ qX a := fun a => ENNReal.toReal_nonneg
  have hpY_nn : ∀ b, 0 ≤ pY b := fun b => ENNReal.toReal_nonneg
  have hqY_nn : ∀ b, 0 ≤ qY b := fun b => ENNReal.toReal_nonneg
  have hunion_preimage :
      (Prod.map φ_X φ_Y ⁻¹' S : Set (CoinTape nX × CoinTape nY)) =
      ⋃ a : Ω_X, (φ_X ⁻¹' {a}) ×ˢ (φ_Y ⁻¹' S_a a) := by
    ext ⟨ωX, ωY⟩
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod_eq,
      Set.mem_singleton_iff, Prod.map, S_a]
    exact ⟨fun h => ⟨φ_X ωX, rfl, h⟩, fun ⟨a, ha, h⟩ => ha ▸ h⟩
  have hdisj_preimage : Pairwise (fun a b : Ω_X => Disjoint
      ((φ_X ⁻¹' {a} : Set (CoinTape nX)) ×ˢ (φ_Y ⁻¹' S_a a))
      ((φ_X ⁻¹' {b} : Set (CoinTape nX)) ×ˢ (φ_Y ⁻¹' S_a b))) := by
    intro a b hab
    rw [Set.disjoint_left]
    rintro ⟨ωX, ωY⟩ h1 h2
    simp only [Set.mem_prod_eq, Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
    exact hab (h1.1.symm.trans h2.1)
  have hLHS : (volume (Prod.map φ_X φ_Y ⁻¹' S :
      Set (CoinTape nX × CoinTape nY))).toReal =
      ∑ a : Ω_X, pX a *
        (volume (φ_Y ⁻¹' S_a a : Set (CoinTape nY))).toReal := by
    rw [hunion_preimage,
      measure_iUnion hdisj_preimage (fun _ => MeasurableSet.of_discrete),
      tsum_fintype,
      ENNReal.toReal_sum (fun a _ => measure_ne_top _ _)]
    congr 1; ext a
    change ((volume.prod volume) _).toReal = _
    rw [Measure.prod_prod, ENNReal.toReal_mul]
  have hRHS : (volume S).toReal =
      ∑ a : Ω_X, qX a * (volume (S_a a)).toReal := by
    have hunion_S : S = ⋃ a : Ω_X, ({a} : Set Ω_X) ×ˢ S_a a := by
      ext ⟨x, y⟩
      simp only [Set.mem_iUnion, Set.mem_prod_eq, Set.mem_singleton_iff, S_a]
      exact ⟨fun h => ⟨x, rfl, h⟩, fun ⟨a, ha, h⟩ => ha ▸ h⟩
    have hdisj_S : Pairwise (fun a b : Ω_X => Disjoint
        (({a} : Set Ω_X) ×ˢ S_a a) (({b} : Set Ω_X) ×ˢ S_a b)) := by
      intro a b hab; rw [Set.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      simp only [Set.mem_prod_eq, Set.mem_singleton_iff] at h1 h2
      exact hab (h1.1.symm.trans h2.1)
    rw [hunion_S, measure_iUnion hdisj_S (fun _ => MeasurableSet.of_discrete),
      tsum_fintype, ENNReal.toReal_sum (fun a _ => measure_ne_top _ _)]
    congr 1; ext a
    change ((volume.prod volume) _).toReal = _
    rw [Measure.prod_prod, ENNReal.toReal_mul]
  have hstep1 : ∑ a : Ω_X, pX a *
      (volume (φ_Y ⁻¹' S_a a : Set (CoinTape nY))).toReal ≤
      ∑ a : Ω_X, pX a * ((volume (S_a a)).toReal + δ / 2) := by
    apply Finset.sum_le_sum; intro a _
    exact mul_le_mul_of_nonneg_left (hY (S_a a)) (hpX_nn a)
  have hpX_sum : ∑ a : Ω_X, pX a = 1 := by
    simp only [hpX_def]
    rw [← ENNReal.toReal_sum (fun a _ => measure_ne_top _ _)]
    have hunion : ⋃ a ∈ (Finset.univ : Finset Ω_X),
        (φ_X ⁻¹' {a} : Set (CoinTape nX)) = Set.univ := by
      ext ωX; simp [Set.mem_iUnion]
    have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset Ω_X)
        (fun a => (φ_X ⁻¹' {a} : Set (CoinTape nX))) := by
      intro a _ b _ hab
      exact Disjoint.preimage _ (Set.disjoint_singleton.mpr hab)
    rw [← measure_biUnion_finset hdisj
      (fun a _ => MeasurableSet.of_discrete)]
    rw [hunion, measure_univ]; simp
  have hstep1' : ∑ a : Ω_X, pX a * ((volume (S_a a)).toReal + δ / 2) =
      (∑ a : Ω_X, pX a * (volume (S_a a)).toReal) + δ / 2 := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [hpX_sum, one_mul]
  have hpX_finset : ∀ T : Finset Ω_X,
      (volume (φ_X ⁻¹' (↑T : Set Ω_X) : Set (CoinTape nX))).toReal =
      ∑ a ∈ T, pX a := by
    intro T
    have hunion : (φ_X ⁻¹' (↑T : Set Ω_X) : Set (CoinTape nX)) =
        ⋃ a ∈ T, φ_X ⁻¹' ({a} : Set Ω_X) := by
      ext ω; simp
    have hdisj : Set.PairwiseDisjoint (↑T : Set Ω_X)
        (fun a => (φ_X ⁻¹' {a} : Set (CoinTape nX))) := by
      intro a _ b _ hab
      exact Disjoint.preimage _ (Set.disjoint_singleton.mpr hab)
    rw [hunion, measure_biUnion_finset hdisj
      (fun _ _ => MeasurableSet.of_discrete),
      ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
  have hqX_finset : ∀ T : Finset Ω_X,
      (volume (↑T : Set Ω_X)).toReal = ∑ a ∈ T, qX a := by
    intro T
    have hunion : (↑T : Set Ω_X) = ⋃ a ∈ T, ({a} : Set Ω_X) := by
      ext x; simp [Set.mem_iUnion]
    have hdisj : Set.PairwiseDisjoint (↑T : Set Ω_X)
        (fun a => ({a} : Set Ω_X)) := by
      intro a _ b _ hab; exact Set.disjoint_singleton.mpr hab
    rw [hunion, measure_biUnion_finset hdisj
      (fun _ _ => MeasurableSet.of_discrete),
      ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
  have hstep2 : ∑ a : Ω_X, pX a * (volume (S_a a)).toReal ≤
      ∑ a : Ω_X, qX a * (volume (S_a a)).toReal + δ / 2 := by
    set g : Ω_X → ℝ := fun a => (volume (S_a a)).toReal with hg_def
    have hg_nn : ∀ a, 0 ≤ g a := fun a => ENNReal.toReal_nonneg
    have hg_le1 : ∀ a, g a ≤ 1 := by
      intro a
      have h1 : volume (S_a a) ≤ volume (Set.univ : Set Ω_Y) :=
        measure_mono (Set.subset_univ _)
      rw [measure_univ] at h1
      calc g a = (volume (S_a a)).toReal := rfl
        _ ≤ (1 : ENNReal).toReal :=
            ENNReal.toReal_mono (by norm_num) h1
        _ = 1 := by norm_num
    suffices h_key : ∑ a : Ω_X, (pX a - qX a) * g a ≤ δ / 2 by
      have h_diff : ∑ a : Ω_X, pX a * g a - ∑ a : Ω_X, qX a * g a =
          ∑ a : Ω_X, (pX a - qX a) * g a := by
        rw [← Finset.sum_sub_distrib]; congr 1; ext a; ring
      linarith [h_diff]
    set Apos := Finset.univ.filter (fun a : Ω_X => qX a < pX a)
    rw [show ∑ a : Ω_X, (pX a - qX a) * g a =
        ∑ a ∈ Apos, (pX a - qX a) * g a +
        ∑ a ∈ Finset.univ.filter (fun a => ¬(qX a < pX a)),
          (pX a - qX a) * g a from
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm]
    have h_neg : ∑ a ∈ Finset.univ.filter (fun a => ¬(qX a < pX a)),
        (pX a - qX a) * g a ≤ 0 := by
      apply Finset.sum_nonpos; intro a ha
      exact mul_nonpos_of_nonpos_of_nonneg
        (by linarith [(Finset.mem_filter.mp ha).2]) (hg_nn a)
    have h_pos : ∑ a ∈ Apos, (pX a - qX a) * g a ≤
        ∑ a ∈ Apos, (pX a - qX a) := by
      apply Finset.sum_le_sum; intro a ha
      exact mul_le_of_le_one_right
        (by linarith [(Finset.mem_filter.mp ha).2]) (hg_le1 a)
    have h_hX : ∑ a ∈ Apos, (pX a - qX a) ≤ δ / 2 := by
      have hX_Apos := hX (↑Apos : Set Ω_X)
      rw [hpX_finset Apos, hqX_finset Apos] at hX_Apos
      have h_eq : ∑ a ∈ Apos, (pX a - qX a) =
          ∑ a ∈ Apos, pX a - ∑ a ∈ Apos, qX a := by
        rw [← Finset.sum_sub_distrib]
      linarith [h_eq]
    linarith
  rw [hLHS]
  calc ∑ a : Ω_X, pX a *
        (volume (φ_Y ⁻¹' S_a a : Set (CoinTape nY))).toReal
      ≤ ∑ a : Ω_X, pX a * ((volume (S_a a)).toReal + δ / 2) := hstep1
    _ = (∑ a : Ω_X, pX a * (volume (S_a a)).toReal) + δ / 2 := hstep1'
    _ ≤ (∑ a : Ω_X, qX a * (volume (S_a a)).toReal) + δ / 2 + δ / 2 := by
        linarith [hstep2]
    _ = (∑ a : Ω_X, qX a * (volume (S_a a)).toReal) + δ := by ring
    _ = (volume S).toReal + δ := by linarith [hRHS]

end Internal

namespace PrivateCoin

/-- Approximate a finite-message protocol over arbitrary finite
probability spaces by one over CoinTape. Given `δ > 0`, produces
`nX`, `nY`, and a CoinTape-based protocol with the same complexity
whose run approximates the original (via inverse CDF construction).
This does not depend on any predicate Q. -/
noncomputable def FiniteMessage.Protocol.toCoinTape
    {Ω_X Ω_Y : Type*}
    [FiniteProbabilitySpace Ω_X] [FiniteProbabilitySpace Ω_Y]
    {X Y α : Type*}
    (p : FiniteMessage.Protocol Ω_X Ω_Y X Y α)
    (δ : ℝ) (hδ : 0 < δ) :
    Σ (nX : ℕ) (nY : ℕ),
      FiniteMessage.Protocol (CoinTape nX) (CoinTape nY) X Y α :=
  let data := Internal.product_coin_approx (Ω_X := Ω_X) (Ω_Y := Ω_Y) δ hδ
  let nX := data.choose
  let nY := data.choose_spec.choose
  let φ_X := data.choose_spec.choose_spec.choose
  let φ_Y := data.choose_spec.choose_spec.choose_spec.choose
  ⟨nX, nY, p.comap (Prod.map φ_X id) (Prod.map φ_Y id)⟩

@[simp]
theorem FiniteMessage.Protocol.toCoinTape_complexity
    {Ω_X Ω_Y : Type*}
    [FiniteProbabilitySpace Ω_X] [FiniteProbabilitySpace Ω_Y]
    {X Y α : Type*}
    (p : FiniteMessage.Protocol Ω_X Ω_Y X Y α)
    (δ : ℝ) (hδ : 0 < δ) :
    (p.toCoinTape δ hδ).2.2.complexity = p.complexity := by
  simp [FiniteMessage.Protocol.toCoinTape]

/-- The CoinTape approximation of a protocol preserves ApproxSatisfies
up to the given slack δ. -/
theorem FiniteMessage.Protocol.toCoinTape_approxSatisfies
    {Ω_X Ω_Y : Type*}
    [FiniteProbabilitySpace Ω_X] [FiniteProbabilitySpace Ω_Y]
    {X Y α : Type*}
    (p : FiniteMessage.Protocol Ω_X Ω_Y X Y α)
    (Q : X → Y → α → Prop)
    (ε δ : ℝ) (hδ : 0 < δ)
    (hp : p.ApproxSatisfies Q ε) :
    (p.toCoinTape δ hδ).2.2.ApproxSatisfies Q (ε + δ) := by
  intro x y
  simp only [FiniteMessage.Protocol.toCoinTape]
  -- Extract the approximation data
  set data := Internal.product_coin_approx (Ω_X := Ω_X) (Ω_Y := Ω_Y) δ hδ
  set φ_X := data.choose_spec.choose_spec.choose
  set φ_Y := data.choose_spec.choose_spec.choose_spec.choose
  have happrox := data.choose_spec.choose_spec.choose_spec.choose_spec
  -- The error set under the new protocol is the preimage under (φ_X, φ_Y)
  let S := {ω : Ω_X × Ω_Y | ¬Q x y (p.rrun x y ω.1 ω.2)}
  have hset : {ω : CoinTape data.choose × CoinTape data.choose_spec.choose |
      ¬Q x y (FiniteMessage.Protocol.rrun
        (p.comap (Prod.map φ_X id) (Prod.map φ_Y id)) x y ω.1 ω.2)} =
      Prod.map φ_X φ_Y ⁻¹' S := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage, Prod.map, S,
      FiniteMessage.Protocol.rrun,
      Deterministic.FiniteMessage.Protocol.comap_run, Function.id_def]
  rw [hset]
  calc (volume (Prod.map φ_X φ_Y ⁻¹' S :
          Set (CoinTape data.choose × CoinTape data.choose_spec.choose))).toReal
      ≤ (volume S).toReal + δ := happrox S
    _ ≤ ε + δ := by linarith [hp x y]

end PrivateCoin

end CommunicationComplexity
