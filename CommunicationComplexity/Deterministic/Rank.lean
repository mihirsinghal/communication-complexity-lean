import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Real.Basic
import CommunicationComplexity.Basic
import CommunicationComplexity.Deterministic.Rectangle
import CommunicationComplexity.Helper

namespace CommunicationComplexity

namespace Deterministic.Rank

open Classical in
/-- The real-valued matrix of a Boolean function `f : X → Y → Bool`,
where the `(x, y)` entry is `1` if `f x y = true` and `0` otherwise. -/
noncomputable def boolFunctionMatrix {X Y : Type*}
    (f : X → Y → Bool) : Matrix X Y ℝ :=
  Matrix.of fun x y => if f x y then 1 else 0

/-- The rank of a Boolean function `f`, defined as the rank of its
real-valued matrix over `ℝ`. -/
noncomputable def boolFunctionRank {X Y : Type*} [Fintype Y]
    (f : X → Y → Bool) : ℕ :=
  (boolFunctionMatrix f).rank

/-- The sign matrix of a Boolean function `f : X → Y → Bool`,
with entries in `{±1}` via `boolSign`. -/
noncomputable def signFunctionMatrix {X Y : Type*}
    (f : X → Y → Bool) : Matrix X Y ℝ :=
  Matrix.of fun x y => boolSign (f x y)

/-- The sign-rank of a Boolean function `f`, defined over `ℝ`. -/
noncomputable def signFunctionRank {X Y : Type*} [Fintype Y]
    (f : X → Y → Bool) : ℕ :=
  (signFunctionMatrix f).rank

open Classical in
/-- The {0,1}-matrix of a subset `R ⊆ X × Y`. -/
noncomputable def rectMatrix {X Y : Type*}
    (R : Set (X × Y)) : Matrix X Y ℝ :=
  Matrix.of fun x y => if (x, y) ∈ R then 1 else 0

/-- For a rectangle `R = A ×ˢ B`, `rectMatrix R` is an outer product,
hence has rank ≤ 1. -/
theorem rank_rectMatrix_le_one {X Y : Type*} [Fintype Y]
    (R : Set (X × Y)) (hR : Rectangle.IsRectangle R) :
    (rectMatrix R).rank ≤ 1 := by
  classical
  obtain ⟨A, B, rfl⟩ := hR
  suffices rectMatrix (A ×ˢ B) =
      Matrix.vecMulVec (fun x => if x ∈ A then (1 : ℝ) else 0)
        (fun y => if y ∈ B then (1 : ℝ) else 0) by
    rw [this]; exact Matrix.rank_vecMulVec_le _ _
  ext x y; simp only [rectMatrix, Matrix.of_apply, Matrix.vecMulVec, Set.mem_prod_eq]
  cases Classical.em (x ∈ A) <;> cases Classical.em (y ∈ B) <;> simp_all

end Deterministic.Rank

end CommunicationComplexity

/-- Matrix rank is subadditive: `rank (A + B) ≤ rank A + rank B`. -/
theorem Matrix.rank_add_le {X Y : Type*} [Fintype Y]
    (A B : Matrix X Y ℝ) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank; rw [Matrix.mulVecLin_add]
  refine (Submodule.finrank_mono ?_).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)
  exact LinearMap.range_add_le _ _

/-- Matrix rank is subadditive over finite sums. -/
theorem Matrix.rank_sum_le {X Y : Type*} [Fintype Y]
    {ι : Type*} (s : Finset ι) (A : ι → Matrix X Y ℝ) :
    (∑ i ∈ s, A i).rank ≤ ∑ i ∈ s, (A i).rank := by
  classical
  induction s using Finset.induction with
  | empty => simp [Matrix.rank_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (Matrix.rank_add_le _ _).trans (Nat.add_le_add_left ih _)

namespace CommunicationComplexity

namespace Deterministic.Rank

open Rectangle in
/-- The rank of a Boolean function is at most the number of
rectangles in any monochromatic rectangle partition.
Each true-mono rectangle contributes a rank-1 matrix,
M_f is their sum, and rank is subadditive. -/
theorem boolFunctionRank_le_ncard
    {X Y : Type*} [Finite X] [Fintype Y]
    (f : X → Y → Bool)
    (Part : Set (Set (X × Y)))
    (hPart : Rectangle.IsMonoPartition Part f) :
    boolFunctionRank f ≤ Set.ncard Part := by
  classical
  let PF := (Set.toFinite Part).toFinset
  let trueRects := PF.filter (fun R => ∃ p ∈ R, f p.1 p.2 = true)
  -- M_f = ∑ over true-mono rectangles of rectMatrix R
  have hsum : boolFunctionMatrix f = ∑ R ∈ trueRects, rectMatrix R := by
    ext x y
    simp only [boolFunctionMatrix, rectMatrix, Matrix.of_apply, Matrix.sum_apply]
    obtain ⟨R₀, hR₀_mem, hR₀_in⟩ := monoPartition_point_mem hPart (x, y)
    have hother : ∀ R ∈ PF, R ≠ R₀ → (x, y) ∉ R := fun R hR hne hmem =>
      hne (monoPartition_part_unique hPart
        ((Set.toFinite Part).mem_toFinset.mp hR) hR₀_mem hmem hR₀_in)
    cases hf : f x y <;> simp only [Bool.false_eq_true, ite_true, ite_false]
    · -- f x y = false: every term is 0
      symm; apply Finset.sum_eq_zero; intro R hR
      by_cases hne : R = R₀
      · subst hne; obtain ⟨⟨x', y'⟩, hpin, hftrue⟩ := (Finset.mem_filter.mp hR).2
        have hmono := monoPartition_values_eq hPart hR₀_mem hR₀_in hpin
        rw [hf] at hmono; simp [← hmono] at hftrue
      · simp [hother R (Finset.mem_filter.mp hR).1 hne]
    · -- f x y = true: only R₀ contributes 1
      symm; rw [Finset.sum_eq_single R₀
        (fun R hR hne => by simp [hother R (Finset.mem_filter.mp hR).1 hne])
        (fun h => absurd (Finset.mem_filter.mpr
          ⟨(Set.toFinite Part).mem_toFinset.mpr hR₀_mem, ⟨x, y⟩, hR₀_in, hf⟩) h)]
      simp [hR₀_in]
  -- rank(M_f) ≤ ∑ rank(rectMatrix R) ≤ ∑ 1 = |trueRects| ≤ |Part|
  calc boolFunctionRank f
      = (∑ R ∈ trueRects, rectMatrix R).rank := by unfold boolFunctionRank; rw [← hsum]
    _ ≤ ∑ R ∈ trueRects, (rectMatrix R).rank := Matrix.rank_sum_le _ _
    _ ≤ ∑ _R ∈ trueRects, 1 := Finset.sum_le_sum fun R hR =>
        rank_rectMatrix_le_one R (hPart.1 R ((Set.toFinite Part).mem_toFinset.mp
          (Finset.mem_filter.mp hR).1))
    _ = trueRects.card := by simp
    _ ≤ PF.card := Finset.card_filter_le _ _
    _ = Set.ncard Part := (Set.ncard_eq_toFinset_card Part (Set.toFinite Part)).symm

open Rectangle in
/-- The sign-rank of a Boolean function is at most the number of
rectangles in any monochromatic rectangle partition. -/
theorem signFunctionRank_le_ncard
    {X Y : Type*} [Finite X] [Fintype Y]
    (f : X → Y → Bool)
    (Part : Set (Set (X × Y)))
    (hPart : Rectangle.IsMonoPartition Part f) :
    signFunctionRank f ≤ Set.ncard Part := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  haveI : DecidableEq X := Classical.decEq X
  let PF := (Set.toFinite Part).toFinset
  let coeff : Set (X × Y) → ℝ := fun R =>
    if ∃ p ∈ R, f p.1 p.2 = true then (-1 : ℝ) else 1
  have hsum :
      signFunctionMatrix f = ∑ R ∈ PF, (coeff R) • rectMatrix R := by
    ext x y
    simp only [signFunctionMatrix, rectMatrix, Matrix.of_apply, Matrix.sum_apply]
    obtain ⟨R₀, hR₀_mem, hR₀_in⟩ := monoPartition_point_mem hPart (x, y)
    have hother : ∀ R ∈ PF, R ≠ R₀ → (x, y) ∉ R := fun R hR hne hmem =>
      hne (monoPartition_part_unique hPart
        ((Set.toFinite Part).mem_toFinset.mp hR) hR₀_mem hmem hR₀_in)
    rw [Finset.sum_eq_single R₀
      (fun R hR hne => by simp [hother R hR hne])
      (fun h => absurd ((Set.toFinite Part).mem_toFinset.mpr hR₀_mem) h)]
    have hmono_at (p : X × Y) (hp : p ∈ R₀) : f p.1 p.2 = f x y := by
      exact monoPartition_values_eq hPart hR₀_mem hp hR₀_in
    cases hxy : f x y
    · have hcoeff : coeff R₀ = 1 := by
        unfold coeff
        refine if_neg ?_
        intro hExists
        rcases hExists with ⟨p, hpR, hptrue⟩
        have : f p.1 p.2 = f x y := hmono_at p hpR
        rw [hptrue, hxy] at this
        cases this
      simp [hR₀_in, hcoeff, boolSign]
    · have hcoeff : coeff R₀ = -1 := by
        unfold coeff
        refine if_pos ?_
        exact ⟨(x, y), hR₀_in, hxy⟩
      simp [hR₀_in, hcoeff, boolSign]
  calc signFunctionRank f
      = (∑ R ∈ PF, (coeff R) • rectMatrix R).rank := by
          unfold signFunctionRank
          rw [← hsum]
    _ ≤ ∑ R ∈ PF, ((coeff R) • rectMatrix R).rank := Matrix.rank_sum_le _ _
    _ ≤ ∑ R ∈ PF, 1 := by
          refine Finset.sum_le_sum ?_
          intro R hR
          by_cases hexists : ∃ p ∈ R, f p.1 p.2 = true
          · have hcoeff : coeff R = -1 := by
              unfold coeff
              exact if_pos hexists
            have hsmul_le :
                ((-1 : ℝ) • rectMatrix R).rank ≤ (rectMatrix R).rank := by
              calc
                ((-1 : ℝ) • rectMatrix R).rank
                    = (((-1 : ℝ) • (1 : Matrix X X ℝ)) * rectMatrix R).rank := by simp
                _ ≤ (rectMatrix R).rank := Matrix.rank_mul_le_right _ _
            have hrect : (rectMatrix R).rank ≤ 1 :=
              rank_rectMatrix_le_one R (hPart.1 R ((Set.toFinite Part).mem_toFinset.mp hR))
            have : (-rectMatrix R).rank ≤ 1 := by
              simpa using hsmul_le.trans hrect
            simpa [hcoeff] using this
          · have hcoeff : coeff R = 1 := by
              unfold coeff
              exact if_neg hexists
            simpa [hcoeff] using
              rank_rectMatrix_le_one R (hPart.1 R ((Set.toFinite Part).mem_toFinset.mp hR))
    _ = PF.card := by simp
    _ = Set.ncard Part := (Set.ncard_eq_toFinset_card Part (Set.toFinite Part)).symm

open Rectangle in
/-- If the deterministic CC of `f` is at most `n`, then the rank
of `f` is at most `2^n`. -/
theorem boolFunctionRank_le_pow_of_communicationComplexity_le
    {X Y : Type*} [Finite X] [Fintype Y]
    (f : X → Y → Bool) (n : ℕ)
    (h : Deterministic.communicationComplexity f ≤ n) :
    boolFunctionRank f ≤ 2 ^ n := by
  obtain ⟨Part, hPart, hCard⟩ := Deterministic.mono_partition_of_communicationComplexity_le f n h
  exact (boolFunctionRank_le_ncard f Part hPart).trans hCard

open Rectangle in
/-- If the deterministic CC of `f` is at most `n`, then the sign-rank
of `f` is at most `2^n`. -/
theorem signFunctionRank_le_pow_of_communicationComplexity_le
    {X Y : Type*} [Finite X] [Fintype Y]
    (f : X → Y → Bool) (n : ℕ)
    (h : Deterministic.communicationComplexity f ≤ n) :
    signFunctionRank f ≤ 2 ^ n := by
  obtain ⟨Part, hPart, hCard⟩ := Deterministic.mono_partition_of_communicationComplexity_le f n h
  exact (signFunctionRank_le_ncard f Part hPart).trans hCard

/-- Log-rank lower bound: the deterministic communication
complexity of a Boolean function `f` is at least `⌈log₂(rank f)⌉`. -/
theorem log_rank_lower_bound
    {X Y : Type*} [Finite X] [Fintype Y]
    (f : X → Y → Bool) :
    (Nat.clog 2 (boolFunctionRank f) : ENat) ≤
      Deterministic.communicationComplexity f := by
  match h : Deterministic.communicationComplexity f with
  | ⊤ => exact le_top
  | (n : ℕ) =>
    exact_mod_cast Nat.clog_le_of_le_pow
      (boolFunctionRank_le_pow_of_communicationComplexity_le f n (le_of_eq h))

/-- Log-sign-rank lower bound: deterministic communication complexity is at least
`⌈log₂(sign-rank f)⌉`. -/
theorem log_sign_rank_lower_bound
    {X Y : Type*} [Finite X] [Fintype Y]
    (f : X → Y → Bool) :
    (Nat.clog 2 (signFunctionRank f) : ENat) ≤
      Deterministic.communicationComplexity f := by
  match h : Deterministic.communicationComplexity f with
  | ⊤ => exact le_top
  | (n : ℕ) =>
    exact_mod_cast Nat.clog_le_of_le_pow
      (signFunctionRank_le_pow_of_communicationComplexity_le f n (le_of_eq h))

end Deterministic.Rank

end CommunicationComplexity
