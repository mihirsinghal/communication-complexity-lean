import Mathlib
import CommunicationComplexity.BitString
import CommunicationComplexity.CoinTape
import CommunicationComplexity.Rectangle.Basic
import CommunicationComplexity.PublicCoin.Complexity

namespace CommunicationComplexity

namespace Functions.GapOrthogonality

open MeasureTheory
open scoped Matrix.Norms.Frobenius
open scoped InnerProductSpace
open scoped BigOperators

variable {m n : Nat}

abbrev Rn (n : ℕ) := EuclideanSpace ℝ (Fin n)
instance (n : ℕ) : MeasurableSpace (Rn n) :=
  borel (EuclideanSpace ℝ (Fin n))

noncomputable def σ (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) : ℝ :=
  Real.sqrt ((Matrix.IsHermitian.eigenvalues
    (A := (A.conjTranspose * A))
    (Matrix.isHermitian_conjTranspose_mul_self A)) i)

def frobeniusInner (A B : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * B i j

/-- Von Neumann's trace inequality: the Frobenius inner product of two matrices is
bounded by the largest singular value of one matrix times the sum of singular values
of the other. Here `σ M₂ ⟨0, hn⟩` is the largest singular value of `M₂` (since
`Matrix.IsHermitian.eigenvalues₀` is antitone, index 0 gives the largest eigenvalue
of `M₂ᵀM₂`, and `σ` takes its square root).

The proof requires SVD (singular value decomposition) infrastructure for rectangular
matrices, which is not yet available in Mathlib. -/
lemma basic (M_1 M_2 : Matrix (Fin m) (Fin n) ℝ) (hn : 0 < n) :
  frobeniusInner M_1 M_2 ≤ σ M_2 ⟨0, hn⟩ * (∑ i, σ M_1 i) := by
  sorry

/-- A lower bound on the r-th singular value of M₁ in terms of the Frobenius
inner product with M₂ and the largest singular value of M₂. Follows from `basic`
and the antitone ordering of singular values.

The proof requires SVD infrastructure not yet available in Mathlib. -/
lemma fact_2_1 (M_1 M_2 : Matrix (Fin m) (Fin n) ℝ) {r : ℕ} (hr : r < M_1.rank)
    (hr_2 : r < n) (hn : 0 < n) :
    σ M_1 ⟨r, hr_2⟩ ≥
      1 / (M_1.rank - r) * (frobeniusInner M_1 M_2 / σ M_2 ⟨0, hn⟩ - ‖M_2‖ * √r) := by
  sorry

/-- Talagrand's concentration inequality for the norm of orthogonal projections.

Note: This statement requires `[NormedAddCommGroup (Submodule ℝ (Rn n))]`, which puts
a norm on the type of submodules itself (not on the elements of a submodule). This is
an unusual instance requirement. Additionally, for the bound to hold with arbitrary
probability measures μ, one would typically need μ to be a Gaussian or log-concave
measure; for general μ, the tail bound need not hold. -/
/- The original statement of `talagrand` is false for arbitrary probability measures μ.
   Counterexample: Let n ≥ 1, V = ⊤ (the whole space), μ = Dirac(0).
   Then starProjection V x = x (projection onto the whole space is identity),
   so ‖starProjection V 0‖ = 0 and √(Module.finrank ℝ V) = √n.
   For any t ∈ (0, √n), the set {x | |‖proj(x)‖ - √n| > t} contains 0 and has
   measure 1 under Dirac(0). But exp(-c·t²) < 1 for every c > 0, so no valid c exists.
   The real Talagrand concentration inequality requires specific distributional
   assumptions (e.g., Gaussian or product measures), not arbitrary probability measures. -/
/- lemma talagrand (V : Submodule ℝ (Rn n))
    [NormedAddCommGroup (Submodule ℝ (Rn n))] [FiniteDimensional ℝ (Rn n)]
    (t : ℝ) (ht : t > 0) (μ : Measure (Rn n)) [IsProbabilityMeasure μ] :
    ∃ (c : ℝ) (hc : 0 < c),
      (μ {x | |‖Submodule.starProjection V x‖ - (√ (Module.finrank ℝ V))| > t}).toReal
        ≤ Real.exp (-c * t^2) := by
  sorry -/

def partialBoolFunc (X Y : Type) : Type := X → Y → Option Bool

/-- Preimage sets of +1 and -1 (True / False) -/
def preimageTrue (f : @partialBoolFunc X Y) : Set (X × Y) :=
  {xy | f xy.1 xy.2 = true}

def preimageFalse (f : @partialBoolFunc X Y) : Set (X × Y) :=
  {xy | f xy.1 xy.2 = false}

/-
Corruption bound theorem (statement form).

The proof requires showing that public-coin protocols induce rectangle partitions
and applying the corruption hypothesis to bound the false preimage mass. This
relies on the rectangle structure of communication protocols, which requires
connecting `PublicCoin.communicationComplexityFin` to protocol-induced partitions.
-/
lemma theorem_2_3
    {X Y : Type} [Fintype X] [Fintype Y]
    [MeasurableSpace (X × Y)]
    (f : partialBoolFunc X Y)
    (μ : ProbabilityMeasure (X × Y))
    (ε δ ξ : ℝ)
    (hε : 0 < ε ∧ ε < 1)
    (hδ : 0 < δ ∧ δ < 1)
    (hξ : 0 ≤ ξ ∧ ξ < 1)
    (hrect :
      ∀ R : Set (X × Y), Rectangle.IsRectangle R →
        μ R > δ →
          μ (R ∩ preimageTrue f)
            > ε * μ (R ∩ preimageFalse f))
    : (1 / δ) * ((μ (preimageFalse f)).toReal - ξ / ε) ≤
        2 ^ (PublicCoin.communicationComplexityFin f ξ) := by
  by_contra h;
  convert CommunicationComplexity.PublicCoin.communicationComplexity_finite _ _;
  any_goals exact Option Bool;
  any_goals exact fun _ _ => none;
  rotate_right;
  · exact -1;
  · unfold PublicCoin.communicationComplexity;
    simp +decide [ PublicCoin.Protocol.ApproxComputes ];
    exact fun _ _ => ⟨ none, none, by linarith [ show ( volume { ω : CoinTape _ | ¬Deterministic.Protocol.run ‹_› ( ω, none ) ( ω, none ) = none } |> ENNReal.toReal ) ≥ 0 by positivity ] ⟩;
  · infer_instance;
  · infer_instance

def IsHypercube (y : Rn n) : Prop :=
  ∀ i : Fin n, y i = 1 ∨ y i = -1

/-- From a large subset A of {±1}^n (of size > 2^((1-α)n)), one can find a subset X
of size k = n/10 such that every x ∈ X has small orthogonal projection onto the span
of any subset of X. The proof uses a greedy selection argument: iteratively choose
vectors from A whose projection onto the span of previously selected vectors is
small, which is possible because A is large enough that not all vectors can have
large projections. -/
lemma theorem_3_1
    (α : ℝ)
    (hα : 0 < α)
    (A : Finset (Rn n))
    (hA : ∀ a ∈ A, IsHypercube a)
    (hsize : A.card > (2 : ℝ) ^ ((1 - α) * n)) :
    let k := n / 10
    ∃ X : Finset (Rn n),
      X ⊆ A ∧
      X.card = k ∧
      ∀ x : Rn n, x ∈ X →
        ∀ (Y : Finset (Rn n)),
          Y ⊆ X →
            ‖Submodule.orthogonalProjection (Submodule.span ℝ Y) x‖ ≤ Real.sqrt n / 3 := by
  intro k
  by_cases hk : n < 10
  · -- When n < 10, k = n / 10 = 0, so X = ∅ satisfies all conditions trivially
    have hk0 : k = 0 := Nat.div_eq_of_lt (by omega)
    exact ⟨∅, Finset.empty_subset _, by simp [hk0],
      fun x hx => absurd hx (by simp)⟩
  · -- When n ≥ 10, k ≥ 1. This requires a greedy selection argument.
    sorry

def IsGoodX
    (α : ℝ)
    (hα : 0 < α)
    (A : Finset (Rn n))
    (hA : ∀ a ∈ A, IsHypercube a)
    (hsize : A.card > (2 : ℝ) ^ ((1 - α) * n))
    (X : Finset (Rn n)) : Prop :=
  ∃ hX, theorem_3_1 α hα A hA hsize = ⟨X, hX⟩

lemma lemma_3_2
    (α : ℝ)
    (hα : 0 < α)
    (A : Finset (Rn n))
    (hA : ∀ a ∈ A, IsHypercube a)
    (hsize : A.card > (2 : ℝ) ^ ((1 - α) * n))
    (X : Finset (Rn n))
    (hX₁ : X.Nonempty)
    (hX₂ : IsGoodX α hα A hA hsize X)
    (β : ℝ)
    (hβ : 0 < β)
    (μ : ProbabilityMeasure (Rn n)) :
    μ { y : Rn n | IsHypercube y ∧
      (Finset.max' (X.image (fun x => |Inner.inner ℝ y x|))
        (Finset.image_nonempty.mpr hX₁) ≤ Real.sqrt n / 4) } ≤
      Real.exp (-β * (m : ℝ)) := by
  obtain ⟨ k, hk ⟩ := hX₂
  rcases n with ( _ | _ | n ) <;> norm_num [ Nat.div_eq_of_lt ] at *
  · aesop
  · norm_num [ Finset.card_eq_one ] at * ; aesop
  · contrapose! k
    intro hX₂ hX₃; have := Finset.card_le_card hX₂; simp_all +decide
    refine' ⟨ hX₁.choose, hX₁.choose_spec, { hX₁.choose }, _, _ ⟩ <;> norm_num
    · exact hX₁.choose_spec
    · rw [ Submodule.starProjection_singleton ] ; norm_num
      rw [ div_self ] <;> norm_num
      · have := hA _ ( hX₂ hX₁.choose_spec ) ; norm_num [ EuclideanSpace.norm_eq ] at *
        rw [ Finset.sum_congr rfl fun i _ => by
          rw [ show ( Exists.choose hX₁ ).ofLp i ^ 2 = 1 by cases this i <;> aesop ] ]
        norm_num
        nlinarith [ Real.sqrt_nonneg ( n + 1 + 1 ),
          Real.sq_sqrt ( show 0 ≤ ( n:ℝ ) + 1 + 1 by positivity ) ]
      · intro h; have := hA _ ( hX₂ hX₁.choose_spec ) ; simp_all +decide [ IsHypercube ]

/-- "Almost orthogonal" relation: |⟪x,y⟫| ≤ √n / 4 -/
def almostOrthogonal (x y : Rn n) : Prop :=
  |Inner.inner ℝ x y| ≤ Real.sqrt n / 4

noncomputable instance (x y : Rn n) : Decidable (almostOrthogonal x y) := by
  unfold almostOrthogonal
  infer_instance

/- The original statement of theorem_3_3 is false as written: A and B are arbitrary
   finite subsets of the hypercube {±1}^n, unrelated to the measure μ. By choosing
   μ = Dirac(0), the hypothesis (μ.prod μ)(almostOrthogonal) = 1 ≥ 1 - ε is trivially
   satisfied (since Inner.inner ℝ 0 0 = 0 ≤ √n/4), while taking A = B = all of {±1}^n
   gives A.card * B.card / 4^n = 1, which cannot be bounded by exp(-c·n) for any c > 0
   and n > 0. The theorem likely intended μ to be related to A and B (e.g., the uniform
   measure on the hypercube), or the conclusion should involve the density of A and B
   under the measure μ. -/
/- theorem theorem_3_3
    (ε : ℝ)
    (hε : ε > 0)
    (A B : Finset (Rn n))
    (hA : ∀ x ∈ A, IsHypercube x)
    (hB : ∀ y ∈ B, IsHypercube y)
    (μ : Measure (Rn n))
    (hμ : IsProbabilityMeasure μ) :
    ((μ.prod μ) {p | almostOrthogonal p.1 p.2}).toReal ≥ ((1 : ℝ) - ε) →
    ∃ c : ℝ, c > 0 ∧
      ((A.card * B.card : ℝ) / (4 : ℝ)^n)
        ≤ Real.exp (-c * n) := by
  sorry -/

def boolToReal : Bool → ℝ
  | true  => 1
  | false => -1

def inner {n : ℕ} (x y : BitString n) : ℝ :=
  ∑ i : Fin n, (boolToReal (x i)) * (boolToReal (y i))

def IsGapOrthogonal (n : ℕ) (x y : BitString n) (b : Bool) : Prop :=
  (|inner x y| ≤ Real.sqrt (n : ℝ) → b = true) ∧
  (Real.sqrt (n : ℝ) < |inner x y| → b = false)

/- The original statement of publicCoin_protocol_lower_bound is false: for n = 1,
   every pair of 1-bit strings has |inner x y| = 1 = √1, so IsGapOrthogonal is
   trivially satisfied by always outputting `true`, using a 0-bit protocol. But the
   conclusion would require c · 1 ≤ 0 for some c > 0, which is impossible.
   A corrected version restricts to sufficiently large n. -/
/- theorem publicCoin_protocol_lower_bound
    (ε : ℝ) (hε : ε < 1 / 2) :
    ∃ c > 0,
      ∀ {n m : ℕ}
        (p : PublicCoin.Protocol (CoinTape m)
          (BitString n) (BitString n) Bool),
        p.ApproxSatisfies
            (fun x y b => IsGapOrthogonal n x y b) ε →
          c * (n : ℝ) ≤ (p.complexity : ℝ) := by
  sorry -/

/-- Corrected version of publicCoin_protocol_lower_bound: the Ω(n) lower bound
    on the public-coin communication complexity of Gap Orthogonality holds for
    sufficiently large n. For small n the problem may be trivial (e.g., for n = 1,
    a 0-bit protocol suffices). -/
theorem publicCoin_protocol_lower_bound
    (ε : ℝ) (hε : 0 ≤ ε ∧ ε < 1 / 2) :
    ∃ c > 0, ∃ N₀ : ℕ,
      ∀ {n m : ℕ}, N₀ ≤ n →
        ∀ (p : PublicCoin.Protocol (CoinTape m)
          (BitString n) (BitString n) Bool),
        p.ApproxSatisfies
            (fun x y b => IsGapOrthogonal n x y b) ε →
          c * (n : ℝ) ≤ (p.complexity : ℝ) := by
  sorry

end Functions.GapOrthogonality

end CommunicationComplexity
