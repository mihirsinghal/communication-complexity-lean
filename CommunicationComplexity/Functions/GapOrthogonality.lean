import Mathlib.Analysis.Matrix.Normed
import CommunicationComplexity.BitString
import CommunicationComplexity.CoinTape
import Mathlib.Analysis.Matrix.Spectrum
import CommunicationComplexity.Rectangle.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import CommunicationComplexity.PublicCoin.Complexity

import Mathlib.Analysis.InnerProductSpace.Basic


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
-- noncomputable instance : InnerProductSpace ℝ (Rn n) :=
--   inferInstance

noncomputable def σ (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin n) : ℝ :=
  Real.sqrt ((Matrix.IsHermitian.eigenvalues
    (A := (A.conjTranspose * A))
    (Matrix.isHermitian_conjTranspose_mul_self A)) i)

def frobeniusInner (A B : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * B i j

lemma basic (M_1 M_2 : Matrix (Fin m) (Fin n) ℝ) (hn : 0 < n) :
  frobeniusInner M_1 M_2 ≤ σ M_2 ⟨0, hn⟩ * (∑ i, σ M_1 i) :=
  by sorry

lemma fact_2_1 (M_1 M_2 : Matrix (Fin m) (Fin n) ℝ) {r : ℕ} (hr : r < M_1.rank) (hr_2 : r < n) (hn : 0 < n) : σ M_1 ⟨r, hr_2⟩ ≥ 1 / (M_1.rank - r) * (frobeniusInner M_1 M_2 / σ M_2 ⟨0, hn⟩ - ‖M_2‖ * √r) :=
  sorry


lemma talagrand (V : Submodule ℝ (Rn n)) [NormedAddCommGroup (Submodule ℝ (Rn n))] [FiniteDimensional ℝ (Rn n)] (t : ℝ) (ht : t > 0) (μ : Measure (Rn n))
  [IsProbabilityMeasure μ] :
  ∃ (c : ℝ) (hc : 0 < c),
  (μ {x | |‖Submodule.starProjection V x‖ - (√ (Module.finrank ℝ V))| > t}).toReal
    ≤ Real.exp (-C * t^2) := by sorry

def partialBoolFunc (X Y : Type) : Type := X → Y → Option Bool

/-- Preimage sets of +1 and -1 (True / False) -/
def preimageTrue (f : @partialBoolFunc X Y) : Set (X × Y) :=
  {xy | f xy.1 xy.2 = true}

def preimageFalse (f : @partialBoolFunc X Y) : Set (X × Y) :=
  {xy | f xy.1 xy.2 = false}

/-- Corruption bound theorem (statement form) -/
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
  : (1 / δ) * ((μ (preimageFalse f)).toReal - ξ / ε) ≤ 2 ^ (PublicCoin.communicationComplexityFin f ξ) :=
by
  sorry

def IsHypercube (y : Rn n) : Prop :=
  ∀ i : Fin n, y i = 1 ∨ y i = -1

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
        Y ⊆ X → ‖ Submodule.orthogonalProjection (Submodule.span ℝ Y) x‖ ≤ Real.sqrt n / 3 :=
by
  admit

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
      (Finset.max' (X.image (fun x => |Inner.inner ℝ y x|)) (Finset.image_nonempty.mpr hX₁) ≤ Real.sqrt n / 4) } ≤
    Real.exp (-β * (m : ℝ)) :=
by
  sorry

/-- “Almost orthogonal” relation: |⟪x,y⟫| ≤ √n / 4 -/
def almostOrthogonal (x y : Rn n) : Prop :=
  |Inner.inner ℝ x y| ≤ Real.sqrt n / 4

noncomputable instance (x y : Rn n) : Decidable (almostOrthogonal x y) :=
by
  unfold almostOrthogonal
  infer_instance
/-- Theorem 3.3 (formal statement) -/
theorem theorem_3_3
  (ε : ℝ)
  (hε : ε > 0)
  (A B : Finset (Rn n))
  (hA : ∀ x ∈ A, IsHypercube x)
  (hB : ∀ y ∈ B, IsHypercube y)
  (μ : Measure (Rn n))
  (hμ : IsProbabilityMeasure μ):
  ((μ.prod μ) {p | almostOrthogonal p.1 p.2}).toReal ≥ ((1 : ℝ) - ε) →
  ∃ c : ℝ, c > 0 ∧
    ((A.card * B.card : ℝ) / (4 : ℝ)^n)
      ≤ Real.exp (-c * n) :=
by
  sorry

def boolToReal : Bool → ℝ
  | true  => 1
  | false => -1

def inner {n : ℕ} (x y : BitString n) : ℝ :=
  ∑ i : Fin n, (boolToReal (x i)) * (boolToReal (y i))

def IsGapOrthogonal (n : ℕ) (x y : BitString n) (b : Bool) : Prop :=
  (|inner x y| ≤ Real.sqrt (n : ℝ) → b = true) ∧
  (Real.sqrt (n : ℝ) < |inner x y| → b = false)

theorem publicCoin_protocol_lower_bound
    (ε : ℝ) (hε : ε < 1 / 2) :
    ∃ c > 0,
      ∀ {n m : ℕ}
        (p : PublicCoin.Protocol (CoinTape m)
          (BitString n) (BitString n) Bool),
        p.ApproxSatisfies
            (fun x y b => IsGapOrthogonal n x y b) ε →
          c * (n : ℝ) ≤ (p.complexity : ℝ) :=
by
  sorry


end Functions.GapOrthogonality

end CommunicationComplexity
