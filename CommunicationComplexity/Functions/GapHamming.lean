import CommunicationComplexity.Basic
import CommunicationComplexity.BitString
import CommunicationComplexity.PublicCoin.Basic
import CommunicationComplexity.PrivateCoin.Basic

namespace CommunicationComplexity

namespace Functions.GapHamming

open MeasureTheory

/-- Gap-Hamming uses the shared bitstring type. -/
abbrev BitString (n : ℕ) := CommunicationComplexity.BitString n

/-- The lower threshold in the standard Gap-Hamming promise. -/
def lowThreshold (n : ℕ) : ℕ :=
  n / 2 - Nat.sqrt n

/-- The upper threshold in the standard Gap-Hamming promise. -/
def highThreshold (n : ℕ) : ℕ :=
  n / 2 + Nat.sqrt n

/-- The "yes" instances of the Gap-Hamming problem. -/
def HasNoGap (n : ℕ) (x y : BitString n) : Prop :=
  hammingDist x y ≤ lowThreshold n

/-- The "no" instances of the Gap-Hamming problem. -/
def HasGap (n : ℕ) (x y : BitString n) : Prop :=
  highThreshold n ≤ hammingDist x y

/-- The Gap-Hamming promise: the Hamming distance is either well below
`n / 2` or well above it, with a gap of order `√n`. -/
def Promise (n : ℕ) (x y : BitString n) : Prop :=
  HasNoGap n x y ∨ HasGap n x y

/-- `IsGapHamming n x y b` means that `b` is a valid Gap-Hamming output
for the input pair `(x, y)`. -/
def IsGapHamming (n : ℕ) (x y : BitString n) : Bool → Prop
  | true => HasNoGap n x y
  | false => HasGap n x y

@[simp]
theorem isGapHamming_true_iff (n : ℕ) (x y : BitString n) :
    IsGapHamming n x y true ↔ HasNoGap n x y := by
  rfl

@[simp]
theorem isGapHamming_false_iff (n : ℕ) (x y : BitString n) :
    IsGapHamming n x y false ↔ HasGap n x y := by
  rfl

/-- Gap-Hamming has linear randomized communication complexity.

This is stated directly for private-coin protocols solving the promise
problem, without introducing a global promise-problem complexity API. -/
theorem privateCoin_protocol_lower_bound
    (ε : ℝ) (hε : ε < 1 / 2) :
    ∃ c > 0,
      ∀ {n nX nY : ℕ}
        (p : PrivateCoin.Protocol (CoinTape nX) (CoinTape nY)
          (BitString n) (BitString n) Bool),
        p.ApproxSatisfies
            (fun x y b => Promise n x y → IsGapHamming n x y b) ε →
          c * (n : ℝ) ≤ (p.complexity : ℝ) := by
  sorry

/-- Public-coin variant of the Gap-Hamming linear lower bound. -/
theorem publicCoin_protocol_lower_bound
    (ε : ℝ) (hε : ε < 1 / 2) :
    ∃ c > 0,
      ∀ {n m : ℕ}
        (p : PublicCoin.Protocol (CoinTape m)
          (BitString n) (BitString n) Bool),
        p.ApproxSatisfies
            (fun x y b => Promise n x y → IsGapHamming n x y b) ε →
          c * (n : ℝ) ≤ (p.complexity : ℝ) := by
  sorry

end Functions.GapHamming

end CommunicationComplexity
