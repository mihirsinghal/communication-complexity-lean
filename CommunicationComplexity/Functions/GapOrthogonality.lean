import CommunicationComplexity.Functions.GapHamming
import CommunicationComplexity.BitString
import CommunicationComplexity.PublicCoin.FiniteMessage
import CommunicationComplexity.Deterministic.Composition

namespace CommunicationComplexity

namespace Functions.GapHamming

abbrev signedBitProduct := CommunicationComplexity.BitString.signedBitProduct
abbrev signedInner := CommunicationComplexity.BitString.signedInner
abbrev agreementCount := CommunicationComplexity.BitString.agreementCount

theorem agreementCount_add_hammingDist_eq_length {n : ℕ} (x y : BitString n) :
    agreementCount x y + hammingDist x y = n :=
  CommunicationComplexity.BitString.agreementCount_add_hammingDist_eq_length x y

theorem agreementCount_eq_length_sub_hammingDist {n : ℕ} (x y : BitString n) :
    (agreementCount x y : ℤ) = n - hammingDist x y :=
  CommunicationComplexity.BitString.agreementCount_eq_length_sub_hammingDist x y

theorem signedInner_eq_length_sub_twice_hammingDist {n : ℕ} (x y : BitString n) :
    signedInner x y = n - 2 * hammingDist x y :=
  CommunicationComplexity.BitString.signedInner_eq_length_sub_twice_hammingDist x y

theorem signedInner_eq_agreementCount_sub_hammingDist {n : ℕ} (x y : BitString n) :
    signedInner x y = agreementCount x y - hammingDist x y :=
  CommunicationComplexity.BitString.signedInner_eq_agreementCount_sub_hammingDist x y

theorem signedInner_append {m n : ℕ}
    (x₁ : Fin m → Bool) (x₂ : Fin n → Bool)
    (y₁ : Fin m → Bool) (y₂ : Fin n → Bool) :
    signedInner (Fin.append x₁ x₂) (Fin.append y₁ y₂) =
      signedInner x₁ y₁ + signedInner x₂ y₂ :=
  CommunicationComplexity.BitString.signedInner_append x₁ x₂ y₁ y₂

theorem signedInner_comp_cast {m n : ℕ} (h : m = n)
    (x y : Fin n → Bool) :
    signedInner (x ∘ Fin.cast h) (y ∘ Fin.cast h) = signedInner x y :=
  CommunicationComplexity.BitString.signedInner_comp_cast h x y

theorem signedInner_amplify {a n : ℕ} (x y : BitString n) :
    signedInner (Fin.repeat a x) (Fin.repeat a y) = a * signedInner x y :=
  CommunicationComplexity.BitString.signedInner_amplify x y

end Functions.GapHamming

namespace Functions.GapOrthogonality

open Functions.GapHamming
open scoped BigOperators
open MeasureTheory

/-- Gap-Orthogonality uses the same Boolean-string representation as
Gap-Hamming. -/
abbrev BitString (n : ℕ) := GapHamming.BitString n

/-- Repeat a string `a` times. This is the `x^a` operation in the book's
reduction sketch. -/
abbrev amplify (a : ℕ) (x : BitString n) : BitString (a * n) :=
  Fin.repeat a x

/-- A constant Boolean string of length `b`. -/
def constBits (b : ℕ) (bit : Bool) : BitString b :=
  fun _ => bit

/-- Repeat a string `a` times and then append `b` constant bits. This is
the `x^a c^b` construction appearing in the reduction. -/
def amplifyAndPad (a b : ℕ) (bit : Bool) (x : BitString n) :
    BitString (a * n + b) :=
  Fin.append (amplify a x) (constBits b bit)

/-- The signed inner product of two constant strings is the common
single-coordinate contribution multiplied by the length. -/
theorem signedInner_constBits (b : ℕ) (bit₁ bit₂ : Bool) :
    signedInner (constBits b bit₁) (constBits b bit₂) =
      b * signedBitProduct bit₁ bit₂ := by
  unfold signedInner constBits
  simp [Finset.sum_const, Fintype.card_fin]

/-- Appending constant tails changes the signed inner product by an
explicit additive term coming from the tails. -/
theorem signedInner_amplifyAndPad
    (a b : ℕ) (bit₁ bit₂ : Bool) (x y : BitString n) :
    signedInner (amplifyAndPad a b bit₁ x) (amplifyAndPad a b bit₂ y) =
      signedInner (amplify a x) (amplify a y) +
        b * signedBitProduct bit₁ bit₂ := by
  unfold amplifyAndPad
  rw [GapHamming.signedInner_append, signedInner_constBits]

/-- The padded instance whose tail is all `true`. -/
def sameTailInstance (a b : ℕ) (x : BitString n) : BitString (a * n + b) :=
  amplifyAndPad a b true x

/-- The padded instance whose tail is all `false`. -/
def oppositeTailInstance (a b : ℕ) (y : BitString n) : BitString (a * n + b) :=
  amplifyAndPad a b false y

namespace PublicCoin.Protocol

/-- A public-coin Gap-Hamming solver induces a public-coin
Gap-Orthogonality solver by running the Gap-Hamming protocol on the two
padded instances and decoding the resulting output bits. -/
noncomputable abbrev reduceGapHamming
    {Ω : Type*} (a b : ℕ) (decode : Bool → Bool → Bool)
    (p : PublicCoin.Protocol Ω
      (GapHamming.BitString (a * n + b))
      (GapHamming.BitString (a * n + b)) Bool) :
    PublicCoin.Protocol Ω (BitString n) (BitString n) Bool :=
  let p' := PublicCoin.FiniteMessage.Protocol.ofProtocol p
  let p₁ : PublicCoin.FiniteMessage.Protocol Ω (BitString n) (BitString n) Bool :=
    p'.comap
      (fun (wx : Ω × BitString n) => (wx.1, sameTailInstance a b wx.2))
      (fun (wy : Ω × BitString n) => (wy.1, sameTailInstance a b wy.2))
  let p₂ : PublicCoin.FiniteMessage.Protocol Ω (BitString n) (BitString n) Bool :=
    p'.comap
      (fun (wx : Ω × BitString n) => (wx.1, sameTailInstance a b wx.2))
      (fun (wy : Ω × BitString n) => (wy.1, oppositeTailInstance a b wy.2))
  let ppair : PublicCoin.FiniteMessage.Protocol Ω (BitString n) (BitString n) (Bool × Bool) :=
    (Deterministic.FiniteMessage.Protocol.prod p₁ p₂).comap
      (fun (wx : Ω × BitString n) => ((wx.1, wx.2), (wx.1, wx.2)))
      (fun (wy : Ω × BitString n) => ((wy.1, wy.2), (wy.1, wy.2)))
  (ppair.map (fun out => decode out.1 out.2)).toProtocol

@[simp]
theorem reduceGapHamming_rrun
    {Ω : Type*} (a b : ℕ) (decode : Bool → Bool → Bool)
    (p : PublicCoin.Protocol Ω
      (GapHamming.BitString (a * n + b))
      (GapHamming.BitString (a * n + b)) Bool)
    (x y : BitString n) (ω : Ω) :
    (reduceGapHamming a b decode p).rrun x y ω =
      decode
        (p.rrun (sameTailInstance a b x) (sameTailInstance a b y) ω)
        (p.rrun (sameTailInstance a b x) (oppositeTailInstance a b y) ω) := by
  simp [reduceGapHamming]
  have h1 :
      Deterministic.FiniteMessage.Protocol.run
          (PublicCoin.FiniteMessage.Protocol.ofProtocol p)
          (ω, sameTailInstance a b x) (ω, sameTailInstance a b y) =
        Deterministic.Protocol.run p
          (ω, sameTailInstance a b x) (ω, sameTailInstance a b y) := by
    simpa [PublicCoin.FiniteMessage.Protocol.rrun, PublicCoin.Protocol.rrun]
      using PublicCoin.FiniteMessage.Protocol.ofProtocol_rrun p
        (sameTailInstance a b x) (sameTailInstance a b y) ω
  have h2 :
      Deterministic.FiniteMessage.Protocol.run
          (PublicCoin.FiniteMessage.Protocol.ofProtocol p)
          (ω, sameTailInstance a b x) (ω, oppositeTailInstance a b y) =
        Deterministic.Protocol.run p
          (ω, sameTailInstance a b x) (ω, oppositeTailInstance a b y) := by
    simpa [PublicCoin.FiniteMessage.Protocol.rrun, PublicCoin.Protocol.rrun]
      using PublicCoin.FiniteMessage.Protocol.ofProtocol_rrun p
        (sameTailInstance a b x) (oppositeTailInstance a b y) ω
  rw [h1, h2]

@[simp]
theorem reduceGapHamming_complexity
    {Ω : Type*} (a b : ℕ) (decode : Bool → Bool → Bool)
    (p : PublicCoin.Protocol Ω
      (GapHamming.BitString (a * n + b))
      (GapHamming.BitString (a * n + b)) Bool) :
    (reduceGapHamming a b decode p).complexity = 2 * p.complexity := by
  simp [reduceGapHamming, Nat.two_mul,
    Deterministic.FiniteMessage.Protocol.comap_complexity,
    Deterministic.FiniteMessage.Protocol.prod_complexity,
    Deterministic.FiniteMessage.Protocol.map_complexity]

end PublicCoin.Protocol

/-- The signed inner product of the two same-tail padded instances. -/
theorem signedInner_sameTailInstance (a b : ℕ) (x y : BitString n) :
    signedInner (sameTailInstance a b x) (sameTailInstance a b y) =
      a * GapHamming.signedInner x y + b := by
  unfold sameTailInstance
  rw [signedInner_amplifyAndPad, GapHamming.signedInner_amplify]
  simp [GapHamming.signedBitProduct]

/-- The signed inner product of the mixed-tail padded instances. -/
theorem signedInner_oppositeTailInstance (a b : ℕ) (x y : BitString n) :
    signedInner (sameTailInstance a b x) (oppositeTailInstance a b y) =
      a * GapHamming.signedInner x y - b := by
  unfold sameTailInstance oppositeTailInstance
  rw [signedInner_amplifyAndPad, GapHamming.signedInner_amplify]
  simp [GapHamming.signedBitProduct, sub_eq_add_neg]

/-- The "almost orthogonal" side of the promise: the signed inner
product has small magnitude. -/
def HasSmallInner (n : ℕ) (x y : BitString n) : Prop :=
  |GapHamming.signedInner x y| < Nat.sqrt n

/-- The "far from orthogonal" side of the promise: the signed inner
product has magnitude at least `2 * √n`. -/
def HasLargeInner (n : ℕ) (x y : BitString n) : Prop :=
  2 * Nat.sqrt n ≤ |GapHamming.signedInner x y|

/-- The promise for Gap-Orthogonality: the signed inner product is
either small in magnitude or definitely large. -/
def Promise (n : ℕ) (x y : BitString n) : Prop :=
  HasSmallInner n x y ∨ HasLargeInner n x y

/-- A Boolean output is valid for Gap-Orthogonality if `true` certifies
"small inner product" and `false` certifies "large inner product". -/
def IsGapOrthogonal (n : ℕ) (x y : BitString n) : Bool → Prop
  | true => HasSmallInner n x y
  | false => HasLargeInner n x y

@[simp]
theorem isGapOrthogonal_true_iff (n : ℕ) (x y : BitString n) :
    IsGapOrthogonal n x y true ↔ HasSmallInner n x y := by
  rfl

@[simp]
theorem isGapOrthogonal_false_iff (n : ℕ) (x y : BitString n) :
    IsGapOrthogonal n x y false ↔ HasLargeInner n x y := by
  rfl

/-- Restatement of the Hamming-distance identity in the
Gap-Orthogonality namespace. -/
theorem signedInner_eq_n_sub_two_mul_hammingDist
    {n : ℕ} (x y : BitString n) :
    GapHamming.signedInner x y = n - 2 * hammingDist x y :=
  GapHamming.signedInner_eq_length_sub_twice_hammingDist x y

/-- A Gap-Hamming yes-instance has signed inner product at least
`2 * √n - 1`. The `-1` accounts for parity when `n` is odd. -/
theorem two_sqrt_le_signedInner_of_hasNoGap
    {n : ℕ} {x y : BitString n}
    (hn : Nat.sqrt n ≤ n / 2)
    (h : GapHamming.HasNoGap n x y) :
    (2 * Nat.sqrt n : ℤ) - 1 ≤ GapHamming.signedInner x y := by
  unfold GapHamming.HasNoGap GapHamming.lowThreshold at h
  have hs := GapHamming.signedInner_eq_length_sub_twice_hammingDist x y
  omega

/-- A Gap-Hamming no-instance has signed inner product at most
`1 - 2 * √n`. The `+1` accounts for parity when `n` is odd. -/
theorem signedInner_le_neg_two_sqrt_of_hasGap
    {n : ℕ} {x y : BitString n}
    (h : GapHamming.HasGap n x y) :
    GapHamming.signedInner x y ≤ 1 - (2 * Nat.sqrt n : ℤ) := by
  unfold GapHamming.HasGap GapHamming.highThreshold at h
  have hs := GapHamming.signedInner_eq_length_sub_twice_hammingDist x y
  omega

/-- A signed inner product of at least `2 * √n` certifies a
Gap-Hamming yes-instance. -/
theorem hasNoGap_of_two_sqrt_le_signedInner
    {n : ℕ} {x y : BitString n}
    (h : (2 * Nat.sqrt n : ℤ) ≤ GapHamming.signedInner x y) :
    GapHamming.HasNoGap n x y := by
  unfold GapHamming.HasNoGap GapHamming.lowThreshold
  have hs := GapHamming.signedInner_eq_length_sub_twice_hammingDist x y
  omega

/-- A signed inner product of at most `-2 * √n` certifies a
Gap-Hamming no-instance. -/
theorem hasGap_of_signedInner_le_neg_two_sqrt
    {n : ℕ} {x y : BitString n}
    (h : GapHamming.signedInner x y ≤ -(2 * Nat.sqrt n : ℤ)) :
    GapHamming.HasGap n x y := by
  unfold GapHamming.HasGap GapHamming.highThreshold
  have hs := GapHamming.signedInner_eq_length_sub_twice_hammingDist x y
  omega

/-- The padded length used in the reduction has square root at most
`20 * (√n + 2)`. -/
theorem sqrt_reductionLength_le (n : ℕ) :
    Nat.sqrt (400 * n + 600 * Nat.sqrt n) ≤ 20 * (Nat.sqrt n + 2) := by
  let r := Nat.sqrt n
  have hn : n ≤ r * r + r + r := by
    simpa [r] using Nat.sqrt_le_add n
  have hbound₁ : 400 * n + 600 * r ≤ 400 * (r * r + r + r) + 600 * r := by
    omega
  have hbound₂ : 400 * (r * r + r + r) + 600 * r ≤ (20 * (r + 2)) * (20 * (r + 2)) := by
    ring_nf
    omega
  have hbound : 400 * n + 600 * r ≤ (20 * (r + 2)) * (20 * (r + 2)) :=
    hbound₁.trans hbound₂
  have hsqrt :
      Nat.sqrt (400 * n + 600 * r) ≤ Nat.sqrt ((20 * (r + 2)) * (20 * (r + 2))) := by
    exact Nat.sqrt_le_sqrt hbound
  simpa [r, Nat.sqrt_eq] using hsqrt

/-- For positive input length, the padded reduction length is large
enough that `√N ≤ N / 2`. -/
theorem sqrt_reductionLength_le_half {n : ℕ} (hn : n ≠ 0) :
    Nat.sqrt (400 * n + 600 * Nat.sqrt n) ≤ (400 * n + 600 * Nat.sqrt n) / 2 := by
  let r := Nat.sqrt n
  have hr_pos : 1 ≤ r := by
    simpa [r] using Nat.succ_le_of_lt (Nat.sqrt_pos.2 (Nat.pos_of_ne_zero hn))
  have hr_le_n : r ≤ n := by
    simpa [r] using Nat.sqrt_le_self n
  have hsqrt := sqrt_reductionLength_le n
  have hlarge : 20 * (r + 2) ≤ (400 * n + 600 * r) / 2 := by
    omega
  simpa [r] using hsqrt.trans hlarge

/-- Formal version of the reduction sketched in the book: there are
repetition and padding parameters `a, b`, together with a decoding rule
for the two Gap-Hamming outputs, such that every promised
Gap-Orthogonality instance can be solved from the two corresponding
Gap-Hamming instances. -/
theorem reduction_to_gapHamming
    (n : ℕ) :
    ∃ a b : ℕ, ∃ decode : Bool → Bool → Bool,
      ∀ {x y : BitString n}, Promise n x y →
        let u := sameTailInstance a b x
        let v₁ := sameTailInstance a b y
        let v₂ := oppositeTailInstance a b y
        GapHamming.Promise (a * n + b) u v₁ →
          GapHamming.Promise (a * n + b) u v₂ →
          ∀ {out₁ out₂ : Bool},
            GapHamming.IsGapHamming (a * n + b) u v₁ out₁ →
            GapHamming.IsGapHamming (a * n + b) u v₂ out₂ →
            IsGapOrthogonal n x y (decode out₁ out₂) := by
  by_cases h0 : n = 0
  · subst h0
    refine ⟨1, 1, fun _ _ => false, ?_⟩
    intro x y hxy
    dsimp [sameTailInstance, oppositeTailInstance, amplifyAndPad, amplify, constBits]
    intro _ _ out₁ out₂ hout₁ hout₂
    simp [IsGapOrthogonal, HasLargeInner, GapHamming.signedInner]
  · let r := Nat.sqrt n
    let N := 400 * n + 600 * r
    refine ⟨400, 600 * r, fun out₁ out₂ => decide (out₁ ≠ out₂), ?_⟩
    intro x y hxy
    dsimp [N]
    intro _ _ out₁ out₂ hout₁ hout₂
    have hr_pos : 1 ≤ r := by
      simpa [r] using Nat.succ_le_of_lt (Nat.sqrt_pos.2 (Nat.pos_of_ne_zero h0))
    have hNhalf : Nat.sqrt (400 * n + 600 * r) ≤ (400 * n + 600 * r) / 2 := by
      simpa [r] using sqrt_reductionLength_le_half h0
    have hsqrtN : Nat.sqrt (400 * n + 600 * r) ≤ 20 * (r + 2) := by
      simpa [r] using sqrt_reductionLength_le n
    have hsqrtN₂ : 2 * Nat.sqrt (400 * n + 600 * r) ≤ 40 * r + 80 := by
      omega
    have hNpos : 0 < 400 * n + 600 * r := by
      have hn_pos : 0 < n := Nat.pos_of_ne_zero h0
      omega
    have hsqrtN_pos : 1 ≤ Nat.sqrt (400 * n + 600 * r) := by
      exact Nat.succ_le_of_lt (Nat.sqrt_pos.2 hNpos)
    rcases hxy with hsmall | hlarge
    · have hs₁ : (-(r : ℤ)) < GapHamming.signedInner x y := by
        exact (abs_lt.mp hsmall).1
      have hs₂ : GapHamming.signedInner x y < r := by
        exact (abs_lt.mp hsmall).2
      have hsame_lb :
          (2 * Nat.sqrt (400 * n + 600 * r) : ℤ) ≤
            GapHamming.signedInner (sameTailInstance 400 (600 * r) x)
              (sameTailInstance 400 (600 * r) y) := by
        rw [signedInner_sameTailInstance]
        omega
      have hoppo_ub :
          GapHamming.signedInner (sameTailInstance 400 (600 * r) x)
              (oppositeTailInstance 400 (600 * r) y) ≤
            -(2 * Nat.sqrt (400 * n + 600 * r) : ℤ) := by
        rw [signedInner_oppositeTailInstance]
        omega
      have hout₁_true : out₁ = true := by
        cases out₁ with
        | false =>
            simp at hout₁
            have hbad :=
              signedInner_le_neg_two_sqrt_of_hasGap (n := 400 * n + 600 * r) hout₁
            rw [signedInner_sameTailInstance] at hbad
            omega
        | true => rfl
      have hout₂_false : out₂ = false := by
        cases out₂ with
        | true =>
            simp at hout₂
            have hbad :=
              two_sqrt_le_signedInner_of_hasNoGap
                (n := 400 * n + 600 * r) hNhalf hout₂
            rw [signedInner_oppositeTailInstance] at hbad
            omega
        | false => rfl
      simpa [hout₁_true, hout₂_false, IsGapOrthogonal] using hsmall
    · have hs_cases :
          (2 * r : ℤ) ≤ GapHamming.signedInner x y ∨
            GapHamming.signedInner x y ≤ -(2 * r : ℤ) := by
        by_cases hs_nonneg : 0 ≤ GapHamming.signedInner x y
        · left
          simpa [HasLargeInner, r, abs_of_nonneg hs_nonneg] using hlarge
        · right
          have hs_nonpos : GapHamming.signedInner x y ≤ 0 := le_of_not_ge hs_nonneg
          have : (2 * r : ℤ) ≤ -GapHamming.signedInner x y := by
            simpa [HasLargeInner, r, abs_of_nonpos hs_nonpos] using hlarge
          omega
      rcases hs_cases with hs_pos | hs_neg
      · have hsame_lb :
            (2 * Nat.sqrt (400 * n + 600 * r) : ℤ) ≤
              GapHamming.signedInner (sameTailInstance 400 (600 * r) x)
                (sameTailInstance 400 (600 * r) y) := by
          rw [signedInner_sameTailInstance]
          omega
        have hoppo_lb :
            (2 * Nat.sqrt (400 * n + 600 * r) : ℤ) ≤
              GapHamming.signedInner (sameTailInstance 400 (600 * r) x)
                (oppositeTailInstance 400 (600 * r) y) := by
          rw [signedInner_oppositeTailInstance]
          omega
        have hout₁_true : out₁ = true := by
          cases out₁ with
          | false =>
              simp at hout₁
              have hbad :=
                signedInner_le_neg_two_sqrt_of_hasGap (n := 400 * n + 600 * r) hout₁
              rw [signedInner_sameTailInstance] at hbad
              omega
          | true => rfl
        have hout₂_true : out₂ = true := by
          cases out₂ with
          | false =>
              simp at hout₂
              have hbad :=
                signedInner_le_neg_two_sqrt_of_hasGap (n := 400 * n + 600 * r) hout₂
              rw [signedInner_oppositeTailInstance] at hbad
              omega
          | true => rfl
        simpa [hout₁_true, hout₂_true, IsGapOrthogonal] using hlarge
      · have hsame_ub :
            GapHamming.signedInner (sameTailInstance 400 (600 * r) x)
                (sameTailInstance 400 (600 * r) y) ≤
              -(2 * Nat.sqrt (400 * n + 600 * r) : ℤ) := by
          rw [signedInner_sameTailInstance]
          omega
        have hoppo_ub :
            GapHamming.signedInner (sameTailInstance 400 (600 * r) x)
                (oppositeTailInstance 400 (600 * r) y) ≤
              -(2 * Nat.sqrt (400 * n + 600 * r) : ℤ) := by
          rw [signedInner_oppositeTailInstance]
          omega
        have hout₁_false : out₁ = false := by
          cases out₁ with
          | true =>
              simp at hout₁
              have hbad :=
                two_sqrt_le_signedInner_of_hasNoGap
                  (n := 400 * n + 600 * r) hNhalf hout₁
              rw [signedInner_sameTailInstance] at hbad
              omega
          | false => rfl
        have hout₂_false : out₂ = false := by
          cases out₂ with
          | true =>
              simp at hout₂
              have hbad :=
                two_sqrt_le_signedInner_of_hasNoGap
                  (n := 400 * n + 600 * r) hNhalf hout₂
              rw [signedInner_oppositeTailInstance] at hbad
              omega
          | false => rfl
        simpa [hout₁_false, hout₂_false, IsGapOrthogonal] using hlarge

/-- Gap-Orthogonality has linear randomized communication complexity.

This is the lower bound that combines with `reduction_to_gapHamming`
to yield the corresponding lower bound for Gap-Hamming. -/
theorem publicCoin_reduceGapHamming_approxSatisfies
    (ε : ℝ) (hε₀ : 0 ≤ ε) (n m : ℕ) :
    ∃ a b : ℕ, ∃ decode : Bool → Bool → Bool,
      ∀ (p : PublicCoin.Protocol (CoinTape m)
          (GapHamming.BitString (a * n + b))
          (GapHamming.BitString (a * n + b)) Bool),
        p.ApproxSatisfies
            (fun x y out =>
              GapHamming.Promise (a * n + b) x y →
                GapHamming.IsGapHamming (a * n + b) x y out) ε →
        (PublicCoin.Protocol.reduceGapHamming a b decode p).ApproxSatisfies
            (fun x y out => Promise n x y → IsGapOrthogonal n x y out)
            (2 * ε) := by
  sorry

theorem privateCoin_protocol_lower_bound
    (ε : ℝ) (hε : ε < 1 / 2) :
    ∃ c > 0,
      ∀ {n nX nY : ℕ}
        (p : PrivateCoin.Protocol (CoinTape nX) (CoinTape nY)
          (BitString n) (BitString n) Bool),
        p.ApproxSatisfies
            (fun x y b => Promise n x y → IsGapOrthogonal n x y b) ε →
          c * (n : ℝ) ≤ (p.complexity : ℝ) := by
  sorry

/-- Public-coin variant of the Gap-Orthogonality linear lower bound. -/
theorem publicCoin_protocol_lower_bound
    (ε : ℝ) (hε : ε < 1 / 2) :
    ∃ c > 0,
      ∀ {n m : ℕ}
        (p : PublicCoin.Protocol (CoinTape m)
          (BitString n) (BitString n) Bool),
        p.ApproxSatisfies
            (fun x y b => Promise n x y → IsGapOrthogonal n x y b) ε →
          c * (n : ℝ) ≤ (p.complexity : ℝ) := by
  sorry

end Functions.GapOrthogonality

end CommunicationComplexity
