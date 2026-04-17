import CommunicationComplexity.Functions.GapHamming
import CommunicationComplexity.BitString
import CommunicationComplexity.PublicCoin.FiniteMessage
import CommunicationComplexity.PublicCoin.Minimax
import CommunicationComplexity.Deterministic.Composition

namespace CommunicationComplexity

namespace Functions.GapOrthogonality

open Functions.GapHamming
open scoped BigOperators
open MeasureTheory

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
    BitString.signedInner (constBits b bit₁) (constBits b bit₂) =
      b * BitString.signedBitProduct bit₁ bit₂ := by
  unfold BitString.signedInner constBits
  simp [Finset.sum_const, Fintype.card_fin]

/-- Appending constant tails changes the signed inner product by an
explicit additive term coming from the tails. -/
theorem signedInner_amplifyAndPad
    (a b : ℕ) (bit₁ bit₂ : Bool) (x y : BitString n) :
    BitString.signedInner (amplifyAndPad a b bit₁ x) (amplifyAndPad a b bit₂ y) =
      BitString.signedInner (amplify a x) (amplify a y) +
        b * BitString.signedBitProduct bit₁ bit₂ := by
  unfold amplifyAndPad
  rw [CommunicationComplexity.BitString.signedInner_append, signedInner_constBits]

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
      (BitString (a * n + b))
      (BitString (a * n + b)) Bool) :
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
      (BitString (a * n + b))
      (BitString (a * n + b)) Bool)
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
      (BitString (a * n + b))
      (BitString (a * n + b)) Bool) :
    (reduceGapHamming a b decode p).complexity = 2 * p.complexity := by
  simp [reduceGapHamming, Nat.two_mul,
    Deterministic.FiniteMessage.Protocol.comap_complexity,
    Deterministic.FiniteMessage.Protocol.prod_complexity,
    Deterministic.FiniteMessage.Protocol.map_complexity]

end PublicCoin.Protocol

/-- The signed inner product of the two same-tail padded instances. -/
theorem signedInner_sameTailInstance (a b : ℕ) (x y : BitString n) :
    BitString.signedInner (sameTailInstance a b x) (sameTailInstance a b y) = a * BitString.signedInner x y + b := by
  unfold sameTailInstance
  rw [signedInner_amplifyAndPad, CommunicationComplexity.BitString.signedInner_amplify]
  simp [BitString.signedBitProduct]

/-- The signed inner product of the mixed-tail padded instances. -/
theorem signedInner_oppositeTailInstance (a b : ℕ) (x y : BitString n) :
    BitString.signedInner (sameTailInstance a b x) (oppositeTailInstance a b y) = a * BitString.signedInner x y - b := by
  unfold sameTailInstance oppositeTailInstance
  rw [signedInner_amplifyAndPad, CommunicationComplexity.BitString.signedInner_amplify]
  simp [BitString.signedBitProduct, sub_eq_add_neg]

/-- The "almost orthogonal" side of the promise: the signed inner
product has small magnitude. -/
def HasSmallInner (n : ℕ) (x y : BitString n) : Prop :=
  |BitString.signedInner x y| < Nat.sqrt n

/-- The "far from orthogonal" side of the promise: the signed inner
product has magnitude at least `2 * √n`. -/
def HasLargeInner (n : ℕ) (x y : BitString n) : Prop :=
  2 * Nat.sqrt n ≤ |BitString.signedInner x y|

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
    BitString.signedInner x y = n - 2 * hammingDist x y :=
  CommunicationComplexity.BitString.signedInner_eq_length_sub_twice_hammingDist x y

/-- A Gap-Hamming yes-instance has signed inner product at least
`2 * √n - 1`. The `-1` accounts for parity when `n` is odd. -/
theorem two_sqrt_le_signedInner_of_hasNoGap
    {n : ℕ} {x y : BitString n}
    (hn : Nat.sqrt n ≤ n / 2)
    (h : GapHamming.HasNoGap n x y) :
    (2 * Nat.sqrt n : ℤ) - 1 ≤ BitString.signedInner x y := by
  unfold GapHamming.HasNoGap GapHamming.lowThreshold at h
  have hs := CommunicationComplexity.BitString.signedInner_eq_length_sub_twice_hammingDist x y
  omega

/-- A Gap-Hamming no-instance has signed inner product at most
`1 - 2 * √n`. The `+1` accounts for parity when `n` is odd. -/
theorem signedInner_le_neg_two_sqrt_of_hasGap
    {n : ℕ} {x y : BitString n}
    (h : GapHamming.HasGap n x y) :
    BitString.signedInner x y ≤ 1 - (2 * Nat.sqrt n : ℤ) := by
  unfold GapHamming.HasGap GapHamming.highThreshold at h
  have hs := CommunicationComplexity.BitString.signedInner_eq_length_sub_twice_hammingDist x y
  omega

/-- A signed inner product of at least `2 * √n` certifies a
Gap-Hamming yes-instance. -/
theorem hasNoGap_of_two_sqrt_le_signedInner
    {n : ℕ} {x y : BitString n}
    (h : (2 * Nat.sqrt n : ℤ) ≤ BitString.signedInner x y) :
    GapHamming.HasNoGap n x y := by
  unfold GapHamming.HasNoGap GapHamming.lowThreshold
  have hs := CommunicationComplexity.BitString.signedInner_eq_length_sub_twice_hammingDist x y
  omega

/-- A signed inner product of at most `-2 * √n` certifies a
Gap-Hamming no-instance. -/
theorem hasGap_of_signedInner_le_neg_two_sqrt
    {n : ℕ} {x y : BitString n}
    (h : BitString.signedInner x y ≤ -(2 * Nat.sqrt n : ℤ)) :
    GapHamming.HasGap n x y := by
  unfold GapHamming.HasGap GapHamming.highThreshold
  have hs := CommunicationComplexity.BitString.signedInner_eq_length_sub_twice_hammingDist x y
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
    simp [IsGapOrthogonal, HasLargeInner, BitString.signedInner]
  · let r := Nat.sqrt n
    let N := 400 * n + 600 * r
    refine ⟨400, 600 * r, fun out₁ out₂ => decide (out₁ ≠ out₂), ?_⟩
    intro x y hxy
    dsimp [N]
    intro _ _ out₁ out₂ hout₁ hout₂
    have hNhalf : Nat.sqrt (400 * n + 600 * r) ≤ (400 * n + 600 * r) / 2 := by
      simpa [r] using sqrt_reductionLength_le_half h0
    have hr_pos : (1 : ℤ) ≤ r := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.sqrt_pos.2 (Nat.pos_of_ne_zero h0))
    rcases hxy with hsmall | hlarge
    · have hs₁ : (-(r : ℤ)) < BitString.signedInner x y := by
        exact (abs_lt.mp hsmall).1
      have hs₂ : BitString.signedInner x y < r := by
        exact (abs_lt.mp hsmall).2
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
          (2 * r : ℤ) ≤ BitString.signedInner x y ∨
            BitString.signedInner x y ≤ -(2 * r : ℤ) := by
        by_cases hs_nonneg : 0 ≤ BitString.signedInner x y
        · left
          simpa [HasLargeInner, r, abs_of_nonneg hs_nonneg] using hlarge
        · right
          have hs_nonpos : BitString.signedInner x y ≤ 0 := le_of_not_ge hs_nonneg
          have : (2 * r : ℤ) ≤ -BitString.signedInner x y := by
            simpa [HasLargeInner, r, abs_of_nonpos hs_nonpos] using hlarge
          omega
      rcases hs_cases with hs_pos | hs_neg
      ·
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
      ·
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

/-
`HasNoGap` and `HasGap` are mutually exclusive when `√N ≥ 1`.
-/
private theorem noGap_gap_absurd {N : ℕ} (hN : 1 ≤ Nat.sqrt N)
    {u v : BitString N}
    (hno : GapHamming.HasNoGap N u v)
    (hgap : GapHamming.HasGap N u v) : False := by
  unfold HasGap HasNoGap at *;
  unfold lowThreshold highThreshold at * ; omega
/-
The padded same-tail instance satisfies the Gap-Hamming promise
when the Gap-Orthogonality promise holds and `√n ≥ 1`.
-/
private theorem padded_sameTail_promise
    {n : ℕ} (hn : 1 ≤ Nat.sqrt n) (x y : BitString n)
    (hprom : Promise n x y) :
    GapHamming.Promise (400 * n + 600 * Nat.sqrt n)
      (sameTailInstance 400 (600 * Nat.sqrt n) x)
      (sameTailInstance 400 (600 * Nat.sqrt n) y) := by
  cases hprom;
  · refine' Or.inl ( hasNoGap_of_two_sqrt_le_signedInner _ );
    rw [ signedInner_sameTailInstance ];
    have h_sqrt_le : Nat.sqrt (400 * n + 600 * n.sqrt) ≤ 20 * (n.sqrt + 2) := by
      exact sqrt_reductionLength_le n;
    grind +locals;
  · unfold HasLargeInner at *;
    cases abs_cases ( x.signedInner y ) <;> simp_all +decide [ BitString.signedInner ];
    · refine' Or.inl ( hasNoGap_of_two_sqrt_le_signedInner _ );
      rw [ signedInner_sameTailInstance ];
      norm_num [ BitString.signedInner ] at *;
      nlinarith [ Nat.sqrt_le ( 400 * n + 600 * n.sqrt ), Nat.lt_succ_sqrt n ];
    · refine' Or.inr _;
      refine' hasGap_of_signedInner_le_neg_two_sqrt _;
      rw [ signedInner_sameTailInstance ];
      have := sqrt_reductionLength_le n;
      norm_num [ BitString.signedInner ] at * ; linarith! [ abs_of_nonpos ( by linarith : ( ∑ i : Fin n, BitString.signedBitProduct ( x i ) ( y i ) ) ≤ 0 ) ]
/-
The padded opposite-tail instance satisfies the Gap-Hamming promise
when the Gap-Orthogonality promise holds and `√n ≥ 1`.
-/
private theorem padded_oppositeTail_promise
    {n : ℕ} (hn : 1 ≤ Nat.sqrt n) (x y : BitString n)
    (hprom : Promise n x y) :
    GapHamming.Promise (400 * n + 600 * Nat.sqrt n)
      (sameTailInstance 400 (600 * Nat.sqrt n) x)
      (oppositeTailInstance 400 (600 * Nat.sqrt n) y) := by
  cases hprom;
  · -- Use the fact that the inner product of the padded opposite-tail instance is less than or equal to -(2 * Nat.sqrt N).
    have h_inner_oppositeTailInstance : BitString.signedInner (sameTailInstance 400 (600 * Nat.sqrt n) x) (oppositeTailInstance 400 (600 * Nat.sqrt n) y) ≤ -(2 * Nat.sqrt (400 * n + 600 * Nat.sqrt n) : ℤ) := by
      rw [ signedInner_oppositeTailInstance ];
      norm_num at *;
      linarith [ abs_lt.mp ‹_›, sqrt_reductionLength_le n ];
    exact Or.inr ( hasGap_of_signedInner_le_neg_two_sqrt h_inner_oppositeTailInstance );
  · rename_i h_large;
    unfold HasLargeInner at h_large;
    by_cases h_nonneg : 0 ≤ BitString.signedInner x y;
    · refine' Or.inl _;
      refine' hasNoGap_of_two_sqrt_le_signedInner _;
      rw [ signedInner_oppositeTailInstance ];
      have := sqrt_reductionLength_le n;
      norm_num at * ; cases abs_cases ( BitString.signedInner x y ) <;> linarith;
    · refine Or.inr ?_;
      refine' hasGap_of_signedInner_le_neg_two_sqrt _;
      rw [ signedInner_oppositeTailInstance ];
      have := sqrt_reductionLength_le n;
      grind +splitImp
/-
For `n ≥ 1`, if both Gap-Hamming sub-protocol predicates hold on the
padded instances, then the decoded output is correct for
Gap-Orthogonality.
-/
private theorem reduction_pointwise_correct
    {n : ℕ} (hn : 1 ≤ Nat.sqrt n) (x y : BitString n)
    (out₁ out₂ : Bool)
    (h₁ : GapHamming.Promise (400 * n + 600 * Nat.sqrt n)
        (sameTailInstance 400 (600 * Nat.sqrt n) x)
        (sameTailInstance 400 (600 * Nat.sqrt n) y) →
      GapHamming.IsGapHamming (400 * n + 600 * Nat.sqrt n)
        (sameTailInstance 400 (600 * Nat.sqrt n) x)
        (sameTailInstance 400 (600 * Nat.sqrt n) y) out₁)
    (h₂ : GapHamming.Promise (400 * n + 600 * Nat.sqrt n)
        (sameTailInstance 400 (600 * Nat.sqrt n) x)
        (oppositeTailInstance 400 (600 * Nat.sqrt n) y) →
      GapHamming.IsGapHamming (400 * n + 600 * Nat.sqrt n)
        (sameTailInstance 400 (600 * Nat.sqrt n) x)
        (oppositeTailInstance 400 (600 * Nat.sqrt n) y) out₂)
    (hprom : Promise n x y) :
    IsGapOrthogonal n x y (decide (out₁ ≠ out₂)) := by
  have hprom₁ := padded_sameTail_promise hn x y hprom
  have hprom₂ := padded_oppositeTail_promise hn x y hprom
  have hgh₁ := h₁ hprom₁
  have hgh₂ := h₂ hprom₂
  have hNsqrt : 1 ≤ Nat.sqrt (400 * n + 600 * Nat.sqrt n) := by
    exact Nat.succ_le_of_lt (Nat.sqrt_pos.mpr (by omega))
  -- Key helper: determine output from HasNoGap/HasGap
  have out₁_of_noGap (hno : GapHamming.HasNoGap (400 * n + 600 * Nat.sqrt n)
      (sameTailInstance 400 (600 * Nat.sqrt n) x)
      (sameTailInstance 400 (600 * Nat.sqrt n) y)) : out₁ = true := by
    cases out₁
    · exact absurd hno (fun h => noGap_gap_absurd hNsqrt h (hgh₁))
    · rfl
  have out₁_of_gap (hg : GapHamming.HasGap (400 * n + 600 * Nat.sqrt n)
      (sameTailInstance 400 (600 * Nat.sqrt n) x)
      (sameTailInstance 400 (600 * Nat.sqrt n) y)) : out₁ = false := by
    cases out₁
    · rfl
    · exact absurd hg (fun h => noGap_gap_absurd hNsqrt (hgh₁) h)
  have out₂_of_noGap (hno : GapHamming.HasNoGap (400 * n + 600 * Nat.sqrt n)
      (sameTailInstance 400 (600 * Nat.sqrt n) x)
      (oppositeTailInstance 400 (600 * Nat.sqrt n) y)) : out₂ = true := by
    cases out₂
    · exact absurd hno (fun h => noGap_gap_absurd hNsqrt h (hgh₂))
    · rfl
  have out₂_of_gap (hg : GapHamming.HasGap (400 * n + 600 * Nat.sqrt n)
      (sameTailInstance 400 (600 * Nat.sqrt n) x)
      (oppositeTailInstance 400 (600 * Nat.sqrt n) y)) : out₂ = false := by
    cases out₂
    · rfl
    · exact absurd hg (fun h => noGap_gap_absurd hNsqrt (hgh₂) h)
  rcases hprom with hsmall | hlarge
  · -- HasSmallInner case: same-tail is HasNoGap, opposite-tail is HasGap
    have hnoGap₁ : GapHamming.HasNoGap (400 * n + 600 * Nat.sqrt n)
        (sameTailInstance 400 (600 * Nat.sqrt n) x)
        (sameTailInstance 400 (600 * Nat.sqrt n) y) := by
      apply hasNoGap_of_two_sqrt_le_signedInner
      rw [signedInner_sameTailInstance]
      have hsqrt := sqrt_reductionLength_le n
      unfold HasSmallInner at hsmall
      have := abs_lt.mp hsmall
      push_cast at *; nlinarith
    have hGap₂ : GapHamming.HasGap (400 * n + 600 * Nat.sqrt n)
        (sameTailInstance 400 (600 * Nat.sqrt n) x)
        (oppositeTailInstance 400 (600 * Nat.sqrt n) y) := by
      apply hasGap_of_signedInner_le_neg_two_sqrt
      rw [signedInner_oppositeTailInstance]
      have hsqrt := sqrt_reductionLength_le n
      unfold HasSmallInner at hsmall
      have := abs_lt.mp hsmall
      push_cast at *; nlinarith
    rw [out₁_of_noGap hnoGap₁, out₂_of_gap hGap₂]
    exact hsmall
  · -- HasLargeInner case
    by_cases hsign : (0 : ℤ) ≤ BitString.signedInner x y
    · -- signedInner ≥ 0, so ≥ 2r: both HasNoGap
      have hnoGap₁ : GapHamming.HasNoGap (400 * n + 600 * Nat.sqrt n)
          (sameTailInstance 400 (600 * Nat.sqrt n) x)
          (sameTailInstance 400 (600 * Nat.sqrt n) y) := by
        apply hasNoGap_of_two_sqrt_le_signedInner
        rw [signedInner_sameTailInstance]
        have hsqrt := sqrt_reductionLength_le n
        unfold HasLargeInner at hlarge
        have := abs_of_nonneg hsign ▸ hlarge
        push_cast at *; nlinarith
      have hnoGap₂ : GapHamming.HasNoGap (400 * n + 600 * Nat.sqrt n)
          (sameTailInstance 400 (600 * Nat.sqrt n) x)
          (oppositeTailInstance 400 (600 * Nat.sqrt n) y) := by
        apply hasNoGap_of_two_sqrt_le_signedInner
        rw [signedInner_oppositeTailInstance]
        have hsqrt := sqrt_reductionLength_le n
        unfold HasLargeInner at hlarge
        have := abs_of_nonneg hsign ▸ hlarge
        push_cast at *; nlinarith
      rw [out₁_of_noGap hnoGap₁, out₂_of_noGap hnoGap₂]
      exact hlarge
    · -- signedInner < 0, so ≤ -2r: both HasGap
      push_neg at hsign
      have hGap₁ : GapHamming.HasGap (400 * n + 600 * Nat.sqrt n)
          (sameTailInstance 400 (600 * Nat.sqrt n) x)
          (sameTailInstance 400 (600 * Nat.sqrt n) y) := by
        apply hasGap_of_signedInner_le_neg_two_sqrt
        rw [signedInner_sameTailInstance]
        have hsqrt := sqrt_reductionLength_le n
        unfold HasLargeInner at hlarge
        have := abs_of_neg hsign ▸ hlarge
        push_cast at *; nlinarith
      have hGap₂ : GapHamming.HasGap (400 * n + 600 * Nat.sqrt n)
          (sameTailInstance 400 (600 * Nat.sqrt n) x)
          (oppositeTailInstance 400 (600 * Nat.sqrt n) y) := by
        apply hasGap_of_signedInner_le_neg_two_sqrt
        rw [signedInner_oppositeTailInstance]
        have hsqrt := sqrt_reductionLength_le n
        unfold HasLargeInner at hlarge
        have := abs_of_neg hsign ▸ hlarge
        push_cast at *; nlinarith
      rw [out₁_of_gap hGap₁, out₂_of_gap hGap₂]
      exact hlarge
/-
Gap-Orthogonality has linear randomized communication complexity.
This is the lower bound that combines with `reduction_to_gapHamming`
to yield the corresponding lower bound for Gap-Hamming. -/
theorem publicCoin_reduceGapHamming_approxSatisfies
    (ε : ℝ) (hε₀ : 0 ≤ ε) (n m : ℕ) :
    ∃ a b : ℕ, ∃ decode : Bool → Bool → Bool,
      ∀ (p : PublicCoin.Protocol (CoinTape m)
          (BitString (a * n + b))
          (BitString (a * n + b)) Bool),
        p.ApproxSatisfies
            (fun x y out =>
              GapHamming.Promise (a * n + b) x y →
                GapHamming.IsGapHamming (a * n + b) x y out) ε →
        (PublicCoin.Protocol.reduceGapHamming a b decode p).ApproxSatisfies
            (fun x y out => Promise n x y → IsGapOrthogonal n x y out)
            (2 * ε) := by
  by_cases hn : n = 0;
  · use 0, 0, fun _ _ => Bool.false;
    intro p hp x y; simp +decide [ PublicCoin.Protocol.reduceGapHamming ] ;
    unfold Promise HasLargeInner; simp_all +decide [ BitString.signedInner ] ;
  · refine' ⟨ 400, 600 * Nat.sqrt n, _, _ ⟩;
    exact fun out₁ out₂ => decide ( out₁ ≠ out₂ );
    intro p hp x y;
    have h_subset : {ω | ¬(Promise n x y → IsGapOrthogonal n x y ((PublicCoin.Protocol.reduceGapHamming 400 (600 * n.sqrt) (fun out₁ out₂ => decide (out₁ ≠ out₂)) p).rrun x y ω))} ⊆ {ω | ¬(GapHamming.Promise (400 * n + 600 * n.sqrt) (sameTailInstance 400 (600 * n.sqrt) x) (sameTailInstance 400 (600 * n.sqrt) y) → GapHamming.IsGapHamming (400 * n + 600 * n.sqrt) (sameTailInstance 400 (600 * n.sqrt) x) (sameTailInstance 400 (600 * n.sqrt) y) (p.rrun (sameTailInstance 400 (600 * n.sqrt) x) (sameTailInstance 400 (600 * n.sqrt) y) ω))} ∪ {ω | ¬(GapHamming.Promise (400 * n + 600 * n.sqrt) (sameTailInstance 400 (600 * n.sqrt) x) (oppositeTailInstance 400 (600 * n.sqrt) y) → GapHamming.IsGapHamming (400 * n + 600 * n.sqrt) (sameTailInstance 400 (600 * n.sqrt) x) (oppositeTailInstance 400 (600 * n.sqrt) y) (p.rrun (sameTailInstance 400 (600 * n.sqrt) x) (oppositeTailInstance 400 (600 * n.sqrt) y) ω))} := by
      intro ω hω;
      contrapose! hω; simp_all +decide;
      convert reduction_pointwise_correct ( Nat.sqrt_pos.mpr ( Nat.pos_of_ne_zero hn ) ) x y _ _ hω.1 hω.2 using 1;
      simp +decide [ PublicCoin.FiniteMessage.Protocol.ofProtocol ];
      congr! 2;
      congr! 2;
      · exact Deterministic.FiniteMessage.Protocol.ofProtocol_run p _ _;
      · exact Deterministic.FiniteMessage.Protocol.ofProtocol_run p _ _;
    refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_mono h_subset ) _;
    · finiteness;
    · refine' le_trans ( ENNReal.toReal_mono _ <| MeasureTheory.measure_union_le _ _ ) _;
      · simp +decide [ MeasureTheory.MeasureSpace.volume ];
      · rw [ ENNReal.toReal_add ];
        · convert add_le_add ( hp ( sameTailInstance 400 ( 600 * n.sqrt ) x ) ( sameTailInstance 400 ( 600 * n.sqrt ) y ) ) ( hp ( sameTailInstance 400 ( 600 * n.sqrt ) x ) ( oppositeTailInstance 400 ( 600 * n.sqrt ) y ) ) using 1 ; ring;
        · exact measure_ne_top _ _;
        · exact measure_ne_top _ _

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

/-- A hard distribution for deterministic Gap-Orthogonality protocols
immediately yields the desired public-coin lower bound. This isolates
the remaining gap in the proof to finding the distributional lower
bound itself. -/
theorem publicCoin_protocol_lower_bound_of_hard_distribution
    (ε c : ℝ) (hc : 0 < c)
    (hdist : ∀ n : ℕ,
      ∃ μ : FiniteProbabilitySpace (BitString n × BitString n),
        ∀ (p : Deterministic.Protocol (BitString n) (BitString n) Bool),
          p.complexity ≤ Nat.ceil (c * (n : ℝ)) - 1 →
            p.distributionalFailure μ
              (fun x y b => Promise n x y → IsGapOrthogonal n x y b) > ε) :
    ∀ {n m : ℕ}
      (p : PublicCoin.Protocol (CoinTape m)
        (BitString n) (BitString n) Bool),
      p.ApproxSatisfies
          (fun x y b => Promise n x y → IsGapOrthogonal n x y b) ε →
        c * (n : ℝ) ≤ (p.complexity : ℝ) := by
  intro n m p hp
  by_cases hn : n = 0
  · subst hn
    simp
  · obtain ⟨μ, hμ⟩ := hdist n
    letI : FiniteProbabilitySpace (BitString n × BitString n) := μ
    have hfail :
        ∀ (q : Deterministic.Protocol (BitString n) (BitString n) Bool),
          q.complexity ≤ Nat.ceil (c * (n : ℝ)) - 1 →
            q.distributionalFailure μ
              (fun x y b => Promise n x y → IsGapOrthogonal n x y b) > ε := by
      intro q hq
      exact hμ q hq
    have hklt :
        Nat.ceil (c * (n : ℝ)) - 1 < p.complexity := by
      exact PublicCoin.protocol_lower_bound_satisfies
        (Q := fun x y b => Promise n x y → IsGapOrthogonal n x y b)
        ε (Nat.ceil (c * (n : ℝ)) - 1) μ hfail p hp
    have hceil_pos : 0 < Nat.ceil (c * (n : ℝ)) := by
      apply Nat.ceil_pos.mpr
      positivity
    have hceil_le : Nat.ceil (c * (n : ℝ)) ≤ p.complexity := by
      have hs := Nat.succ_le_of_lt hklt
      simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hceil_pos)] using hs
    calc
      c * (n : ℝ) ≤ Nat.ceil (c * (n : ℝ)) := Nat.le_ceil _
      _ ≤ (p.complexity : ℝ) := by exact_mod_cast hceil_le

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
