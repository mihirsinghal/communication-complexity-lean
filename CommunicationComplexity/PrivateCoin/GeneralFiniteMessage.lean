import CommunicationComplexity.PrivateCoin.Basic
import CommunicationComplexity.PrivateCoin.FiniteMessage
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open MeasureTheory

namespace CommunicationComplexity

/-- A generalized randomized two-party communication protocol where at each step,
a player sends an element of an arbitrary finite type `β` (rather than just a `Bool`).
This version uses arbitrary finite probability spaces `Ω_X`, `Ω_Y`.
Sending a `β`-valued message costs `⌈log₂ |β|⌉` bits.

Since `Ω_X` and `Ω_Y` are finite, all functions out of them are
automatically measurable, so no measurability hypotheses are needed. -/
inductive PrivateCoin.GeneralFiniteMessage.Protocol
    (Ω_X Ω_Y : Type*) [Fintype Ω_X] [Fintype Ω_Y]
    (X Y α : Type*) where
  | output (a : α) :
      PrivateCoin.GeneralFiniteMessage.Protocol Ω_X Ω_Y X Y α
  | alice {β : Type} [Fintype β] [Nonempty β]
      (f : X → Ω_X → β)
      (P : β → PrivateCoin.GeneralFiniteMessage.Protocol Ω_X Ω_Y X Y α) :
      PrivateCoin.GeneralFiniteMessage.Protocol Ω_X Ω_Y X Y α
  | bob {β : Type} [Fintype β] [Nonempty β]
      (f : Y → Ω_Y → β)
      (P : β → PrivateCoin.GeneralFiniteMessage.Protocol Ω_X Ω_Y X Y α) :
      PrivateCoin.GeneralFiniteMessage.Protocol Ω_X Ω_Y X Y α

namespace PrivateCoin.GeneralFiniteMessage.Protocol

variable {Ω_X Ω_Y X Y α : Type*} [Fintype Ω_X] [Fintype Ω_Y]

/-- Executes the generalized randomized protocol on inputs `x`, `y`
with random coins `ω_x`, `ω_y`. -/
def run (p : Protocol Ω_X Ω_Y X Y α)
    (x : X) (y : Y) (ω_x : Ω_X) (ω_y : Ω_Y) : α :=
  match p with
  | output a => a
  | alice f P => (P (f x ω_x)).run x y ω_x ω_y
  | bob f P => (P (f y ω_y)).run x y ω_x ω_y

/-- The communication complexity of a generalized randomized protocol.
Sending a `β`-valued message costs `⌈log₂ |β|⌉` bits. -/
def complexity : Protocol Ω_X Ω_Y X Y α → ℕ
  | output _ => 0
  | alice (β := β) _ P =>
      Nat.clog 2 (Fintype.card β) +
        Finset.univ.sup (fun i => (P i).complexity)
  | bob (β := β) _ P =>
      Nat.clog 2 (Fintype.card β) +
        Finset.univ.sup (fun i => (P i).complexity)

/-- Swaps the roles of Alice and Bob in a general finite-message protocol. -/
def swap : Protocol Ω_X Ω_Y X Y α → Protocol Ω_Y Ω_X Y X α
  | .output a => .output a
  | alice f P =>
      bob f (fun b => (P b).swap)
  | bob f P =>
      alice f (fun b => (P b).swap)

@[simp]
theorem swap_run (p : Protocol Ω_X Ω_Y X Y α)
    (x : X) (y : Y) (ω_x : Ω_X) (ω_y : Ω_Y) :
    p.swap.run y x ω_y ω_x = p.run x y ω_x ω_y := by
  induction p with
  | output a => simp [swap, run]
  | alice f P ih => simp only [swap, run]; exact ih _
  | bob f P ih => simp only [swap, run]; exact ih _

@[simp]
theorem swap_complexity (p : Protocol Ω_X Ω_Y X Y α) :
    p.swap.complexity = p.complexity := by
  induction p with
  | output a => simp [swap, complexity]
  | alice f P ih => simp only [swap, complexity, ih]
  | bob f P ih => simp only [swap, complexity, ih]

/-- A general finite-message protocol `ε`-satisfies a predicate `Q`
if for every input `(x, y)`, the probability that
`Q x y (p.run ...)` fails is at most `ε`. -/
def approx_satisfies
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    (p : Protocol Ω_X Ω_Y X Y α) (Q : X → Y → α → Prop)
    (ε : ℝ) : Prop :=
  ∀ x y,
    (volume {ω : Ω_X × Ω_Y |
      ¬Q x y (p.run x y ω.1 ω.2)}).toReal ≤ ε

open Classical in
/-- A general finite-message protocol `ε`-computes a function `f`
if for every input `(x, y)`, the probability of producing an
incorrect answer is at most `ε`. -/
def approx_computes
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    (p : Protocol Ω_X Ω_Y X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y,
    (volume {ω : Ω_X × Ω_Y |
      p.run x y ω.1 ω.2 ≠ f x y}).toReal ≤ ε

open Classical in
theorem approx_computes_eq_approx_satisfies
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    (p : Protocol Ω_X Ω_Y X Y α) (f : X → Y → α) (ε : ℝ) :
    p.approx_computes f ε =
      p.approx_satisfies (fun x y a => a = f x y) ε := by
  simp only [approx_computes, approx_satisfies, ne_eq]

/-- Embed a coin-flip randomized protocol into a generalized randomized
protocol over `CoinTape` probability spaces (with `β = Bool` at each step). -/
def ofProtocol {nX nY : ℕ} :
    PrivateCoin.Protocol nX nY X Y α →
      Protocol (CoinTape nX) (CoinTape nY) X Y α
  | PrivateCoin.Protocol.output a => output a
  | PrivateCoin.Protocol.alice f P =>
      alice f (fun b => ofProtocol (P b))
  | PrivateCoin.Protocol.bob f P =>
      bob f (fun b => ofProtocol (P b))

theorem ofProtocol_run {nX nY : ℕ}
    (p : PrivateCoin.Protocol nX nY X Y α)
    (x : X) (y : Y)
    (ω_x : CoinTape nX) (ω_y : CoinTape nY) :
    (ofProtocol p).run x y ω_x ω_y =
      p.run x y ω_x ω_y := by
  induction p with
  | output a =>
    simp [ofProtocol, run, PrivateCoin.Protocol.run]
  | alice f P ih =>
    simp [ofProtocol, run, PrivateCoin.Protocol.run, ih]
  | bob f P ih =>
    simp [ofProtocol, run, PrivateCoin.Protocol.run, ih]

theorem ofProtocol_complexity {nX nY : ℕ}
    (p : PrivateCoin.Protocol nX nY X Y α) :
    (ofProtocol p).complexity = p.complexity := by
  induction p with
  | output a =>
    simp [ofProtocol, complexity,
      PrivateCoin.Protocol.complexity]
  | alice f P ih =>
    simp only [ofProtocol, complexity,
      PrivateCoin.Protocol.complexity, ih]
    have : Nat.clog 2 (Fintype.card Bool) = 1 := by decide
    rw [this]
    have : (Finset.univ : Finset Bool) = {false, true} := by
      ext b; simp
    simp [this]
  | bob f P ih =>
    simp only [ofProtocol, complexity,
      PrivateCoin.Protocol.complexity, ih]
    have : Nat.clog 2 (Fintype.card Bool) = 1 := by decide
    rw [this]
    have : (Finset.univ : Finset Bool) = {false, true} := by
      ext b; simp
    simp [this]

/-- Every coin-flip randomized protocol can be viewed as a generalized
randomized protocol with the same run behavior and complexity. -/
theorem ofProtocol_equiv {nX nY : ℕ}
    (p : PrivateCoin.Protocol nX nY X Y α) :
    ∃ (P : Protocol (CoinTape nX) (CoinTape nY) X Y α),
      P.run = p.run ∧ P.complexity = p.complexity :=
  ⟨ofProtocol p,
   funext₂ fun x y => funext₂ fun ω_x ω_y =>
     ofProtocol_run p x y ω_x ω_y,
   ofProtocol_complexity p⟩

/-- Pull back the randomness of a general finite-message protocol
through maps `φ_X` and `φ_Y`, producing a finite-message protocol
over coin tapes. -/
def toFiniteMessage {nX nY : ℕ}
    (φ_X : CoinTape nX → Ω_X) (φ_Y : CoinTape nY → Ω_Y) :
    Protocol Ω_X Ω_Y X Y α →
      PrivateCoin.FiniteMessage.Protocol nX nY X Y α
  | .output a => .output a
  | alice f P =>
      PrivateCoin.FiniteMessage.Protocol.alice
        (fun x ω => f x (φ_X ω))
        (fun b => (P b).toFiniteMessage φ_X φ_Y)
  | bob f P =>
      PrivateCoin.FiniteMessage.Protocol.bob
        (fun y ω => f y (φ_Y ω))
        (fun b => (P b).toFiniteMessage φ_X φ_Y)

theorem toFiniteMessage_run {nX nY : ℕ}
    (φ_X : CoinTape nX → Ω_X) (φ_Y : CoinTape nY → Ω_Y)
    (p : Protocol Ω_X Ω_Y X Y α)
    (x : X) (y : Y) (ω_x : CoinTape nX) (ω_y : CoinTape nY) :
    (p.toFiniteMessage φ_X φ_Y).run x y ω_x ω_y =
      p.run x y (φ_X ω_x) (φ_Y ω_y) := by
  induction p with
  | output a =>
    simp [toFiniteMessage, run,
      PrivateCoin.FiniteMessage.Protocol.run]
  | alice f P ih =>
    simp only [toFiniteMessage, PrivateCoin.FiniteMessage.Protocol.run, run]
    exact ih _
  | bob f P ih =>
    simp only [toFiniteMessage, PrivateCoin.FiniteMessage.Protocol.run, run]
    exact ih _

theorem toFiniteMessage_complexity {nX nY : ℕ}
    (φ_X : CoinTape nX → Ω_X) (φ_Y : CoinTape nY → Ω_Y)
    (p : Protocol Ω_X Ω_Y X Y α) :
    (p.toFiniteMessage φ_X φ_Y).complexity = p.complexity := by
  induction p with
  | output a =>
    simp [toFiniteMessage, complexity,
      PrivateCoin.FiniteMessage.Protocol.complexity]
  | alice f P ih =>
    simp only [toFiniteMessage,
      PrivateCoin.FiniteMessage.Protocol.complexity,
      complexity, ih]
  | bob f P ih =>
    simp only [toFiniteMessage,
      PrivateCoin.FiniteMessage.Protocol.complexity,
      complexity, ih]

end PrivateCoin.GeneralFiniteMessage.Protocol

namespace Internal

/-- For any finite type `Ω` with a probability measure and any `δ > 0`,
there exist `n` and `φ : CoinTape n → Ω` such that for any set `S`,
the pushforward measure exceeds the true measure by at most `δ`. -/
theorem single_coin_approx
    {Ω : Type*} [Finite Ω]
    [MeasureSpace Ω] [DiscreteMeasurableSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (n : ℕ) (φ : CoinTape n → Ω),
      ∀ (S : Set Ω),
        (volume (φ ⁻¹' S : Set (CoinTape n))).toReal ≤
        (volume S).toReal + δ := by
  haveI : Nonempty Ω := nonempty_of_isProbabilityMeasure volume
  haveI : Fintype Ω := Fintype.ofFinite Ω
  classical
  -- Strategy: inverse CDF construction.
  -- Enumerate Ω via Fintype.equivFin, compute cumulative probabilities,
  -- partition CoinTape n (identified with Fin 2^n) into bins proportional
  -- to probabilities. Per-element discrepancy ≤ 1/2^n, so total ≤ |Ω|/2^n.
  -- Choose n with |Ω|/2^n ≤ δ.
  set k := Fintype.card Ω with hk_def
  have hk_pos : 0 < k := Fintype.card_pos
  -- Step 1: Choose n large enough that k / 2^n ≤ δ
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (k : ℝ) / 2 ^ n ≤ δ := by
    -- (1/2)^n → 0, so k * (1/2)^n < δ for large n
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
      (div_pos hδ (Nat.cast_pos.mpr hk_pos)) (by norm_num : (1 / 2 : ℝ) < 1)
    -- hn : (1/2)^n < δ/k
    refine ⟨n, le_of_lt ?_⟩
    -- Goal: k / 2^n < δ
    -- From hn, multiply by k: (1/2)^n * k < δ. And k/2^n = (1/2)^n * k.
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
  -- Weight for each element: w(j) = ⌊vol({e.symm j}) * N⌋
  set w : Fin k → ℕ := fun j =>
    Nat.floor ((volume ({e.symm j} : Set Ω)).toReal * N) with hw_def
  -- Cumulative weight: cumW(m) = Σ_{i < m} w(i)
  set cumW : ℕ → ℕ := fun m =>
    ∑ i ∈ Finset.range m, if h : i < k then w ⟨i, h⟩ else 0 with hcumW_def
  -- Step 3: Define φ using inverse CDF
  -- For index i, find the bin: count how many bins end at or before i
  -- binIdx(i) = |{j < k | cumW(j+1) ≤ i}|, capped at k-1
  set binIdx : ℕ → Fin k := fun i =>
    ⟨min ((Finset.range k).filter (fun j => cumW (j + 1) ≤ i)).card (k - 1),
     by omega⟩ with hbinIdx_def
  -- φ maps each coin tape element to the corresponding Ω element
  refine ⟨fun ω => e.symm (binIdx (eC ω).val), fun S => ?_⟩
  -- Step 4: Prove the bound for all S
  -- Key fact: on CoinTape n, volume = counting measure / N
  -- So vol(φ⁻¹(S)) = |{ω | φ(ω) ∈ S}| / N
  -- We bound |{ω | φ(ω) ∈ S}| ≤ (vol_Ω(S) * N) + k
  -- giving vol(φ⁻¹(S)) ≤ vol_Ω(S) + k/N ≤ vol_Ω(S) + δ
  set φ := fun ω => e.symm (binIdx (eC ω).val)
  -- Per-element weight bound: w(j) ≤ vol({e.symm j}) * N (floor ≤ original)
  have hw_le : ∀ j : Fin k, (w j : ℝ) ≤ (volume ({e.symm j} : Set Ω)).toReal * N := by
    intro j
    exact Nat.floor_le (by positivity)
  -- Probability sums to 1: Σ_j vol({e.symm j}) = 1
  have hprob_sum : ∑ j : Fin k, (volume ({e.symm j} : Set Ω)).toReal = 1 := by
    -- The singletons {e.symm j} for j : Fin k partition Ω
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
  -- Total weight: Σ_j w(j) ≤ N
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
  -- Weight deficit: N - Σ w ≤ k
  have hdeficit : N - ∑ j : Fin k, w j ≤ k := by
    -- Each ⌊vol_j * N⌋₊ ≥ vol_j * N - 1, so Σ w_j ≥ N - k
    by_contra h; push_neg at h
    -- h : k < N - Σ w j, so N > Σ w j + k
    have hN_bound : N ≤ ∑ j : Fin k, w j + k := by
      suffices (N : ℝ) ≤ ∑ j : Fin k, (w j : ℝ) + k by exact_mod_cast this
      calc (N : ℝ)
          = ∑ j : Fin k, (volume ({e.symm j} : Set Ω)).toReal * N := by
            rw [← Finset.sum_mul, hprob_sum, one_mul]
        _ ≤ ∑ j : Fin k, ((w j : ℝ) + 1) := by
            apply Finset.sum_le_sum; intro j _
            -- vol * N < ⌊vol * N⌋₊ + 1
            linarith [Nat.lt_floor_add_one
              ((volume ({e.symm j} : Set Ω)).toReal * N)]
        _ = ∑ j : Fin k, (w j : ℝ) + ∑ j : Fin k, (1 : ℝ) := by
            rw [← Finset.sum_add_distrib]
        _ = ∑ j : Fin k, (w j : ℝ) + k := by simp
    omega
  -- Fiber bound: |φ⁻¹(S)| ≤ Σ_{a ∈ S} w(e a) + (N - Σ w)
  -- (the deficit goes to the last bin which may overflow)
  -- First establish cumW properties needed for the fiber analysis
  have hcumW_mono : ∀ a b, a ≤ b → cumW a ≤ cumW b :=
    fun a b h => Finset.sum_le_sum_of_subset (Finset.range_mono h)
  have hcumW_step : ∀ j : Fin k, cumW (↑j + 1) = cumW ↑j + w j := by
    intro j; simp [cumW, Finset.sum_range_succ, j.isLt]
  have hcumW_k : cumW k = ∑ j : Fin k, w j := by
    simp only [cumW]
    -- Reindex: ∑ i ∈ range k, dite ... = ∑ j : Fin k, w j
    rw [← Fin.sum_univ_eq_sum_range
      (fun i => if h : i < k then w ⟨i, h⟩ else 0)]
    apply Finset.sum_congr rfl
    intro ⟨i, hi⟩ _
    simp [hi]
  have hcumW_le_N : ∀ j : Fin k, cumW (↑j + 1) ≤ N :=
    fun j => le_trans (hcumW_mono _ _ (by omega)) (hcumW_k ▸ hsum_le)
  -- For i in [cumW(j), cumW(j+1)), binIdx(i) = j
  have hbinIdx_eq : ∀ (j : Fin k) (i : ℕ),
      cumW ↑j ≤ i → i < cumW (↑j + 1) → binIdx i = j := by
    intro j i hlo hhi
    ext; simp only [binIdx]
    -- The filter is {m ∈ range k | cumW(m+1) ≤ i} = range j.val
    -- because for m < j: cumW(m+1) ≤ cumW(j) ≤ i
    --     and for m ≥ j: cumW(m+1) ≥ cumW(j+1) > i
    have hfilt : (Finset.range k).filter (fun m => cumW (m + 1) ≤ i) =
        Finset.range j.val := by
      ext m; simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨_, hm⟩
        by_contra h; push_neg at h
        -- m ≥ j.val, so cumW(m+1) ≥ cumW(j+1) > i
        have : cumW (j.val + 1) ≤ cumW (m + 1) := hcumW_mono _ _ (by omega)
        omega
      · intro hm; exact ⟨by omega, le_trans (hcumW_mono _ _ (by omega)) hlo⟩
    rw [hfilt, Finset.card_range]
    -- min(j.val, k-1) = j.val since j.val < k
    omega
  -- Each fiber has ≥ w(j) elements (via injection of interval [cumW j, cumW(j+1)))
  have hfib_ge : ∀ j : Fin k,
      w j ≤ (Finset.univ.filter (fun ω : CoinTape n =>
        binIdx (eC ω).val = j)).card := by
    intro j
    -- Inject [cumW j, cumW(j+1)) into the fiber via eC.symm
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
    -- Image of f is a subset of the fiber, with |image| = w j
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
    -- Complement counting: total fibers = N, complement fibers ≥ complement weight
    set filt := Finset.univ.filter (fun j : Fin k => e.symm j ∈ S)
    set filtC := Finset.univ.filter (fun j : Fin k => e.symm j ∉ S)
    have hdisj : Disjoint filt filtC :=
      Finset.disjoint_filter.mpr (fun j _ h1 h2 => h2 h1)
    have hunion : filt ∪ filtC = Finset.univ := by
      ext j; simp only [filt, filtC, Finset.mem_union, Finset.mem_filter,
        Finset.mem_univ, true_and, iff_true]; exact em _
    -- g maps CoinTape to Fin k (the bin assignment)
    set g : CoinTape n → Fin k := fun ω => binIdx (eC ω).val
    -- φ(ω) ∈ S ↔ g(ω) ∈ filt
    have hphi_g : ∀ ω : CoinTape n,
        (φ ω ∈ S) ↔ (g ω ∈ filt) := by
      intro ω; simp only [φ, g, filt, Finset.mem_filter, Finset.mem_univ, true_and]
    -- Rewrite LHS filter to use g
    have hLHS_eq : Finset.univ.filter (fun ω : CoinTape n => φ ω ∈ S) =
        Finset.univ.filter (fun ω => g ω ∈ filt) := by
      ext ω; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hphi_g ω
    rw [show (Finset.univ.filter (fun ω : CoinTape n => φ ω ∈ S)).card =
        (Finset.univ.filter (fun ω => g ω ∈ filt)).card from congrArg _ hLHS_eq]
    -- Fiberwise: |{ω | g ω ∈ filt}| = ∑ j ∈ filt, |fiber(j)|
    rw [← Finset.sum_card_fiberwise_eq_card_filter]
    -- Total fibers = N
    have htotal : ∑ j : Fin k,
        (Finset.univ.filter (fun ω : CoinTape n => g ω = j)).card = N := by
      have h := (Finset.card_eq_sum_card_fiberwise
        (f := g) (s := Finset.univ) (t := Finset.univ)
        (fun ω _ => Finset.mem_coe.mpr (Finset.mem_univ _))).symm
      rwa [Finset.card_univ] at h
    -- Split total: ∑ filt + ∑ filtC = N
    have htotal_split :
        ∑ j ∈ filt, (Finset.univ.filter (fun ω : CoinTape n => g ω = j)).card +
        ∑ j ∈ filtC, (Finset.univ.filter (fun ω : CoinTape n => g ω = j)).card = N := by
      rw [← Finset.sum_union hdisj, hunion]; exact htotal
    -- Weight splits: filt.sum w + filtC.sum w = Σ w
    have hcomp_ge : filt.sum w + filtC.sum w = ∑ j : Fin k, w j := by
      rw [← Finset.sum_union hdisj, hunion]
    -- filtC fibers ≥ filtC weight (each fiber ≥ w)
    have hfiltC_ge : filtC.sum w ≤
        ∑ j ∈ filtC, (Finset.univ.filter (fun ω : CoinTape n => g ω = j)).card := by
      apply Finset.sum_le_sum; intro j _; exact hfib_ge j
    -- Conclude
    omega
  -- Volume on CoinTape is counting measure / N
  have hvol_coinTape : ∀ (T : Set (CoinTape n)),
      (volume T).toReal =
      (Finset.univ.filter (fun ω : CoinTape n => ω ∈ T)).card / N := by
    intro T
    -- volume on CoinTape n is uniformOn Set.univ
    change (ProbabilityTheory.uniformOn Set.univ T).toReal = _
    rw [ProbabilityTheory.uniformOn_univ]
    rw [ENNReal.toReal_div]
    congr 1
    -- Measure.count T → filter card
    rw [Measure.count_apply MeasurableSet.of_discrete,
      Set.encard_eq_coe_toFinset_card T]
    simp only [ENat.toENNReal_coe, ENNReal.toReal_natCast]
    congr 1; congr 1; ext x; simp [Set.mem_toFinset]
  -- Volume on Ω decomposes over singletons
  have hvol_sum : ∀ (S : Set Ω),
      (volume S).toReal =
      ∑ j ∈ Finset.univ.filter (fun j : Fin k => e.symm j ∈ S),
        (volume ({e.symm j} : Set Ω)).toReal := by
    intro S
    -- S = ⋃ j ∈ filter, {e.symm j}
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
  -- Now combine everything
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
          -- sum of weights ≤ vol(S) * N, and deficit ≤ k
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
          -- N - Σ w (real subtraction) ≤ k, since Σ w ≤ N
          have hdef_real : (N : ℝ) - ∑ j : Fin k, (w j : ℝ) ≤ k := by
            rw [← Nat.cast_sum, ← Nat.cast_sub hsum_le]
            exact_mod_cast hdeficit
          -- Normalize casts and conclude
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

/-- The uniform distribution on a finite type can be approximated
by coin flips: for any `δ > 0`, there exist `nX`, `nY` and maps
`φ_X`, `φ_Y` such that for any set `S ⊆ Ω_X × Ω_Y`, the
pushforward measure of `S` under `(φ_X, φ_Y)` exceeds the true
measure by at most `δ`. -/
private theorem product_coin_approx
    {Ω_X Ω_Y : Type*} [Finite Ω_X] [Finite Ω_Y]
    [MeasureSpace Ω_X] [DiscreteMeasurableSpace Ω_X]
    [MeasureSpace Ω_Y] [DiscreteMeasurableSpace Ω_Y]
    [IsProbabilityMeasure (volume : Measure Ω_X)]
    [IsProbabilityMeasure (volume : Measure Ω_Y)]
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (nX nY : ℕ) (φ_X : CoinTape nX → Ω_X)
      (φ_Y : CoinTape nY → Ω_Y),
      ∀ (S : Set (Ω_X × Ω_Y)),
        (volume (Prod.map φ_X φ_Y ⁻¹' S :
          Set (CoinTape nX × CoinTape nY))).toReal ≤
        (volume S).toReal + δ := by
  haveI : Fintype Ω_X := Fintype.ofFinite Ω_X
  haveI : Fintype Ω_Y := Fintype.ofFinite Ω_Y
  -- Apply single_coin_approx to each coordinate with δ/2
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  obtain ⟨nX, φ_X, hX⟩ := @single_coin_approx Ω_X _ _ _ _ (δ / 2) hδ2
  obtain ⟨nY, φ_Y, hY⟩ := @single_coin_approx Ω_Y _ _ _ _ (δ / 2) hδ2
  refine ⟨nX, nY, φ_X, φ_Y, fun S => ?_⟩
  -- Strategy: decompose product measures as sums over elements,
  -- then use hX and hY to bound the difference.
  -- Define slice: S_a = {b | (a,b) ∈ S}
  set S_a : Ω_X → Set Ω_Y := fun a => Prod.mk a ⁻¹' S with hS_a_def
  -- Define real-valued "weight" functions for each element
  set pX : Ω_X → ℝ := fun a =>
    (volume (φ_X ⁻¹' {a} : Set (CoinTape nX))).toReal with hpX_def
  set qX : Ω_X → ℝ := fun a =>
    (volume ({a} : Set Ω_X)).toReal with hqX_def
  set pY : Ω_Y → ℝ := fun b =>
    (volume (φ_Y ⁻¹' {b} : Set (CoinTape nY))).toReal with hpY_def
  set qY : Ω_Y → ℝ := fun b =>
    (volume ({b} : Set Ω_Y)).toReal with hqY_def
  -- All weights are nonneg
  have hpX_nn : ∀ a, 0 ≤ pX a := fun a => ENNReal.toReal_nonneg
  have hqX_nn : ∀ a, 0 ≤ qX a := fun a => ENNReal.toReal_nonneg
  have hpY_nn : ∀ b, 0 ≤ pY b := fun b => ENNReal.toReal_nonneg
  have hqY_nn : ∀ b, 0 ≤ qY b := fun b => ENNReal.toReal_nonneg
  -- Decompose LHS: vol_{CX×CY}(preimage) = Σ_a pX(a) * vol_CY(φ_Y⁻¹(S_a))
  -- Write preimage as disjoint union of rectangles indexed by Ω_X
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
  -- Decompose RHS: vol_{X×Y}(S) = Σ_a qX(a) * vol_Y(S_a)
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
  -- Bound using hY: replace vol_CY(φ_Y⁻¹(S_a)) with vol_Y(S_a) + δ/2
  have hstep1 : ∑ a : Ω_X, pX a *
      (volume (φ_Y ⁻¹' S_a a : Set (CoinTape nY))).toReal ≤
      ∑ a : Ω_X, pX a * ((volume (S_a a)).toReal + δ / 2) := by
    apply Finset.sum_le_sum; intro a _
    exact mul_le_mul_of_nonneg_left (hY (S_a a)) (hpX_nn a)
  -- Expand: Σ pX * (g + δ/2) = Σ pX * g + δ/2
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
  -- Helper: vol(φ_X⁻¹(T)) = Σ_{a∈T} pX(a)
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
  -- Helper: vol(T) = Σ_{a∈T} qX(a)
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
  -- Bound using hX: Σ pX(a) * g(a) ≤ Σ qX(a) * g(a) + δ/2
  -- via A⁺/A⁻ splitting trick
  have hstep2 : ∑ a : Ω_X, pX a * (volume (S_a a)).toReal ≤
      ∑ a : Ω_X, qX a * (volume (S_a a)).toReal + δ / 2 := by
    set g : Ω_X → ℝ := fun a => (volume (S_a a)).toReal with hg_def
    have hg_nn : ∀ a, 0 ≤ g a := fun a => ENNReal.toReal_nonneg
    have hg_le1 : ∀ a, g a ≤ 1 := by
      intro a
      have h1 : volume (S_a a) ≤ volume (Set.univ : Set Ω_Y) :=
        measure_mono (Set.subset_univ _)
      rw [measure_univ] at h1
      -- h1 : volume (S_a a) ≤ 1
      calc g a = (volume (S_a a)).toReal := rfl
        _ ≤ (1 : ENNReal).toReal :=
            ENNReal.toReal_mono (by norm_num) h1
        _ = 1 := by norm_num
    -- Reduce to bounding ∑ (pX - qX) * g ≤ δ/2
    suffices h_key : ∑ a : Ω_X, (pX a - qX a) * g a ≤ δ / 2 by
      have h_diff : ∑ a : Ω_X, pX a * g a - ∑ a : Ω_X, qX a * g a =
          ∑ a : Ω_X, (pX a - qX a) * g a := by
        rw [← Finset.sum_sub_distrib]; congr 1; ext a; ring
      linarith [h_diff]
    -- Split into A⁺ = {a | qX a < pX a} and complement
    set Apos := Finset.univ.filter (fun a : Ω_X => qX a < pX a)
    rw [show ∑ a : Ω_X, (pX a - qX a) * g a =
        ∑ a ∈ Apos, (pX a - qX a) * g a +
        ∑ a ∈ Finset.univ.filter (fun a => ¬(qX a < pX a)),
          (pX a - qX a) * g a from
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm]
    -- Complement: each term ≤ 0 (pX - qX ≤ 0 and g ≥ 0)
    have h_neg : ∑ a ∈ Finset.univ.filter (fun a => ¬(qX a < pX a)),
        (pX a - qX a) * g a ≤ 0 := by
      apply Finset.sum_nonpos; intro a ha
      exact mul_nonpos_of_nonpos_of_nonneg
        (by linarith [(Finset.mem_filter.mp ha).2]) (hg_nn a)
    -- Apos: (pX - qX) ≥ 0 and g ≤ 1, so (pX-qX)*g ≤ (pX-qX)
    have h_pos : ∑ a ∈ Apos, (pX a - qX a) * g a ≤
        ∑ a ∈ Apos, (pX a - qX a) := by
      apply Finset.sum_le_sum; intro a ha
      exact mul_le_of_le_one_right
        (by linarith [(Finset.mem_filter.mp ha).2]) (hg_le1 a)
    -- From hX: ∑ Apos (pX - qX) ≤ δ/2
    have h_hX : ∑ a ∈ Apos, (pX a - qX a) ≤ δ / 2 := by
      have hX_Apos := hX (↑Apos : Set Ω_X)
      rw [hpX_finset Apos, hqX_finset Apos] at hX_Apos
      have h_eq : ∑ a ∈ Apos, (pX a - qX a) =
          ∑ a ∈ Apos, pX a - ∑ a ∈ Apos, qX a := by
        rw [← Finset.sum_sub_distrib]
      linarith [h_eq]
    linarith
  -- Combine all bounds
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

namespace PrivateCoin.GeneralFiniteMessage.Protocol

variable {Ω_X Ω_Y X Y α : Type*} [Fintype Ω_X] [Fintype Ω_Y]

/-- If a general finite-message protocol `ε`-satisfies `Q` under
the uniform measure, then for any `ε' > ε` there exists a
coin-flip finite-message protocol that `ε'`-satisfies `Q` with
the same complexity. -/
theorem approx_satisfies_finiteMessage
    [MeasureSpace Ω_X] [DiscreteMeasurableSpace Ω_X]
    [MeasureSpace Ω_Y] [DiscreteMeasurableSpace Ω_Y]
    [IsProbabilityMeasure (volume : Measure Ω_X)]
    [IsProbabilityMeasure (volume : Measure Ω_Y)]
    (p : Protocol Ω_X Ω_Y X Y α) (Q : X → Y → α → Prop)
    (ε ε' : ℝ) (hε : ε < ε')
    (hp : p.approx_satisfies Q ε) :
    ∃ (nX nY : ℕ)
      (q : PrivateCoin.FiniteMessage.Protocol nX nY X Y α),
      q.approx_satisfies Q ε' ∧
      q.complexity = p.complexity := by
  -- Pick δ = ε' - ε and get coin approximations φ_X, φ_Y
  have hδ : 0 < ε' - ε := sub_pos.mpr hε
  obtain ⟨nX, nY, φ_X, φ_Y, happrox⟩ :=
    Internal.product_coin_approx (Ω_X := Ω_X) (Ω_Y := Ω_Y) (ε' - ε) hδ
  -- Construct the finite-message protocol by pulling back randomness
  refine ⟨nX, nY, p.toFiniteMessage φ_X φ_Y, ?_, ?_⟩
  · -- approx_satisfies: error ≤ ε + δ = ε'
    intro x y
    -- Rewrite the run using toFiniteMessage_run
    -- The error set under the new protocol is the preimage of the
    -- original error set under (φ_X, φ_Y)
    let S := {ω : Ω_X × Ω_Y | ¬Q x y (p.run x y ω.1 ω.2)}
    -- Rewrite error set using toFiniteMessage_run
    have hset : {ω : CoinTape nX × CoinTape nY |
        ¬Q x y ((p.toFiniteMessage φ_X φ_Y).run x y ω.1 ω.2)} =
        Prod.map φ_X φ_Y ⁻¹' S := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage,
        Prod.map, S, toFiniteMessage_run]
    rw [hset]
    -- Apply the approximation bound and the original error bound
    calc (volume (Prod.map φ_X φ_Y ⁻¹' S :
            Set (CoinTape nX × CoinTape nY))).toReal
        ≤ (volume S).toReal + (ε' - ε) := happrox S
      _ ≤ ε + (ε' - ε) := by linarith [hp x y]
      _ = ε' := by ring
  · exact toFiniteMessage_complexity φ_X φ_Y p

end PrivateCoin.GeneralFiniteMessage.Protocol

end CommunicationComplexity
