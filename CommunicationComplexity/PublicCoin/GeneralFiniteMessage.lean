import CommunicationComplexity.PublicCoin.Basic
import CommunicationComplexity.PublicCoin.FiniteMessage
import CommunicationComplexity.PrivateCoin.GeneralFiniteMessage
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open MeasureTheory

namespace CommunicationComplexity

/-- A public-coin two-party communication protocol where at each step,
a player sends an element of an arbitrary finite type `β`.
This version uses an arbitrary finite probability space `Ω` shared
by both players. Sending a `β`-valued message costs `⌈log₂ |β|⌉` bits.

Since `Ω` is finite, all functions out of it are automatically
measurable, so no measurability hypotheses are needed. -/
inductive PublicCoin.GeneralFiniteMessage.Protocol
    (Ω : Type*) [Fintype Ω]
    (X Y α : Type*) where
  | output (a : α) :
      PublicCoin.GeneralFiniteMessage.Protocol Ω X Y α
  | alice {β : Type} [Fintype β] [Nonempty β]
      (f : X → Ω → β)
      (P : β → PublicCoin.GeneralFiniteMessage.Protocol Ω X Y α) :
      PublicCoin.GeneralFiniteMessage.Protocol Ω X Y α
  | bob {β : Type} [Fintype β] [Nonempty β]
      (f : Y → Ω → β)
      (P : β → PublicCoin.GeneralFiniteMessage.Protocol Ω X Y α) :
      PublicCoin.GeneralFiniteMessage.Protocol Ω X Y α

namespace PublicCoin.GeneralFiniteMessage.Protocol

variable {Ω X Y α : Type*} [Fintype Ω]

/-- Executes the public-coin generalized protocol on inputs `x`, `y`
with shared randomness `ω`. -/
def run (p : Protocol Ω X Y α)
    (x : X) (y : Y) (ω : Ω) : α :=
  match p with
  | output a => a
  | alice f P => (P (f x ω)).run x y ω
  | bob f P => (P (f y ω)).run x y ω

/-- The communication complexity of a public-coin generalized protocol.
Sending a `β`-valued message costs `⌈log₂ |β|⌉` bits. -/
def complexity : Protocol Ω X Y α → ℕ
  | output _ => 0
  | alice (β := β) _ P =>
      Nat.clog 2 (Fintype.card β) +
        Finset.univ.sup (fun i => (P i).complexity)
  | bob (β := β) _ P =>
      Nat.clog 2 (Fintype.card β) +
        Finset.univ.sup (fun i => (P i).complexity)

/-- Swaps the roles of Alice and Bob. The shared randomness
is unchanged. -/
def swap : Protocol Ω X Y α → Protocol Ω Y X α
  | .output a => .output a
  | alice f P =>
      bob f (fun b => (P b).swap)
  | bob f P =>
      alice f (fun b => (P b).swap)

@[simp]
theorem swap_run (p : Protocol Ω X Y α)
    (x : X) (y : Y) (ω : Ω) :
    p.swap.run y x ω = p.run x y ω := by
  induction p with
  | output a => simp [swap, run]
  | alice f P ih => simp only [swap, run]; exact ih _
  | bob f P ih => simp only [swap, run]; exact ih _

@[simp]
theorem swap_complexity (p : Protocol Ω X Y α) :
    p.swap.complexity = p.complexity := by
  induction p with
  | output a => simp [swap, complexity]
  | alice f P ih => simp only [swap, complexity, ih]
  | bob f P ih => simp only [swap, complexity, ih]

/-- Embed a coin-flip public-coin protocol into a generalized
public-coin protocol over `CoinTape` (with `β = Bool`
at each step). -/
def ofProtocol {n : ℕ} :
    PublicCoin.Protocol n X Y α →
      Protocol (CoinTape n) X Y α
  | PublicCoin.Protocol.output a => output a
  | PublicCoin.Protocol.alice f P =>
      alice f (fun b => ofProtocol (P b))
  | PublicCoin.Protocol.bob f P =>
      bob f (fun b => ofProtocol (P b))

theorem ofProtocol_run {n : ℕ}
    (p : PublicCoin.Protocol n X Y α)
    (x : X) (y : Y) (ω : CoinTape n) :
    (ofProtocol p).run x y ω =
      p.run x y ω := by
  induction p with
  | output a =>
    simp [ofProtocol, run, PublicCoin.Protocol.run]
  | alice f P ih =>
    simp [ofProtocol, run, PublicCoin.Protocol.run, ih]
  | bob f P ih =>
    simp [ofProtocol, run, PublicCoin.Protocol.run, ih]

theorem ofProtocol_complexity {n : ℕ}
    (p : PublicCoin.Protocol n X Y α) :
    (ofProtocol p).complexity = p.complexity := by
  induction p with
  | output a =>
    simp [ofProtocol, complexity,
      PublicCoin.Protocol.complexity]
  | alice f P ih =>
    simp only [ofProtocol, complexity,
      PublicCoin.Protocol.complexity, ih]
    have : Nat.clog 2 (Fintype.card Bool) = 1 := by decide
    rw [this]
    have : (Finset.univ : Finset Bool) = {false, true} := by
      ext b; simp
    simp [this]
  | bob f P ih =>
    simp only [ofProtocol, complexity,
      PublicCoin.Protocol.complexity, ih]
    have : Nat.clog 2 (Fintype.card Bool) = 1 := by decide
    rw [this]
    have : (Finset.univ : Finset Bool) = {false, true} := by
      ext b; simp
    simp [this]

/-- Every coin-flip public-coin protocol can be viewed as a generalized
public-coin protocol with the same run behavior and complexity. -/
theorem ofProtocol_equiv {n : ℕ}
    (p : PublicCoin.Protocol n X Y α) :
    ∃ (P : Protocol (CoinTape n) X Y α),
      P.run = p.run ∧ P.complexity = p.complexity :=
  ⟨ofProtocol p,
   funext₂ fun x y => funext fun ω =>
     ofProtocol_run p x y ω,
   ofProtocol_complexity p⟩

/-- A general public-coin finite-message protocol `ε`-satisfies a
predicate `Q` if for every input `(x, y)`, the probability that
`Q x y (p.run ...)` fails is at most `ε`. -/
def ApproxSatisfies
    [MeasureSpace Ω]
    (p : Protocol Ω X Y α) (Q : X → Y → α → Prop)
    (ε : ℝ) : Prop :=
  ∀ x y,
    (volume {ω : Ω | ¬Q x y (p.run x y ω)}).toReal ≤ ε

open Classical in
/-- A general public-coin finite-message protocol `ε`-computes a
function `f` if for every input `(x, y)`, the probability of
producing an incorrect answer is at most `ε`. -/
def ApproxComputes
    [MeasureSpace Ω]
    (p : Protocol Ω X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y,
    (volume {ω : Ω | p.run x y ω ≠ f x y}).toReal ≤ ε

open Classical in
theorem ApproxComputes_eq_ApproxSatisfies
    [MeasureSpace Ω]
    (p : Protocol Ω X Y α) (f : X → Y → α) (ε : ℝ) :
    p.ApproxComputes f ε =
      p.ApproxSatisfies (fun x y a => a = f x y) ε := by
  simp only [ApproxComputes, ApproxSatisfies, ne_eq]


/-- Pull back the randomness of a general public-coin finite-message
protocol through a map `φ`, producing a finite-message protocol
over coin tapes. -/
def toFiniteMessage {n : ℕ}
    (φ : CoinTape n → Ω) :
    Protocol Ω X Y α →
      PublicCoin.FiniteMessage.Protocol n X Y α
  | .output a => .output a
  | alice f P =>
      PublicCoin.FiniteMessage.Protocol.alice
        (fun x ω => f x (φ ω))
        (fun b => (P b).toFiniteMessage φ)
  | bob f P =>
      PublicCoin.FiniteMessage.Protocol.bob
        (fun y ω => f y (φ ω))
        (fun b => (P b).toFiniteMessage φ)

theorem toFiniteMessage_run {n : ℕ}
    (φ : CoinTape n → Ω)
    (p : Protocol Ω X Y α)
    (x : X) (y : Y) (ω : CoinTape n) :
    (p.toFiniteMessage φ).run x y ω =
      p.run x y (φ ω) := by
  induction p with
  | output a =>
    simp [toFiniteMessage, run,
      PublicCoin.FiniteMessage.Protocol.run]
  | alice f P ih =>
    simp only [toFiniteMessage,
      PublicCoin.FiniteMessage.Protocol.run, run]
    exact ih _
  | bob f P ih =>
    simp only [toFiniteMessage,
      PublicCoin.FiniteMessage.Protocol.run, run]
    exact ih _

theorem toFiniteMessage_complexity {n : ℕ}
    (φ : CoinTape n → Ω)
    (p : Protocol Ω X Y α) :
    (p.toFiniteMessage φ).complexity = p.complexity := by
  induction p with
  | output a =>
    simp [toFiniteMessage, complexity,
      PublicCoin.FiniteMessage.Protocol.complexity]
  | alice f P ih =>
    simp only [toFiniteMessage,
      PublicCoin.FiniteMessage.Protocol.complexity,
      complexity, ih]
  | bob f P ih =>
    simp only [toFiniteMessage,
      PublicCoin.FiniteMessage.Protocol.complexity,
      complexity, ih]

/-- If a general public-coin finite-message protocol `ε`-satisfies
`Q` under the measure on `Ω`, then for any `ε' > ε` there exists a
coin-flip finite-message protocol that `ε'`-satisfies `Q` with the
same complexity. -/
theorem ApproxSatisfies_finiteMessage
    [MeasureSpace Ω] [DiscreteMeasurableSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    (p : Protocol Ω X Y α) (Q : X → Y → α → Prop)
    (ε ε' : ℝ) (hε : ε < ε')
    (hp : p.ApproxSatisfies Q ε) :
    ∃ (n : ℕ)
      (q : PublicCoin.FiniteMessage.Protocol n X Y α),
      q.ApproxSatisfies Q ε' ∧
      q.complexity = p.complexity := by
  -- Pick δ = ε' - ε and get coin approximation φ
  have hδ : 0 < ε' - ε := sub_pos.mpr hε
  obtain ⟨n, φ, happrox⟩ :=
    Internal.single_coin_approx (Ω := Ω) (ε' - ε) hδ
  -- Construct the finite-message protocol by pulling back randomness
  refine ⟨n, p.toFiniteMessage φ, ?_, ?_⟩
  · -- ApproxSatisfies: error ≤ ε + δ = ε'
    intro x y
    -- The error set under the new protocol is the preimage of the
    -- original error set under φ
    let S := {ω : Ω | ¬Q x y (p.run x y ω)}
    -- Rewrite error set using toFiniteMessage_run
    have hset : {ω : CoinTape n |
        ¬Q x y ((p.toFiniteMessage φ).run x y ω)} =
        φ ⁻¹' S := by
      ext ω; simp only [Set.mem_setOf_eq, Set.mem_preimage,
        S, toFiniteMessage_run]
    rw [hset]
    -- Apply the approximation bound and the original error bound
    calc (volume (φ ⁻¹' S : Set (CoinTape n))).toReal
        ≤ (volume S).toReal + (ε' - ε) := happrox S
      _ ≤ ε + (ε' - ε) := by linarith [hp x y]
      _ = ε' := by ring
  · exact toFiniteMessage_complexity φ p

end PublicCoin.GeneralFiniteMessage.Protocol

end CommunicationComplexity
