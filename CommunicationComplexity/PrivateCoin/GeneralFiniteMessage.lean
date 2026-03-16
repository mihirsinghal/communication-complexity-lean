import CommunicationComplexity.PrivateCoin.Basic
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

/-- The preimage of any set under the protocol's output is measurable
in the product probability space. Since `Ω_X` and `Ω_Y` are finite,
the product `Ω_X × Ω_Y` has discrete measurable space, so every
set is measurable. -/
theorem measurable_preimage_run
    [MeasurableSpace Ω_X] [DiscreteMeasurableSpace Ω_X]
    [MeasurableSpace Ω_Y] [DiscreteMeasurableSpace Ω_Y]
    (p : Protocol Ω_X Ω_Y X Y α) (x : X) (y : Y) (s : Set α) :
    MeasurableSet ((fun (ω : Ω_X × Ω_Y) ↦ p.run x y ω.1 ω.2) ⁻¹' s) :=
  MeasurableSet.of_discrete

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

end PrivateCoin.GeneralFiniteMessage.Protocol

end CommunicationComplexity
