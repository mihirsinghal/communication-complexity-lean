import CommunicationComplexity.PrivateCoin.Basic
import Mathlib.Data.Real.Basic

namespace CommunicationComplexity

open MeasureTheory ProbabilityTheory

namespace PublicCoin

/-- A randomized two-party communication protocol where both players
have access to the same public coin flips. Both Alice and Bob see
the shared `CoinTape n`. At each step, a player sends a bit
depending on their input and the shared coins. -/
inductive Protocol (n : ℕ) (X Y α : Type*) where
  | output (a : α) : Protocol n X Y α
  | alice
      (f : X → CoinTape n → Bool)
      (P : Bool → Protocol n X Y α) :
      Protocol n X Y α
  | bob
      (f : Y → CoinTape n → Bool)
      (P : Bool → Protocol n X Y α) :
      Protocol n X Y α

namespace Protocol

variable {n : ℕ} {X Y α : Type*}

/-- Executes the public-coin protocol on inputs `x`, `y` with
shared coin flips `ω`. -/
def run (p : Protocol n X Y α) (x : X) (y : Y)
    (ω : CoinTape n) : α :=
  match p with
  | .output a => a
  | .alice f P => (P (f x ω)).run x y ω
  | .bob f P => (P (f y ω)).run x y ω

def complexity : Protocol n X Y α → ℕ
  | .output _ => 0
  | .alice _ P => 1 + max (P false).complexity (P true).complexity
  | .bob _ P => 1 + max (P false).complexity (P true).complexity

/-- Swaps the roles of Alice and Bob. The shared randomness is unchanged. -/
def swap : Protocol n X Y α → Protocol n Y X α
  | .output a => .output a
  | .alice f P => .bob f (fun b => (P b).swap)
  | .bob f P => .alice f (fun b => (P b).swap)

@[simp]
theorem swap_run (p : Protocol n X Y α) (x : X) (y : Y)
    (ω : CoinTape n) :
    p.swap.run y x ω = p.run x y ω := by
  induction p with
  | output a => simp [swap, run]
  | alice f P ih => simp [swap, run, ih]
  | bob f P ih => simp [swap, run, ih]

@[simp]
theorem swap_complexity (p : Protocol n X Y α) :
    p.swap.complexity = p.complexity := by
  induction p with
  | output a => simp [swap, complexity]
  | alice f P ih => simp [swap, complexity, ih]
  | bob f P ih => simp [swap, complexity, ih]

open Classical in
/-- A public-coin protocol `ε`-computes a function `f` if for every
input `(x, y)`, the probability (under the uniform coin-flip measure)
of producing an incorrect answer is at most `ε`. -/
def approx_computes
    (p : Protocol n X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y,
    (volume {ω : CoinTape n |
      p.run x y ω ≠ f x y}).toReal ≤ ε

end Protocol

end PublicCoin

end CommunicationComplexity
