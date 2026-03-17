import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Measure.Prod

namespace CommunicationComplexity

abbrev CoinTape (n : ℕ) := Fin n → Bool

open MeasureTheory ProbabilityTheory

/-- The uniform probability measure on `CoinTape n`. Every outcome
of `n` independent fair coin flips is equally likely. -/
noncomputable instance coinTapeMeasure (n : ℕ) : MeasureSpace (CoinTape n) where
  volume := uniformOn Set.univ

instance coinTapeIsProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (volume : Measure (CoinTape n)) := by
  change IsProbabilityMeasure (uniformOn Set.univ)
  infer_instance

namespace PrivateCoin

/-- A randomized two-party communication protocol where each player has access
to private coin flips. Alice gets `nX` independent fair coin flips
(`CoinTape nX`) and Bob gets `nY` (`CoinTape nY`).
At each step, a player sends a bit depending on their input and coins. -/
inductive Protocol (nX nY : ℕ) (X Y α : Type*) where
  | output (a : α) : Protocol nX nY X Y α
  | alice
      (f : X → CoinTape nX → Bool)
      (P : Bool → Protocol nX nY X Y α) :
      Protocol nX nY X Y α
  | bob
      (f : Y → CoinTape nY → Bool)
      (P : Bool → Protocol nX nY X Y α) :
      Protocol nX nY X Y α

namespace Protocol

variable {nX nY : ℕ} {X Y α : Type*}

/-- Executes the randomized protocol on inputs `x`, `y` with
coin flips `ω_x`, `ω_y`. -/
def run (p : Protocol nX nY X Y α) (x : X) (y : Y)
    (ω_x : CoinTape nX) (ω_y : CoinTape nY) : α :=
  match p with
  | .output a => a
  | .alice f P => (P (f x ω_x)).run x y ω_x ω_y
  | .bob f P => (P (f y ω_y)).run x y ω_x ω_y

def complexity : Protocol nX nY X Y α → ℕ
  | .output _ => 0
  | .alice _ P => 1 + max (P false).complexity (P true).complexity
  | .bob _ P => 1 + max (P false).complexity (P true).complexity

/-- Swaps the roles of Alice and Bob, producing a protocol on
`Y × X` from one on `X × Y`. The coin flip counts are also swapped. -/
def swap : Protocol nX nY X Y α → Protocol nY nX Y X α
  | .output a => .output a
  | .alice f P => .bob f (fun b => (P b).swap)
  | .bob f P => .alice f (fun b => (P b).swap)

@[simp]
theorem swap_run (p : Protocol nX nY X Y α) (x : X) (y : Y)
    (ω_x : CoinTape nX) (ω_y : CoinTape nY) :
    p.swap.run y x ω_y ω_x = p.run x y ω_x ω_y := by
  induction p with
  | output a => simp [swap, run]
  | alice f P ih => simp [swap, run, ih]
  | bob f P ih => simp [swap, run, ih]

@[simp]
theorem swap_complexity (p : Protocol nX nY X Y α) :
    p.swap.complexity = p.complexity := by
  induction p with
  | output a => simp [swap, complexity]
  | alice f P ih => simp [swap, complexity, ih]
  | bob f P ih => simp [swap, complexity, ih]

/-- A randomized protocol `ε`-satisfies a predicate `Q` if for every
input `(x, y)`, the probability that `Q x y (p.run ...)` fails
is at most `ε`. -/
def approx_satisfies
    (p : Protocol nX nY X Y α) (Q : X → Y → α → Prop)
    (ε : ℝ) : Prop :=
  ∀ x y,
    (volume {ω : CoinTape nX × CoinTape nY |
      ¬Q x y (p.run x y ω.1 ω.2)}).toReal ≤ ε

open Classical in
/-- A randomized protocol `ε`-computes a function `f` if for every
input `(x, y)`, the probability (under the uniform coin-flip measure)
of producing an incorrect answer is at most `ε`. -/
def approx_computes
    (p : Protocol nX nY X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y,
    (volume {ω : CoinTape nX × CoinTape nY |
      p.run x y ω.1 ω.2 ≠ f x y}).toReal ≤ ε

open Classical in
theorem approx_computes_eq_approx_satisfies
    (p : Protocol nX nY X Y α) (f : X → Y → α) (ε : ℝ) :
    p.approx_computes f ε =
      p.approx_satisfies (fun x y a => a = f x y) ε := by
  simp only [approx_computes, approx_satisfies, ne_eq]

end Protocol

end PrivateCoin

end CommunicationComplexity
