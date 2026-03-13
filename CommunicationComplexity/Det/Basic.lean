import Mathlib.Tactic.Common

/-- A deterministic two-party communication protocol where Alice holds input `x : X`,
Bob holds input `y : Y`, and the protocol computes a value of type `α`.
At each step, either Alice or Bob sends a single bit based on their input,
and the protocol branches accordingly. -/

inductive DetProtocol (X Y α : Type*) where
  | output (val : α) : DetProtocol X Y α
  | alice (f : X → Bool) (P : Bool → DetProtocol X Y α) : DetProtocol X Y α
  | bob (f : Y → Bool) (P : Bool → DetProtocol X Y α) : DetProtocol X Y α

namespace DetProtocol

variable {X Y α : Type*}

/-- Executes the protocol on inputs `x` and `y`, returning the output value. -/
def run (p : DetProtocol X Y α) (x : X) (y : Y) : α :=
  match p with
  | DetProtocol.output val => val
  | DetProtocol.alice f P => (P (f x)).run x y
  | DetProtocol.bob f P => (P (f y)).run x y

/-- The communication complexity of a protocol, i.e. the worst-case number of bits exchanged. -/
def complexity : DetProtocol X Y α → ℕ
  | DetProtocol.output _ => 0
  | DetProtocol.alice _ P => 1 + max (P false).complexity (P true).complexity
  | DetProtocol.bob _ P => 1 + max (P false).complexity (P true).complexity

/-- Two protocols are equivalent if they produce the same output on all inputs. -/
def equiv (p q : DetProtocol X Y α) : Prop :=
  p.run = q.run

/-- A protocol computes a function `f` if it produces `f x y` on all inputs `(x, y)`. -/
def computes (p : DetProtocol X Y α) (f : X → Y → α) : Prop :=
  p.run = f

/-- Swaps the roles of Alice and Bob, producing a protocol on `Y × X` from one on `X × Y`.
Alice nodes become bob nodes and vice versa. -/
def swap : DetProtocol X Y α → DetProtocol Y X α
  | DetProtocol.output val => DetProtocol.output val
  | DetProtocol.alice f P => DetProtocol.bob f (fun b => (P b).swap)
  | DetProtocol.bob f P => DetProtocol.alice f (fun b => (P b).swap)

@[simp]
theorem swap_run (p : DetProtocol X Y α) (x : X) (y : Y) :
    p.swap.run y x = p.run x y := by
  induction p with
  | output val => simp [swap, run]
  | alice f P ih => simp [swap, run, ih]
  | bob f P ih => simp [swap, run, ih]

@[simp]
theorem swap_complexity (p : DetProtocol X Y α) :
    p.swap.complexity = p.complexity := by
  induction p with
  | output val => simp [swap, complexity]
  | alice f P ih => simp [swap, complexity, ih]
  | bob f P ih => simp [swap, complexity, ih]

/-- An alice protocol on `X × Y` can be converted into a bob protocol on `Y × X`
with the same run behavior (up to argument swap) and complexity.
Useful for reducing the bob case to the alice case in inductive proofs. -/
theorem alice_to_bob (f : X → Bool) (P : Bool → DetProtocol X Y α) :
    ∃ q : DetProtocol Y X α,
      (∀ x y, q.run y x = (alice f P).run x y) ∧
      q.complexity = (alice f P).complexity :=
  ⟨(alice f P).swap, fun x y => swap_run _ x y, swap_complexity _⟩

/-- A bob protocol on `X × Y` can be converted into an alice protocol on `Y × X`
with the same run behavior (up to argument swap) and complexity.
Useful for reducing the alice case to the bob case in inductive proofs. -/
theorem bob_to_alice (f : Y → Bool) (P : Bool → DetProtocol X Y α) :
    ∃ q : DetProtocol Y X α,
      (∀ x y, q.run y x = (bob f P).run x y) ∧
      q.complexity = (bob f P).complexity :=
  ⟨(bob f P).swap, fun x y => swap_run _ x y, swap_complexity _⟩

end DetProtocol
