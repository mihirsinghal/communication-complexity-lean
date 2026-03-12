import Mathlib

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

end DetProtocol
