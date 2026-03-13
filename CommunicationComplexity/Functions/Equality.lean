import CommunicationComplexity.Basic

/-- The equality function on `n`-bit strings. Returns `true` iff the two inputs are equal. -/
def EQ (n : ℕ) (x y : Fin n → Bool) : Bool :=
  decide (x = y)
