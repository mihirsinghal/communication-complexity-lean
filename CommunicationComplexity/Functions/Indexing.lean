import CommunicationComplexity.Deterministic.OneWay
import CommunicationComplexity.Deterministic.UpperBounds

namespace CommunicationComplexity

namespace Functions.Indexing

open Deterministic

variable (n : ℕ+)

/-- The indexing function: Bob outputs Alice's `i`-th bit. -/
def indexing (x : Fin n → Bool) (i : Fin n) : Bool :=
  x i

/-- The trivial one-way protocol for indexing: Alice sends her full string. -/
def trivialProtocol : OneWay.Protocol (Fin n → Bool) (Fin n) Bool where
  Message := Fin n → Bool
  send := id
  decode := fun x i => x i

/-- One-way upper bound for indexing: Alice can send all `n` bits. -/
theorem oneWayCommunicationComplexity_le :
    OneWay.communicationComplexity (indexing n) ≤ (n : ℕ) := by
  rw [OneWay.communicationComplexity_le_iff]
  refine ⟨trivialProtocol n, ?_, ?_⟩
  · ext x i
    rfl
  · simp [trivialProtocol, OneWay.Protocol.cost,
      Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Nat.one_lt_ofNat, Nat.clog_pow]

/-- Deterministic upper bound for indexing induced by the one-way protocol. -/
theorem communicationComplexity_le :
    Deterministic.communicationComplexity (indexing n) ≤ (n : ℕ) + 1 := by
  exact OneWay.deterministic_communicationComplexity_le_of_oneWay_le_bool
    (f := indexing n) (n := n) (oneWayCommunicationComplexity_le n)

end Functions.Indexing

end CommunicationComplexity
