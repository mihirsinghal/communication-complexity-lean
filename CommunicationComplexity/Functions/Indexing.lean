import CommunicationComplexity.Basic
import CommunicationComplexity.Deterministic.Rectangle
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
  refine ⟨trivialProtocol n, (by ext x i; rfl), ?_⟩
  · simp [trivialProtocol, OneWay.Protocol.cost,
      Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Nat.one_lt_ofNat, Nat.clog_pow]

/-- Deterministic upper bound for indexing induced by the one-way protocol. -/
theorem communicationComplexity_le :
    Deterministic.communicationComplexity (indexing n) ≤ (n : ℕ) + 1 := by
  exact OneWay.deterministic_communicationComplexity_le_of_oneWay_le_bool
    (f := indexing n) (n := n) (oneWayCommunicationComplexity_le n)

theorem le_oneWayCommunicationComplexity : n ≤ OneWay.communicationComplexity (indexing n) := by
  rw [OneWay.le_communicationComplexity_iff]
  intro p hp_comp
  have hinj : Function.Injective p.send := by
    intro x y heq
    ext i
    have hx := congrFun (congrFun hp_comp x) i
    have hy := congrFun (congrFun hp_comp y) i
    have hm : p.decode (p.send x) i = p.decode (p.send y) i := by
      simpa using congrArg (fun m => p.decode m i) heq
    simpa [OneWay.Protocol.Computes, OneWay.Protocol.run, indexing] using hx.symm.trans (hm.trans hy)
  have hcard : Fintype.card (Fin n → Bool) ≤ Fintype.card p.Message := by
    exact Fintype.card_le_of_injective p.send hinj
  have hpow_dom : 2 ^ (n : ℕ) ≤ Fintype.card p.Message := by
    simpa [Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using hcard
  have hcost : Fintype.card p.Message ≤ 2 ^ p.cost := by
    apply Nat.le_pow_clog; linarith
  by_contra!
  have h_bad : 2 ^ p.cost < 2 ^ (n : ℕ) := by
    refine Nat.pow_lt_pow_of_lt (by linarith) this
  omega

theorem oneWayCommunicationComplexity_eq :
    OneWay.communicationComplexity (indexing n) = (n : ℕ) := by
  exact le_antisymm (oneWayCommunicationComplexity_le n) (le_oneWayCommunicationComplexity n)

end Functions.Indexing

end CommunicationComplexity
