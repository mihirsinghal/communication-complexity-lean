import CommunicationComplexity.Deterministic.Complexity
import CommunicationComplexity.PrivateCoin.Complexity
import CommunicationComplexity.PublicCoin.Basic

namespace CommunicationComplexity

open MeasureTheory ProbabilityTheory

/-- Convert a deterministic protocol to a randomized protocol
with 0 coin flips. The randomized protocol ignores its (trivial)
randomness and behaves identically to the deterministic one. -/
def Deterministic.Protocol.toPrivateCoin {X Y α}
    (p : Deterministic.Protocol X Y α) :
    PrivateCoin.Protocol 0 0 X Y α :=
  match p with
  | .output val => .output val
  | .alice f P =>
      .alice (fun x _ => f x) (fun b => (P b).toPrivateCoin)
  | .bob f P =>
      .bob (fun y _ => f y) (fun b => (P b).toPrivateCoin)

@[simp] theorem Deterministic.Protocol.toPrivateCoin_run
    {X Y α} (p : Deterministic.Protocol X Y α)
    (x : X) (y : Y)
    (ω_x : CoinTape 0) (ω_y : CoinTape 0) :
    p.toPrivateCoin.run x y ω_x ω_y = p.run x y := by
  induction p <;> simp [Deterministic.Protocol.toPrivateCoin,
    PrivateCoin.Protocol.run, Deterministic.Protocol.run, *]

@[simp] theorem Deterministic.Protocol.toPrivateCoin_complexity
    {X Y α} (p : Deterministic.Protocol X Y α) :
    p.toPrivateCoin.complexity = p.complexity := by
  induction p <;> simp [Deterministic.Protocol.toPrivateCoin,
    PrivateCoin.Protocol.complexity, Deterministic.Protocol.complexity, *]

open Classical in
theorem PrivateCoin.communicationComplexity_le_deterministic
    {X Y α} (f : X → Y → α) (ε : ℝ) (hε : 0 ≤ ε) :
    PrivateCoin.communicationComplexity f ε ≤
      Deterministic.communicationComplexity f := by
  match h : Deterministic.communicationComplexity f with
  | ⊤ => exact le_top
  | (n : ℕ) =>
    obtain ⟨p, hp, hc⟩ :=
      (Deterministic.communicationComplexity_le_iff f n).mp
        (le_of_eq h)
    rw [PrivateCoin.communicationComplexity_le_iff]
    refine ⟨0, 0, p.toPrivateCoin, ?_, ?_⟩
    · -- ApproxComputes: error is 0 since protocol is deterministic
      intro x y
      have hp' : p.run x y = f x y := congr_fun (congr_fun hp x) y
      simp [Deterministic.Protocol.toPrivateCoin_run, hp', hε]
    · rw [Deterministic.Protocol.toPrivateCoin_complexity]
      exact hc

/-- Fix the randomness of a public-coin protocol, producing a
deterministic protocol with the same complexity. -/
def PublicCoin.Protocol.toDeterministic {n : ℕ} {X Y α : Type*}
    (p : PublicCoin.Protocol n X Y α) (ω : CoinTape n) :
    Deterministic.Protocol X Y α :=
  match p with
  | .output a => .output a
  | .alice f P => .alice (fun x => f x ω) (fun b => (P b).toDeterministic ω)
  | .bob f P => .bob (fun y => f y ω) (fun b => (P b).toDeterministic ω)

@[simp] theorem PublicCoin.Protocol.toDeterministic_run
    {n : ℕ} {X Y α : Type*}
    (p : PublicCoin.Protocol n X Y α) (ω : CoinTape n)
    (x : X) (y : Y) :
    (p.toDeterministic ω).run x y = p.run x y ω := by
  induction p <;> simp [PublicCoin.Protocol.toDeterministic,
    Deterministic.Protocol.run, PublicCoin.Protocol.run, *]

@[simp] theorem PublicCoin.Protocol.toDeterministic_complexity
    {n : ℕ} {X Y α : Type*}
    (p : PublicCoin.Protocol n X Y α) (ω : CoinTape n) :
    (p.toDeterministic ω).complexity = p.complexity := by
  induction p <;> simp [PublicCoin.Protocol.toDeterministic,
    Deterministic.Protocol.complexity, PublicCoin.Protocol.complexity, *]

end CommunicationComplexity
