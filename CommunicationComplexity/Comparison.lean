import CommunicationComplexity.Deterministic.Complexity
import CommunicationComplexity.PrivateCoin.Complexity

namespace CommunicationComplexity

open MeasureTheory ProbabilityTheory

/-- Convert a deterministic protocol to a randomized protocol
with 0 coin flips. The randomized protocol ignores its (trivial)
randomness and behaves identically to the deterministic one. -/
private def Deterministic.Protocol.toPrivateCoin {X Y α}
    (p : Deterministic.Protocol X Y α) :
    PrivateCoin.Protocol 0 0 X Y α :=
  match p with
  | .output val => .output val
  | .alice f P =>
      .alice (fun x _ => f x) (fun b => (P b).toPrivateCoin)
  | .bob f P =>
      .bob (fun y _ => f y) (fun b => (P b).toPrivateCoin)

private theorem Deterministic.Protocol.toPrivateCoin_run
    {X Y α} (p : Deterministic.Protocol X Y α)
    (x : X) (y : Y)
    (ω_x : CoinTape 0) (ω_y : CoinTape 0) :
    p.toPrivateCoin.run x y ω_x ω_y = p.run x y := by
  induction p with
  | output val =>
    simp [Deterministic.Protocol.toPrivateCoin,
      PrivateCoin.Protocol.run,
      Deterministic.Protocol.run]
  | alice f P ih =>
    simp [Deterministic.Protocol.toPrivateCoin,
      PrivateCoin.Protocol.run,
      Deterministic.Protocol.run, ih]
  | bob f P ih =>
    simp [Deterministic.Protocol.toPrivateCoin,
      PrivateCoin.Protocol.run,
      Deterministic.Protocol.run, ih]

private theorem Deterministic.Protocol.toPrivateCoin_complexity
    {X Y α} (p : Deterministic.Protocol X Y α) :
    p.toPrivateCoin.complexity = p.complexity := by
  induction p with
  | output val =>
    simp [Deterministic.Protocol.toPrivateCoin,
      PrivateCoin.Protocol.complexity,
      Deterministic.Protocol.complexity]
  | alice f P ih =>
    simp [Deterministic.Protocol.toPrivateCoin,
      PrivateCoin.Protocol.complexity,
      Deterministic.Protocol.complexity, ih]
  | bob f P ih =>
    simp [Deterministic.Protocol.toPrivateCoin,
      PrivateCoin.Protocol.complexity,
      Deterministic.Protocol.complexity, ih]

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
    · -- approx_computes: error is 0 since protocol is deterministic
      intro x y
      have hrun : ∀ ω : CoinTape 0 × CoinTape 0,
          p.toPrivateCoin.run x y ω.1 ω.2 = f x y := by
        intro ω
        rw [Deterministic.Protocol.toPrivateCoin_run]
        exact congr_fun (congr_fun hp x) y
      -- The error set is empty since the protocol always returns f x y
      have hempty : {ω : CoinTape 0 × CoinTape 0 |
          p.toPrivateCoin.run x y ω.1 ω.2 ≠ f x y} = ∅ := by
        ext ω; simp [hrun ω]
      simp [hempty, hε]
    · rw [Deterministic.Protocol.toPrivateCoin_complexity]
      exact hc

end CommunicationComplexity
