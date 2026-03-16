import CommunicationComplexity.Deterministic.Basic
import CommunicationComplexity.Deterministic.FiniteMessage
import CommunicationComplexity.PrivateCoin.Basic
import CommunicationComplexity.PrivateCoin.FiniteMessage

namespace CommunicationComplexity

open MeasureTheory ProbabilityTheory

@[simp]
private theorem WithTop.iInf_le_coe_iff {ι : Sort*} {f : ι → WithTop ℕ} {n : ℕ} :
    iInf f ≤ ↑n ↔ ∃ i, f i ≤ ↑n := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    apply not_lt.mpr h
    have : ∀ i, (↑(n + 1) : WithTop ℕ) ≤ f i := fun i => by
      match f i, hne i with
      | none, _ => exact le_top
      | some m, hi =>
        exact WithTop.coe_le_coe.mpr
          (Nat.succ_le_of_lt (WithTop.coe_lt_coe.mp hi))
    exact lt_of_lt_of_le
      (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n))
      (le_iInf this)
  · rintro ⟨i, hi⟩
    exact (iInf_le f i).trans hi

namespace Deterministic

noncomputable def communicationComplexity
    {X Y α} (f : X → Y → α) : WithTop ℕ :=
  ⨅ (p : Protocol X Y α) (_ : p.computes f),
    (p.complexity : WithTop ℕ)

theorem communicationComplexity_le_iff
    {X Y α} (f : X → Y → α) (n : ℕ) :
    communicationComplexity f ≤ n ↔
      ∃ p : Protocol X Y α,
        p.computes f ∧ p.complexity ≤ n := by
  simp only [communicationComplexity,
    WithTop.iInf_le_coe_iff, Nat.cast_le, exists_prop]

theorem communicationComplexity_le_iff_finiteMessage
    {X Y α} (f : X → Y → α) (n : ℕ) :
    communicationComplexity f ≤ n ↔
      ∃ p : FiniteMessage.Protocol X Y α,
        p.run = f ∧ p.complexity ≤ n := by
  rw [communicationComplexity_le_iff]
  constructor
  · rintro ⟨p, hp, hc⟩
    obtain ⟨P, hP_run, hP_comp⟩ :=
      FiniteMessage.Protocol.ofProtocol_equiv p
    exact ⟨P, hP_run.trans hp, hP_comp ▸ hc⟩
  · rintro ⟨p, hp, hc⟩
    obtain ⟨P, hP_run, hP_comp⟩ :=
      FiniteMessage.Protocol.toProtocol p
    exact ⟨P, hP_run.trans hp, hP_comp ▸ hc⟩

theorem le_communicationComplexity_iff
    {X Y α} (f : X → Y → α) (n : ℕ) :
    (n : WithTop ℕ) ≤ communicationComplexity f ↔
      ∀ p : Protocol X Y α,
        p.computes f → n ≤ p.complexity := by
  simp only [communicationComplexity,
    le_iInf_iff, Nat.cast_le]

end Deterministic

namespace PrivateCoin

/-- The `ε`-error randomized communication complexity of `f`,
defined as the minimum worst-case number of bits exchanged over all
coin-flip randomized protocols that compute `f` with error at most
`ε` on every input. -/
noncomputable def communicationComplexity
    {X Y α} [DecidableEq α]
    (f : X → Y → α) (ε : ℝ) : WithTop ℕ :=
  ⨅ (nX : ℕ) (nY : ℕ)
    (p : Protocol nX nY X Y α)
    (_ : p.approx_computes f ε),
    (p.complexity : WithTop ℕ)

theorem communicationComplexity_le_iff
    {X Y α} [DecidableEq α]
    (f : X → Y → α) (ε : ℝ) (n : ℕ) :
    communicationComplexity f ε ≤ n ↔
      ∃ (nX nY : ℕ) (p : Protocol nX nY X Y α),
        p.approx_computes f ε ∧
        p.complexity ≤ n := by
  unfold communicationComplexity
  simp only [WithTop.iInf_le_coe_iff, Nat.cast_le, exists_prop]

theorem le_communicationComplexity_iff
    {X Y α} [DecidableEq α]
    (f : X → Y → α) (ε : ℝ) (n : ℕ) :
    (n : WithTop ℕ) ≤ communicationComplexity f ε ↔
      ∀ (nX nY : ℕ) (p : Protocol nX nY X Y α),
        p.approx_computes f ε →
        n ≤ p.complexity := by
  unfold communicationComplexity
  simp only [le_iInf_iff, Nat.cast_le]

theorem communicationComplexity_le_iff_finiteMessage
    {X Y α} [DecidableEq α]
    (f : X → Y → α) (ε : ℝ) (n : ℕ) :
    communicationComplexity f ε ≤ n ↔
      ∃ (nX nY : ℕ)
        (p : FiniteMessage.Protocol nX nY X Y α),
        (∀ x y,
          (volume {ω : CoinTape nX × CoinTape nY |
            p.run x y ω.1 ω.2 ≠ f x y}).toReal
            ≤ ε) ∧
        p.complexity ≤ n := by
  rw [communicationComplexity_le_iff]
  constructor
  · rintro ⟨nX, nY, p, hp, hc⟩
    obtain ⟨P, hP_run, hP_comp⟩ :=
      FiniteMessage.Protocol.ofProtocol_equiv p
    refine ⟨nX, nY, P, ?_, hP_comp ▸ hc⟩
    intro x y; simp_rw [hP_run]; exact hp x y
  · rintro ⟨nX, nY, p, hp, hc⟩
    obtain ⟨P, hP_run, hP_comp⟩ :=
      FiniteMessage.Protocol.toProtocol p
    refine ⟨nX, nY, P, ?_, hP_comp ▸ hc⟩
    intro x y; simp_rw [hP_run]; exact hp x y

end PrivateCoin

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

theorem PrivateCoin.communicationComplexity_le_deterministic
    {X Y α} [DecidableEq α]
    (f : X → Y → α) (ε : ℝ) (hε : 0 ≤ ε) :
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
