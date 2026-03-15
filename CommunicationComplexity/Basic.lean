import CommunicationComplexity.Deterministic.Basic
import CommunicationComplexity.Deterministic.FiniteMessage
import CommunicationComplexity.PrivateCoin.Basic
import CommunicationComplexity.PrivateCoin.FiniteMessage
import Mathlib.MeasureTheory.Measure.Dirac

open MeasureTheory

namespace CommunicationComplexity

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
      | some m, hi => exact WithTop.coe_le_coe.mpr (Nat.succ_le_of_lt (WithTop.coe_lt_coe.mp hi))
    exact lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n)) (le_iInf this)
  · rintro ⟨i, hi⟩
    exact (iInf_le f i).trans hi

namespace Deterministic

/-- The deterministic communication complexity of a function `f : X → Y → α`, defined as the
minimum worst-case number of bits exchanged over all deterministic protocols computing `f`.
Returns `⊤` if no finite protocol computes `f`. -/
noncomputable def communicationComplexity {X Y α} (f : X → Y → α) : WithTop ℕ :=
  ⨅ (p : Protocol X Y α) (_ : p.computes f), (p.complexity : WithTop ℕ)

/-- The deterministic communication complexity of `f` is at most `n` iff there exists a
deterministic protocol computing `f` with complexity at most `n`. -/
theorem communicationComplexity_le_iff {X Y α} (f : X → Y → α) (n : ℕ) :
    communicationComplexity f ≤ n ↔
      ∃ p : Protocol X Y α, p.computes f ∧ p.complexity ≤ n := by
  simp only [communicationComplexity, WithTop.iInf_le_coe_iff, Nat.cast_le,
    exists_prop]

/-- The deterministic communication complexity of `f` is at most `n` iff there exists a
generalized deterministic protocol computing `f` with complexity at most `n`. -/
theorem communicationComplexity_le_iff_finiteMessage {X Y α} (f : X → Y → α) (n : ℕ) :
    communicationComplexity f ≤ n ↔
      ∃ p : FiniteMessage.Protocol X Y α, p.run = f ∧ p.complexity ≤ n := by
  rw [communicationComplexity_le_iff]
  constructor
  · rintro ⟨p, hp, hc⟩
    obtain ⟨P, hP_run, hP_comp⟩ := FiniteMessage.Protocol.ofProtocol_equiv p
    exact ⟨P, hP_run.trans hp, hP_comp ▸ hc⟩
  · rintro ⟨p, hp, hc⟩
    obtain ⟨P, hP_run, hP_comp⟩ := FiniteMessage.Protocol.toProtocol p
    exact ⟨P, hP_run.trans hp, hP_comp ▸ hc⟩

/-- The deterministic communication complexity of `f` is at least `n` iff every deterministic
protocol computing `f` has complexity at least `n`. -/
theorem le_communicationComplexity_iff {X Y α} (f : X → Y → α) (n : ℕ) :
    (n : WithTop ℕ) ≤ communicationComplexity f ↔
      ∀ p : Protocol X Y α, p.computes f → n ≤ p.complexity := by
  simp only [communicationComplexity, le_iInf_iff, Nat.cast_le]

end Deterministic

namespace PrivateCoin

/-- The `ε`-error randomized communication complexity of a function `f : X → Y → α`, defined as
the minimum worst-case number of bits exchanged over all randomized protocols that compute `f`
with error probability at most `ε` on every input. The randomness spaces are required to be finite.
Returns `⊤` if no finite protocol `ε`-computes `f`. -/
noncomputable def communicationComplexity {X Y α} (f : X → Y → α) (ε : ℝ) : WithTop ℕ :=
  ⨅ (Ω_X : Type) (Ω_Y : Type) (_ : Finite Ω_X) (_ : Finite Ω_Y)
    (_ : MeasureSpace Ω_X) (_ : MeasureSpace Ω_Y)
    (_ : IsProbabilityMeasure (volume : Measure Ω_X))
    (_ : IsProbabilityMeasure (volume : Measure Ω_Y))
    (p : Protocol Ω_X Ω_Y X Y α) (_ : p.approx_computes f ε),
    (p.complexity : WithTop ℕ)

/-- The randomized communication complexity of `f` at error `ε` is at most `n` iff there exist
finite probability spaces and a randomized protocol that `ε`-computes `f` with complexity at
most `n`. -/
theorem communicationComplexity_le_iff {X Y α} (f : X → Y → α) (ε : ℝ) (n : ℕ) :
    communicationComplexity f ε ≤ n ↔
      ∃ (Ω_X Ω_Y : Type) (_ : Finite Ω_X) (_ : Finite Ω_Y)
        (_ : MeasureSpace Ω_X) (_ : MeasureSpace Ω_Y)
        (_ : IsProbabilityMeasure (volume : Measure Ω_X))
        (_ : IsProbabilityMeasure (volume : Measure Ω_Y))
        (p : Protocol Ω_X Ω_Y X Y α),
        p.approx_computes f ε ∧ p.complexity ≤ n := by
  simp only [communicationComplexity, WithTop.iInf_le_coe_iff, Nat.cast_le, exists_prop,
    exists_and_left]

/-- Helper: to show rand CC ≤ n, provide a randomized protocol that ε-computes `f`
with complexity ≤ n. Typeclass arguments are inferred automatically. -/
theorem communicationComplexity_le_of_protocol {X Y α} {f : X → Y → α} {ε : ℝ} {n : ℕ}
    {Ω_X Ω_Y : Type} [Finite Ω_X] [Finite Ω_Y]
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    [IsProbabilityMeasure (volume : Measure Ω_X)]
    [IsProbabilityMeasure (volume : Measure Ω_Y)]
    (p : Protocol Ω_X Ω_Y X Y α)
    (hp : p.approx_computes f ε) (hc : p.complexity ≤ n) :
    communicationComplexity f ε ≤ n :=
  (communicationComplexity_le_iff f ε n).mpr
    ⟨Ω_X, Ω_Y, inferInstance, inferInstance, inferInstance, inferInstance,
     inferInstance, inferInstance, p, hp, hc⟩

/-- The randomized communication complexity of `f` at error `ε` is at least `n` iff every
randomized protocol that `ε`-computes `f` (over any finite probability spaces) has complexity
at least `n`. -/
theorem le_communicationComplexity_iff {X Y α} (f : X → Y → α) (ε : ℝ) (n : ℕ) :
    (n : WithTop ℕ) ≤ communicationComplexity f ε ↔
      ∀ (Ω_X Ω_Y : Type) [Finite Ω_X] [Finite Ω_Y]
        [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
        [IsProbabilityMeasure (volume : Measure Ω_X)]
        [IsProbabilityMeasure (volume : Measure Ω_Y)]
        (p : Protocol Ω_X Ω_Y X Y α),
        p.approx_computes f ε → n ≤ p.complexity := by
  unfold communicationComplexity
  simp only [le_iInf_iff, Nat.cast_le]

/-- The randomized communication complexity of `f` at error `ε` is at most `n` iff there exist
finite probability spaces and a generalized randomized protocol that `ε`-computes `f` with
complexity at most `n`. -/
theorem communicationComplexity_le_iff_finiteMessage {X Y α}
    (f : X → Y → α) (ε : ℝ) (n : ℕ) :
    communicationComplexity f ε ≤ n ↔
      ∃ (Ω_X Ω_Y : Type) (_ : Finite Ω_X) (_ : Finite Ω_Y)
        (_ : MeasureSpace Ω_X) (_ : MeasureSpace Ω_Y)
        (_ : IsProbabilityMeasure (volume : Measure Ω_X))
        (_ : IsProbabilityMeasure (volume : Measure Ω_Y))
        (p : FiniteMessage.Protocol Ω_X Ω_Y X Y α),
        (∀ x y, (volume {ω : Ω_X × Ω_Y | p.run x y ω.1 ω.2 ≠ f x y}).toReal ≤ ε) ∧
        p.complexity ≤ n := by
  rw [communicationComplexity_le_iff]
  constructor
  · -- Binary protocol → generalized protocol
    rintro ⟨Ω_X, Ω_Y, hfX, hfY, msX, msY, hpX, hpY, p, hp, hc⟩
    obtain ⟨P, hP_run, hP_comp⟩ :=
      FiniteMessage.Protocol.ofProtocol_equiv p
    refine ⟨Ω_X, Ω_Y, hfX, hfY, msX, msY, hpX, hpY,
      P, ?_, hP_comp ▸ hc⟩
    intro x y; simp_rw [hP_run]; exact hp x y
  · -- Generalized protocol → binary protocol
    rintro ⟨Ω_X, Ω_Y, hfX, hfY, msX, msY, hpX, hpY, p, hp, hc⟩
    obtain ⟨P, hP_run, hP_comp⟩ :=
      FiniteMessage.Protocol.toProtocol p
    refine ⟨Ω_X, Ω_Y, hfX, hfY, msX, msY, hpX, hpY, P, ?_, hP_comp ▸ hc⟩
    intro x y; simp_rw [hP_run]; exact hp x y

/-- Helper: to show rand CC ≤ n, provide a generalized randomized protocol that ε-computes `f`
with complexity ≤ n. Typeclass arguments are inferred automatically. -/
theorem communicationComplexity_le_of_finiteMessage_protocol {X Y α}
    {f : X → Y → α} {ε : ℝ} {n : ℕ}
    {Ω_X Ω_Y : Type} [Finite Ω_X] [Finite Ω_Y]
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    [IsProbabilityMeasure (volume : Measure Ω_X)]
    [IsProbabilityMeasure (volume : Measure Ω_Y)]
    (p : FiniteMessage.Protocol Ω_X Ω_Y X Y α)
    (hp : ∀ x y, (volume {ω : Ω_X × Ω_Y | p.run x y ω.1 ω.2 ≠ f x y}).toReal ≤ ε)
    (hc : p.complexity ≤ n) :
    communicationComplexity f ε ≤ n :=
  (communicationComplexity_le_iff_finiteMessage f ε n).mpr
    ⟨Ω_X, Ω_Y, inferInstance, inferInstance, inferInstance, inferInstance,
     inferInstance, inferInstance, p, hp, hc⟩

end PrivateCoin

/-- Convert a deterministic protocol to a randomized protocol with
trivial (Unit) probability spaces. The randomized protocol ignores
its randomness and behaves identically to the deterministic one. -/
-- Unit with Dirac measure as a probability space, used for embedding det protocols into rand
private noncomputable instance unitMeasureSpace : MeasureSpace Unit := ⟨Measure.dirac ()⟩
private instance unitIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure Unit) :=
  ⟨by simp [unitMeasureSpace, Measure.dirac_apply_of_mem (Set.mem_univ ())]⟩

/-- Convert a deterministic protocol to a randomized protocol over Unit probability spaces. -/
private def Deterministic.Protocol.toPrivateCoin {X Y α}
    (p : Deterministic.Protocol X Y α) : PrivateCoin.Protocol Unit Unit X Y α :=
  match p with
  | .output val => .output val
  | .alice f P =>
      .alice (fun x _ => f x)
        (fun _ => measurable_const) (fun b => (P b).toPrivateCoin)
  | .bob f P =>
      .bob (fun y _ => f y)
        (fun _ => measurable_const) (fun b => (P b).toPrivateCoin)

private theorem Deterministic.Protocol.toPrivateCoin_run {X Y α}
    (p : Deterministic.Protocol X Y α) (x : X) (y : Y)
    (ω_x : Unit) (ω_y : Unit) :
    p.toPrivateCoin.run x y ω_x ω_y = p.run x y := by
  induction p with
  | output val =>
    simp [Deterministic.Protocol.toPrivateCoin, PrivateCoin.Protocol.run,
      Deterministic.Protocol.run]
  | alice f P ih =>
    simp [Deterministic.Protocol.toPrivateCoin, PrivateCoin.Protocol.run,
      Deterministic.Protocol.run, ih]
  | bob f P ih =>
    simp [Deterministic.Protocol.toPrivateCoin, PrivateCoin.Protocol.run,
      Deterministic.Protocol.run, ih]

private theorem Deterministic.Protocol.toPrivateCoin_complexity {X Y α}
    (p : Deterministic.Protocol X Y α) :
    p.toPrivateCoin.complexity = p.complexity := by
  induction p with
  | output val =>
    simp [Deterministic.Protocol.toPrivateCoin, PrivateCoin.Protocol.complexity,
      Deterministic.Protocol.complexity]
  | alice f P ih =>
    simp [Deterministic.Protocol.toPrivateCoin, PrivateCoin.Protocol.complexity,
      Deterministic.Protocol.complexity, ih]
  | bob f P ih =>
    simp [Deterministic.Protocol.toPrivateCoin, PrivateCoin.Protocol.complexity,
      Deterministic.Protocol.complexity, ih]

theorem PrivateCoin.communicationComplexity_le_deterministic {X Y α}
    (f : X → Y → α) (ε : ℝ) (hε : 0 ≤ ε) :
    PrivateCoin.communicationComplexity f ε ≤ Deterministic.communicationComplexity f := by
  -- Case split on whether det_cc is ⊤ (trivial) or some finite value
  match h : Deterministic.communicationComplexity f with
  | ⊤ => exact le_top
  | (n : ℕ) =>
    -- There exists a det protocol with complexity ≤ n
    obtain ⟨p, hp, hc⟩ := (Deterministic.communicationComplexity_le_iff f n).mp (le_of_eq h)
    -- Convert to rand protocol and show rand_cc ≤ n
    rw [PrivateCoin.communicationComplexity_le_iff]
    refine ⟨Unit, Unit, inferInstance, inferInstance, unitMeasureSpace, unitMeasureSpace,
      unitIsProbabilityMeasure, unitIsProbabilityMeasure, p.toPrivateCoin, ?_, ?_⟩
    · -- approx_computes: error is 0 since the protocol is deterministic
      intro x y
      have hrun : ∀ ω : Unit × Unit, p.toPrivateCoin.run x y ω.1 ω.2 = f x y := by
        intro ω; rw [Deterministic.Protocol.toPrivateCoin_run]
        exact congr_fun (congr_fun hp x) y
      simp [hrun, hε]
    · -- complexity: toPrivateCoin preserves complexity
      rw [Deterministic.Protocol.toPrivateCoin_complexity]; exact hc

end CommunicationComplexity
