import CommunicationComplexity.Det.Basic
import CommunicationComplexity.Det.Generalized
import CommunicationComplexity.Rand.Basic
import Mathlib.MeasureTheory.Measure.Dirac

open MeasureTheory

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

/-- The deterministic communication complexity of a function `f : X → Y → α`, defined as the
minimum worst-case number of bits exchanged over all deterministic protocols computing `f`.
Returns `⊤` if no finite protocol computes `f`. -/
noncomputable def deterministic_communication_complexity {X Y α} (f : X → Y → α) : WithTop ℕ :=
  ⨅ (p : DetProtocol X Y α) (_ : p.computes f), (p.complexity : WithTop ℕ)

/-- The deterministic communication complexity of `f` is at most `n` iff there exists a
deterministic protocol computing `f` with complexity at most `n`. -/
theorem det_cc_le_iff {X Y α} (f : X → Y → α) (n : ℕ) :
    deterministic_communication_complexity f ≤ n ↔
      ∃ p : DetProtocol X Y α, p.computes f ∧ p.complexity ≤ n := by
  simp only [deterministic_communication_complexity, WithTop.iInf_le_coe_iff, Nat.cast_le,
    exists_prop]

/-- The deterministic communication complexity of `f` is at most `n` iff there exists a
generalized deterministic protocol computing `f` with complexity at most `n`. -/
theorem det_cc_le_iff_generalized {X Y α} (f : X → Y → α) (n : ℕ) :
    deterministic_communication_complexity f ≤ n ↔
      ∃ p : DetProtocolGeneralized X Y α, p.run = f ∧ p.complexity ≤ n := by
  rw [det_cc_le_iff]
  constructor
  · rintro ⟨p, hp, hc⟩
    obtain ⟨P, hP_run, hP_comp⟩ := DetProtocolGeneralized.det_protocol_to_det_protocol_generalized p
    exact ⟨P, hP_run.trans hp, hP_comp ▸ hc⟩
  · rintro ⟨p, hp, hc⟩
    obtain ⟨P, hP_run, hP_comp⟩ := DetProtocolGeneralized.det_protocol_generalized_to_det_protocol p
    exact ⟨P, hP_run.trans hp, hP_comp ▸ hc⟩

/-- The deterministic communication complexity of `f` is at least `n` iff every deterministic
protocol computing `f` has complexity at least `n`. -/
theorem le_det_cc_iff {X Y α} (f : X → Y → α) (n : ℕ) :
    (n : WithTop ℕ) ≤ deterministic_communication_complexity f ↔
      ∀ p : DetProtocol X Y α, p.computes f → n ≤ p.complexity := by
  simp only [deterministic_communication_complexity, le_iInf_iff, Nat.cast_le]

/-- The `ε`-error randomized communication complexity of a function `f : X → Y → α`, defined as
the minimum worst-case number of bits exchanged over all randomized protocols that compute `f`
with error probability at most `ε` on every input. The randomness spaces are required to be finite.
Returns `⊤` if no finite protocol `ε`-computes `f`. -/
noncomputable def randomized_communication_complexity {X Y α} (f : X → Y → α) (ε : ℝ) : WithTop ℕ :=
  ⨅ (Ω_X : Type) (Ω_Y : Type) (_ : Fintype Ω_X) (_ : Fintype Ω_Y)
    (_ : MeasureSpace Ω_X) (_ : MeasureSpace Ω_Y)
    (_ : IsProbabilityMeasure (volume : Measure Ω_X))
    (_ : IsProbabilityMeasure (volume : Measure Ω_Y))
    (p : RandProtocol Ω_X Ω_Y X Y α) (_ : p.approx_computes f ε),
    (p.complexity : WithTop ℕ)

/-- The randomized communication complexity of `f` at error `ε` is at most `n` iff there exist
finite probability spaces and a randomized protocol that `ε`-computes `f` with complexity at
most `n`. -/
theorem rand_cc_le_iff {X Y α} (f : X → Y → α) (ε : ℝ) (n : ℕ) :
    randomized_communication_complexity f ε ≤ n ↔
      ∃ (Ω_X Ω_Y : Type) (_ : Fintype Ω_X) (_ : Fintype Ω_Y)
        (_ : MeasureSpace Ω_X) (_ : MeasureSpace Ω_Y)
        (_ : IsProbabilityMeasure (volume : Measure Ω_X))
        (_ : IsProbabilityMeasure (volume : Measure Ω_Y))
        (p : RandProtocol Ω_X Ω_Y X Y α),
        p.approx_computes f ε ∧ p.complexity ≤ n := by
  simp only [randomized_communication_complexity, WithTop.iInf_le_coe_iff, Nat.cast_le, exists_prop,
    exists_const_iff, exists_and_left]

/-- The randomized communication complexity of `f` at error `ε` is at least `n` iff every
randomized protocol that `ε`-computes `f` (over any finite probability spaces) has complexity
at least `n`. -/
theorem le_rand_cc_iff {X Y α} (f : X → Y → α) (ε : ℝ) (n : ℕ) :
    (n : WithTop ℕ) ≤ randomized_communication_complexity f ε ↔
      ∀ (Ω_X Ω_Y : Type) [Fintype Ω_X] [Fintype Ω_Y]
        [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
        [IsProbabilityMeasure (volume : Measure Ω_X)]
        [IsProbabilityMeasure (volume : Measure Ω_Y)]
        (p : RandProtocol Ω_X Ω_Y X Y α),
        p.approx_computes f ε → n ≤ p.complexity := by
  unfold randomized_communication_complexity
  simp only [le_iInf_iff, Nat.cast_le]

/-- Convert a deterministic protocol to a randomized protocol with trivial (Unit) probability spaces.
The randomized protocol ignores its randomness and behaves identically to the deterministic one. -/
-- Unit with Dirac measure as a probability space, used for embedding det protocols into rand
private noncomputable instance unitMeasureSpace : MeasureSpace Unit := ⟨Measure.dirac ()⟩
private instance unitIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure Unit) :=
  ⟨by simp [unitMeasureSpace, Measure.dirac_apply_of_mem (Set.mem_univ ())]⟩

/-- Convert a deterministic protocol to a randomized protocol over Unit probability spaces. -/
private def DetProtocol.toRand (p : DetProtocol X Y α) : RandProtocol Unit Unit X Y α :=
  match p with
  | DetProtocol.output val => RandProtocol.output val
  | DetProtocol.alice f P => RandProtocol.alice (fun x _ => f x) (fun _ => measurable_const) (fun b => (P b).toRand)
  | DetProtocol.bob f P => RandProtocol.bob (fun y _ => f y) (fun _ => measurable_const) (fun b => (P b).toRand)

private theorem DetProtocol.toRand_run (p : DetProtocol X Y α) (x : X) (y : Y) (ω_x : Unit) (ω_y : Unit) :
    p.toRand.run x y ω_x ω_y = p.run x y := by
  induction p with
  | output val => simp [DetProtocol.toRand, RandProtocol.run, DetProtocol.run]
  | alice f P ih => simp [DetProtocol.toRand, RandProtocol.run, DetProtocol.run, ih]
  | bob f P ih => simp [DetProtocol.toRand, RandProtocol.run, DetProtocol.run, ih]

private theorem DetProtocol.toRand_complexity (p : DetProtocol X Y α) :
    p.toRand.complexity = p.complexity := by
  induction p with
  | output val => simp [DetProtocol.toRand, RandProtocol.complexity, DetProtocol.complexity]
  | alice f P ih => simp [DetProtocol.toRand, RandProtocol.complexity, DetProtocol.complexity, ih]
  | bob f P ih => simp [DetProtocol.toRand, RandProtocol.complexity, DetProtocol.complexity, ih]

theorem rand_cc_le_det_cc {X Y α} (f : X → Y → α) (ε : ℝ) (hε : 0 ≤ ε) :
    randomized_communication_complexity f ε ≤ deterministic_communication_complexity f := by
  -- Case split on whether det_cc is ⊤ (trivial) or some finite value
  match h : deterministic_communication_complexity f with
  | ⊤ => exact le_top
  | (n : ℕ) =>
    -- There exists a det protocol with complexity ≤ n
    obtain ⟨p, hp, hc⟩ := (det_cc_le_iff f n).mp (le_of_eq h)
    -- Convert to rand protocol and show rand_cc ≤ n
    rw [rand_cc_le_iff]
    refine ⟨Unit, Unit, Unit.fintype, Unit.fintype, unitMeasureSpace, unitMeasureSpace,
      unitIsProbabilityMeasure, unitIsProbabilityMeasure, p.toRand, ?_, ?_⟩
    · -- approx_computes: error is 0 since the protocol is deterministic
      intro x y
      have hrun : ∀ ω : Unit × Unit, p.toRand.run x y ω.1 ω.2 = f x y := by
        intro ω; rw [DetProtocol.toRand_run]; exact congr_fun (congr_fun hp x) y
      simp [hrun, hε]
    · -- complexity: toRand preserves complexity
      rw [DetProtocol.toRand_complexity]; exact hc
