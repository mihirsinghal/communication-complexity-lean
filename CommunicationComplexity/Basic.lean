import Mathlib

open MeasureTheory ProbabilityTheory

inductive DetProtocol (X Y α : Type*) where
  | result (val : α) : DetProtocol X Y α
  | alice (f : X → Bool) (P0 : DetProtocol X Y α) (P1 : DetProtocol X Y α) : DetProtocol X Y α
  | bob (f : Y → Bool) (P0 : DetProtocol X Y α) (P1 : DetProtocol X Y α) : DetProtocol X Y α

namespace DetProtocol

variable {X Y α : Type*}

def run (p : DetProtocol X Y α) (x : X) (y : Y) : α :=
  match p with
  | DetProtocol.result val => val
  | DetProtocol.alice f P0 P1 => if f x then P1.run x y else P0.run x y
  | DetProtocol.bob f P0 P1 => if f y then P1.run x y else P0.run x y

def complexity : DetProtocol X Y α → ℕ
  | DetProtocol.result _ => 0
  | DetProtocol.alice _ P0 P1 => 1 + max P0.complexity P1.complexity
  | DetProtocol.bob _ P0 P1 => 1 + max P0.complexity P1.complexity

def equiv (p q : DetProtocol X Y α) : Prop :=
  ∀ x y, p.run x y = q.run x y

def computes (p : DetProtocol X Y α) (f : X → Y → α) : Prop :=
  ∀ x y, p.run x y = f x y

end DetProtocol

inductive RandProtocol
    (Ω_X Ω_Y : Type*)
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    [IsProbabilityMeasure (volume : Measure Ω_X)]
    [IsProbabilityMeasure (volume : Measure Ω_Y)]
    (X Y α : Type*) where
  | output (a : α) :
      RandProtocol Ω_X Ω_Y X Y α
  | alice
      (f : X → Ω_X → Bool)
      (hf : ∀ x, Measurable (f x))
      (P0 P1 : RandProtocol Ω_X Ω_Y X Y α) :
      RandProtocol Ω_X Ω_Y X Y α
  | bob
      (f : Y → Ω_Y → Bool)
      (hf : ∀ y, Measurable (f y))
      (P0 P1 : RandProtocol Ω_X Ω_Y X Y α) :
      RandProtocol Ω_X Ω_Y X Y α

namespace RandProtocol

variable {Ω_X Ω_Y X Y α : Type*}
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    [IsProbabilityMeasure (volume : Measure Ω_X)]
    [IsProbabilityMeasure (volume : Measure Ω_Y)]

def run
    (p : RandProtocol Ω_X Ω_Y X Y α) (x : X) (y : Y) (ω_x : Ω_X) (ω_y : Ω_Y) :
    α :=
  match p with
  | RandProtocol.output a => a
  | RandProtocol.alice f _ P0 P1 =>
      if f x ω_x then P1.run x y ω_x ω_y else P0.run x y ω_x ω_y
  | RandProtocol.bob f _ P0 P1 =>
      if f y ω_y then P1.run x y ω_x ω_y else P0.run x y ω_x ω_y

theorem measurable_preimage_run
    (p : RandProtocol Ω_X Ω_Y X Y α) (x : X) (y : Y) (s : Set α) :
    MeasurableSet ((fun (ω : Ω_X × Ω_Y) ↦ p.run x y ω.1 ω.2) ⁻¹' s) := by
  induction p with
  | output a =>
    unfold run
    unfold Set.preimage
    simp only [measurableSet_setOf, measurable_const]
  | alice f hf P0 P1 ih0 ih1 =>
    unfold run
    unfold Set.preimage
    have key : {ω : Ω_X × Ω_Y |
        (if f x ω.1 = true then P1.run x y ω.1 ω.2 else P0.run x y ω.1 ω.2) ∈ s} =
      ({ω | f x ω.1 = true} ∩ {ω | P1.run x y ω.1 ω.2 ∈ s}) ∪
      ({ω | ¬(f x ω.1 = true)} ∩ {ω | P0.run x y ω.1 ω.2 ∈ s}) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff]
      by_cases h : f x ω.1 = true <;> simp [h]
    rw [key]
    have hcond : MeasurableSet {ω : Ω_X × Ω_Y | f x ω.1 = true} := by
      have : {ω : Ω_X × Ω_Y | f x ω.1 = true} = (fun ω => f x ω.1) ⁻¹' {true} := by
        ext ω; simp [Set.mem_preimage]
      rw [this]
      exact ((hf x).comp measurable_fst) (measurableSet_singleton true)
    exact (hcond.inter ih1).union (hcond.compl.inter ih0)
  | bob f hf P0 P1 ih0 ih1 =>
    unfold run
    unfold Set.preimage
    have key : {ω : Ω_X × Ω_Y |
        (if f y ω.2 = true then P1.run x y ω.1 ω.2 else P0.run x y ω.1 ω.2) ∈ s} =
      ({ω | f y ω.2 = true} ∩ {ω | P1.run x y ω.1 ω.2 ∈ s}) ∪
      ({ω | ¬(f y ω.2 = true)} ∩ {ω | P0.run x y ω.1 ω.2 ∈ s}) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff]
      by_cases h : f y ω.2 = true <;> simp [h]
    rw [key]
    have hcond : MeasurableSet {ω : Ω_X × Ω_Y | f y ω.2 = true} := by
      have : {ω : Ω_X × Ω_Y | f y ω.2 = true} = (fun ω => f y ω.2) ⁻¹' {true} := by
        ext ω; simp [Set.mem_preimage]
      rw [this]
      exact ((hf y).comp measurable_snd) (measurableSet_singleton true)
    exact (hcond.inter ih1).union (hcond.compl.inter ih0)

def approx_computes
    (p : RandProtocol Ω_X Ω_Y X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y, (volume {ω : Ω_X × Ω_Y | p.run x y ω.1 ω.2 ≠ f x y}).toReal ≤ ε

end RandProtocol
