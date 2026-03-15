import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory

namespace CommunicationComplexity

namespace PrivateCoin

/-- A randomized two-party communication protocol. Each player has access to private
randomness (`Ω_X` for Alice, `Ω_Y` for Bob), modeled as probability spaces.
At each step, a player sends a bit that may depend on both their input and their randomness. -/
inductive Protocol
    (Ω_X Ω_Y : Type*)
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    [IsProbabilityMeasure (volume : Measure Ω_X)]
    [IsProbabilityMeasure (volume : Measure Ω_Y)]
    (X Y α : Type*) where
  | output (a : α) :
      Protocol Ω_X Ω_Y X Y α
  | alice
      (f : X → Ω_X → Bool)
      (hf : ∀ x, Measurable (f x))
      (P : Bool → Protocol Ω_X Ω_Y X Y α) :
      Protocol Ω_X Ω_Y X Y α
  | bob
      (f : Y → Ω_Y → Bool)
      (hf : ∀ y, Measurable (f y))
      (P : Bool → Protocol Ω_X Ω_Y X Y α) :
      Protocol Ω_X Ω_Y X Y α

namespace Protocol

variable {Ω_X Ω_Y X Y α : Type*}
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    [IsProbabilityMeasure (volume : Measure Ω_X)]
    [IsProbabilityMeasure (volume : Measure Ω_Y)]

/-- Executes the randomized protocol on inputs `x`, `y` with random coins `ω_x`, `ω_y`. -/
def run
    (p : Protocol Ω_X Ω_Y X Y α) (x : X) (y : Y) (ω_x : Ω_X) (ω_y : Ω_Y) :
    α :=
  match p with
  | .output a => a
  | .alice f _ P => (P (f x ω_x)).run x y ω_x ω_y
  | .bob f _ P => (P (f y ω_y)).run x y ω_x ω_y

def complexity : Protocol Ω_X Ω_Y X Y α → ℕ
  | .output _ => 0
  | .alice _ _ P => 1 + max (P false).complexity (P true).complexity
  | .bob _ _ P => 1 + max (P false).complexity (P true).complexity

/-- Swaps the roles of Alice and Bob, producing a protocol on `Y × X` from one on `X × Y`.
Alice nodes become bob nodes and vice versa; the randomness spaces are also swapped. -/
def swap : Protocol Ω_X Ω_Y X Y α → Protocol Ω_Y Ω_X Y X α
  | .output a => .output a
  | .alice f hf P => .bob f hf (fun b => (P b).swap)
  | .bob f hf P => .alice f hf (fun b => (P b).swap)

@[simp]
theorem swap_run (p : Protocol Ω_X Ω_Y X Y α) (x : X) (y : Y)
    (ω_x : Ω_X) (ω_y : Ω_Y) :
    p.swap.run y x ω_y ω_x = p.run x y ω_x ω_y := by
  induction p with
  | output a => simp [swap, run]
  | alice f hf P ih => simp [swap, run, ih]
  | bob f hf P ih => simp [swap, run, ih]

@[simp]
theorem swap_complexity (p : Protocol Ω_X Ω_Y X Y α) :
    p.swap.complexity = p.complexity := by
  induction p with
  | output a => simp [swap, complexity]
  | alice f hf P ih => simp [swap, complexity, ih]
  | bob f hf P ih => simp [swap, complexity, ih]

/-- The preimage of any set under the protocol's output is measurable in the product
probability space, which is needed to make sense of error probabilities. -/
theorem measurable_preimage_run
    (p : Protocol Ω_X Ω_Y X Y α) (x : X) (y : Y) (s : Set α) :
    MeasurableSet ((fun (ω : Ω_X × Ω_Y) ↦ p.run x y ω.1 ω.2) ⁻¹' s) := by
  induction p with
  | output a =>
    unfold run
    unfold Set.preimage
    simp only [measurableSet_setOf, measurable_const]
  | alice f hf P ih =>
    unfold run
    unfold Set.preimage
    have key : {ω : Ω_X × Ω_Y |
        (P (f x ω.1)).run x y ω.1 ω.2 ∈ s} =
      ({ω | f x ω.1 = true} ∩ {ω | (P true).run x y ω.1 ω.2 ∈ s}) ∪
      ({ω | ¬(f x ω.1 = true)} ∩ {ω | (P false).run x y ω.1 ω.2 ∈ s}) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff]
      by_cases h : f x ω.1 = true <;> simp [h]
    rw [key]
    have hcond : MeasurableSet {ω : Ω_X × Ω_Y | f x ω.1 = true} := by
      have : {ω : Ω_X × Ω_Y | f x ω.1 = true} = (fun ω => f x ω.1) ⁻¹' {true} := by
        ext ω; simp [Set.mem_preimage]
      rw [this]
      exact ((hf x).comp measurable_fst) (measurableSet_singleton true)
    exact (hcond.inter (ih true)).union (hcond.compl.inter (ih false))
  | bob f hf P ih =>
    unfold run
    unfold Set.preimage
    have key : {ω : Ω_X × Ω_Y |
        (P (f y ω.2)).run x y ω.1 ω.2 ∈ s} =
      ({ω | f y ω.2 = true} ∩ {ω | (P true).run x y ω.1 ω.2 ∈ s}) ∪
      ({ω | ¬(f y ω.2 = true)} ∩ {ω | (P false).run x y ω.1 ω.2 ∈ s}) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff]
      by_cases h : f y ω.2 = true <;> simp [h]
    rw [key]
    have hcond : MeasurableSet {ω : Ω_X × Ω_Y | f y ω.2 = true} := by
      have : {ω : Ω_X × Ω_Y | f y ω.2 = true} = (fun ω => f y ω.2) ⁻¹' {true} := by
        ext ω; simp [Set.mem_preimage]
      rw [this]
      exact ((hf y).comp measurable_snd) (measurableSet_singleton true)
    exact (hcond.inter (ih true)).union (hcond.compl.inter (ih false))

/-- A randomized protocol `ε`-computes a function `f` if for every input `(x, y)`,
the probability of outputting a value other than `f x y` is at most `ε`. -/
def approx_computes
    (p : Protocol Ω_X Ω_Y X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y, (volume {ω : Ω_X × Ω_Y | p.run x y ω.1 ω.2 ≠ f x y}).toReal ≤ ε

end Protocol

end PrivateCoin

end CommunicationComplexity
