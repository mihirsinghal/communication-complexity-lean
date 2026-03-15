import CommunicationComplexity.Basic
import CommunicationComplexity.Rectangle.Basic
import CommunicationComplexity.Deterministic.Subprotocol
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.Ring

namespace CommunicationComplexity

namespace Deterministic.Protocol

variable {X Y α : Type*}

-- Internal: leaf rectangles relative to a constraint A × B.
private def leafRectanglesAux (p : Protocol X Y α) (A : Set X) (B : Set Y) :
    Set (Set (X × Y)) :=
  match p with
  | output _  => {A ×ˢ B}
  | alice f P => leafRectanglesAux (P false) (A ∩ {x | f x = false}) B ∪
                 leafRectanglesAux (P true)  (A ∩ {x | f x = true})  B
  | bob   f P => leafRectanglesAux (P false) A (B ∩ {y | f y = false}) ∪
                 leafRectanglesAux (P true)  A (B ∩ {y | f y = true})

/-- The set of rectangles induced by protocol leaves over all inputs `X × Y`. -/
def leafRectangles (p : Protocol X Y α) : Set (Set (X × Y)) :=
  leafRectanglesAux p Set.univ Set.univ

private lemma aux_isRectangle (p : Protocol X Y α) (A : Set X) (B : Set Y)
    (R : Set (X × Y)) (hR : R ∈ leafRectanglesAux p A B) : Rectangle.IsRectangle R := by
  induction p generalizing A B with
  | output _ =>
    simp only [leafRectanglesAux, Set.mem_singleton_iff] at hR
    exact ⟨A, B, hR⟩
  | alice f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with h | h <;> exact ih _ _ _ h
  | bob f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with h | h <;> exact ih _ _ _ h

/-- Every protocol leaf-rectangle is a genuine rectangle. -/
lemma leafRectangles_isRectangle (p : Protocol X Y α)
    (R : Set (X × Y)) (hR : R ∈ leafRectangles p) : Rectangle.IsRectangle R :=
  aux_isRectangle p Set.univ Set.univ R hR

private lemma aux_subset (p : Protocol X Y α) (A : Set X) (B : Set Y)
    (R : Set (X × Y)) (hR : R ∈ leafRectanglesAux p A B) : R ⊆ A ×ˢ B := by
  induction p generalizing A B with
  | output _ =>
    simp only [leafRectanglesAux, Set.mem_singleton_iff] at hR
    subst hR; exact le_refl _
  | alice f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with h | h <;>
      exact (ih _ _ _ h).trans (by intro ⟨x, y⟩ ⟨hx, hy⟩; exact ⟨hx.1, hy⟩)
  | bob f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with h | h <;>
      exact (ih _ _ _ h).trans (by intro ⟨x, y⟩ ⟨hx, hy⟩; exact ⟨hx, hy.1⟩)

private lemma aux_cover (p : Protocol X Y α) (A : Set X) (B : Set Y) :
    A ×ˢ B ⊆ ⋃₀ leafRectanglesAux p A B := by
  induction p generalizing A B with
  | output _ =>
    intro xy hxy
    exact Set.mem_sUnion.mpr ⟨_, Set.mem_singleton _, hxy⟩
  | alice f P ih =>
    intro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [leafRectanglesAux, Set.sUnion_union]
    cases hf : f x with
    | false => exact Set.mem_union_left  _ (ih false _ _ ⟨⟨hx, hf⟩, hy⟩)
    | true  => exact Set.mem_union_right _ (ih true  _ _ ⟨⟨hx, hf⟩, hy⟩)
  | bob f P ih =>
    intro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [leafRectanglesAux, Set.sUnion_union]
    cases hf : f y with
    | false => exact Set.mem_union_left  _ (ih false _ _ ⟨hx, ⟨hy, hf⟩⟩)
    | true  => exact Set.mem_union_right _ (ih true  _ _ ⟨hx, ⟨hy, hf⟩⟩)

private lemma aux_disjoint (p : Protocol X Y α) (A : Set X) (B : Set Y)
    (R S : Set (X × Y)) (hR : R ∈ leafRectanglesAux p A B) (hS : S ∈ leafRectanglesAux p A B)
    (hne : R ≠ S) : Disjoint R S := by
  induction p generalizing A B with
  | output _ =>
    simp only [leafRectanglesAux, Set.mem_singleton_iff] at hR hS
    exact absurd (hR.trans hS.symm) hne
  | alice f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR hS
    rcases hR with hR | hR <;> rcases hS with hS | hS
    · exact ih false _ _ hR hS
    · apply Set.disjoint_left.mpr; intro xy hxyR hxyS
      have h1 := (aux_subset (P false) _ _ R hR hxyR).1.2
      have h2 := (aux_subset (P true)  _ _ S hS hxyS).1.2
      simp_all
    · apply Set.disjoint_left.mpr; intro xy hxyR hxyS
      have h1 := (aux_subset (P true)  _ _ R hR hxyR).1.2
      have h2 := (aux_subset (P false) _ _ S hS hxyS).1.2
      simp_all
    · exact ih true _ _ hR hS
  | bob f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR hS
    rcases hR with hR | hR <;> rcases hS with hS | hS
    · exact ih false _ _ hR hS
    · apply Set.disjoint_left.mpr; intro xy hxyR hxyS
      have h1 := (aux_subset (P false) _ _ R hR hxyR).2.2
      have h2 := (aux_subset (P true)  _ _ S hS hxyS).2.2
      simp_all
    · apply Set.disjoint_left.mpr; intro xy hxyR hxyS
      have h1 := (aux_subset (P true)  _ _ R hR hxyR).2.2
      have h2 := (aux_subset (P false) _ _ S hS hxyS).2.2
      simp_all
    · exact ih true _ _ hR hS

/-- The leaf rectangles of a protocol cover the whole input space. -/
lemma leafRectangles_cover (p : Protocol X Y α) :
    ⋃₀ leafRectangles p = Set.univ :=
  Set.eq_univ_of_univ_subset (by simpa using aux_cover p Set.univ Set.univ)

/-- Distinct protocol leaf rectangles are disjoint. -/
lemma leafRectangles_disjoint (p : Protocol X Y α)
    (R S : Set (X × Y)) (hR : R ∈ leafRectangles p) (hS : S ∈ leafRectangles p)
    (hne : R ≠ S) : Disjoint R S :=
  aux_disjoint p Set.univ Set.univ R S hR hS hne

private lemma aux_mono (p : Protocol X Y α) (A : Set X) (B : Set Y)
    (R : Set (X × Y)) (hR : R ∈ leafRectanglesAux p A B)
    (x x' : X) (y y' : Y) (hxy : (x, y) ∈ R) (hxy' : (x', y') ∈ R) :
    p.run x y = p.run x' y' := by
  induction p generalizing A B with
  | output v => rfl
  | alice f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with hR | hR
    · have hfx  : f x  = false := (aux_subset (P false) _ _ R hR hxy).1.2
      have hfx' : f x' = false := (aux_subset (P false) _ _ R hR hxy').1.2
      simp only [run, hfx, hfx']
      exact ih false _ _ hR
    · have hfx  : f x  = true := (aux_subset (P true) _ _ R hR hxy).1.2
      have hfx' : f x' = true := (aux_subset (P true) _ _ R hR hxy').1.2
      simp only [run, hfx, hfx']
      exact ih true _ _ hR
  | bob f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with hR | hR
    · have hfy  : f y  = false := (aux_subset (P false) _ _ R hR hxy).2.2
      have hfy' : f y' = false := (aux_subset (P false) _ _ R hR hxy').2.2
      simp only [run, hfy, hfy']
      exact ih false _ _ hR
    · have hfy  : f y  = true := (aux_subset (P true) _ _ R hR hxy).2.2
      have hfy' : f y' = true := (aux_subset (P true) _ _ R hR hxy').2.2
      simp only [run, hfy, hfy']
      exact ih true _ _ hR

lemma leafRectangles_mono (p : Protocol X Y α)
    (g : X → Y → α) (h_comp : computes p g)
    (R : Set (X × Y)) (hR : R ∈ leafRectangles p) : Rectangle.IsMonochromatic R g := by
  intro x x' y y' hxy hxy'
  have := aux_mono p Set.univ Set.univ R hR x x' y y' hxy hxy'
  simp only [computes, funext_iff] at h_comp
  rw [← h_comp x y, ← h_comp x' y']; exact this

private lemma aux_card (p : Protocol X Y α) (A : Set X) (B : Set Y) :
    Set.ncard (leafRectanglesAux p A B) ≤ 2 ^ p.complexity := by
  induction p generalizing A B with
  | output _ =>
    simp [leafRectanglesAux, complexity]
  | alice f P ih =>
    simp only [leafRectanglesAux, complexity]
    calc Set.ncard (leafRectanglesAux (P false) (A ∩ {x | f x = false}) B ∪
                    leafRectanglesAux (P true)  (A ∩ {x | f x = true})  B)
        ≤ Set.ncard (leafRectanglesAux (P false) (A ∩ {x | f x = false}) B) +
          Set.ncard (leafRectanglesAux (P true)  (A ∩ {x | f x = true})  B) :=
            Set.ncard_union_le _ _
      _ ≤ 2 ^ (P false).complexity + 2 ^ (P true).complexity := by
            exact Nat.add_le_add (ih false _ _) (ih true _ _)
      _ ≤ 2 ^ max (P false).complexity (P true).complexity +
          2 ^ max (P false).complexity (P true).complexity :=
            Nat.add_le_add
              (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _))
              (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
      _ = 2 ^ (1 + max (P false).complexity (P true).complexity) := by ring
  | bob f P ih =>
    simp only [leafRectanglesAux, complexity]
    calc Set.ncard (leafRectanglesAux (P false) A (B ∩ {y | f y = false}) ∪
                    leafRectanglesAux (P true)  A (B ∩ {y | f y = true}))
        ≤ Set.ncard (leafRectanglesAux (P false) A (B ∩ {y | f y = false})) +
          Set.ncard (leafRectanglesAux (P true)  A (B ∩ {y | f y = true})) :=
            Set.ncard_union_le _ _
      _ ≤ 2 ^ (P false).complexity + 2 ^ (P true).complexity :=
            Nat.add_le_add (ih false _ _) (ih true _ _)
      _ ≤ 2 ^ max (P false).complexity (P true).complexity +
          2 ^ max (P false).complexity (P true).complexity :=
            Nat.add_le_add
              (Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _))
              (Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _))
      _ = 2 ^ (1 + max (P false).complexity (P true).complexity) := by ring

lemma leafRectangles_card (p : Protocol X Y α) :
    Set.ncard (leafRectangles p) ≤ 2 ^ p.complexity :=
  aux_card p Set.univ Set.univ

/-- The leaf rectangles of a protocol computing `g` form a
monochromatic rectangle partition. -/
theorem leafRectangles_isMonoPartition
    (p : Protocol X Y α) (g : X → Y → α)
    (h_comp : computes p g) :
    Rectangle.IsMonoPartition (leafRectangles p) g :=
  ⟨fun R hR => leafRectangles_isRectangle p R hR,
   fun R hR => leafRectangles_mono p g h_comp R hR,
   leafRectangles_cover p,
   fun R S hR hS hne =>
     leafRectangles_disjoint p R S hR hS hne⟩

/-- Theorem 1.6: if π computes g, then X × Y is partitioned
into at most 2^c monochromatic rectangles with respect to g. -/
theorem rectangle_partition
    (p : Protocol X Y α) (g : X → Y → α)
    (h_comp : computes p g) :
    Rectangle.IsMonoPartition (leafRectangles p) g ∧
    Set.ncard (leafRectangles p) ≤ 2 ^ p.complexity :=
  ⟨leafRectangles_isMonoPartition p g h_comp,
   leafRectangles_card p⟩

/-- The input pairs that reach a fixed subprotocol path form a rectangle. -/
theorem reachesPath_isRectangle {s p : Protocol X Y α} (hsp : SubprotocolPath s p) :
    Rectangle.IsRectangle {xy : X × Y | reachesPath hsp xy.1 xy.2} := by
  refine ⟨reachXPath hsp, reachYPath hsp, ?_⟩
  ext xy
  rcases xy with ⟨x, y⟩
  simp [reachesPath, Set.mem_prod]

/-- The input pairs that reach a chosen subprotocol witness form a rectangle. -/
theorem reaches_isRectangle {s p : Protocol X Y α} (hsp : IsSubprotocol s p) :
    Rectangle.IsRectangle {xy : X × Y | reaches hsp xy.1 xy.2} := by
  simpa [reaches, reachX, reachY] using reachesPath_isRectangle (choosePath hsp)

end Deterministic.Protocol

namespace Deterministic

variable {X Y α : Type*}

/-- If `deterministic_communication_complexity g ≤ n`, then there is a monochromatic
rectangle partition of `X × Y` with at most `2^n` rectangles. -/
theorem mono_partition_of_communicationComplexity_le
    (g : X → Y → α) (n : ℕ)
    (h : communicationComplexity g ≤ n) :
    ∃ Part : Set (Set (X × Y)),
      Rectangle.IsMonoPartition Part g ∧
      Set.ncard Part ≤ 2 ^ n := by
  obtain ⟨p, hp, hc⟩ := (communicationComplexity_le_iff g n).mp h
  exact ⟨Protocol.leafRectangles p,
    Protocol.leafRectangles_isMonoPartition p g hp,
    (Protocol.leafRectangles_card p).trans
      (Nat.pow_le_pow_right (by omega) hc)⟩

/-- Rectangle lower-bound method: to prove `CC(g) ≥ n + 1`, it suffices to show
every monochromatic rectangle partition of `g` has more than `2^n` parts. -/
theorem communicationComplexity_lower_bound
    (g : X → Y → α) (n : ℕ)
    (h : ∀ Part : Set (Set (X × Y)),
      Rectangle.IsMonoPartition Part g →
      2 ^ n < Set.ncard Part) :
    (n + 1 : ℕ) ≤ communicationComplexity g := by
  rw [le_communicationComplexity_iff]
  intro p hp
  have hle : communicationComplexity g ≤
      p.complexity :=
    (communicationComplexity_le_iff g p.complexity).mpr ⟨p, hp, le_refl _⟩
  obtain ⟨Part, hPart, hCard⟩ :=
    mono_partition_of_communicationComplexity_le g p.complexity hle
  have hsuff := h Part hPart
  by_contra hlt; push_neg at hlt
  have : 2 ^ p.complexity ≤ 2 ^ n :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

end Deterministic

end CommunicationComplexity
