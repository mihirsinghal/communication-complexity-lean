import CommunicationComplexity.Det.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.Ring

namespace DetProtocol

variable {X Y α : Type*}

def isRectangle (S : Set (X × Y)) : Prop :=
  ∃ A : Set X, ∃ B : Set Y, S = A ×ˢ B

theorem isRectangle_iff (R : Set (X × Y)) :
    isRectangle R ↔ ∀ x x' y y', (x, y) ∈ R → (x', y') ∈ R → (x', y) ∈ R ∧ (x, y') ∈ R := by
  constructor
  · rintro ⟨A, B, rfl⟩ x x' y y' ⟨hx, hy⟩ ⟨hx', hy'⟩
    exact ⟨⟨hx', hy⟩, ⟨hx, hy'⟩⟩
  · intro h
    refine ⟨Prod.fst '' R, Prod.snd '' R, ?_⟩
    ext ⟨x, y⟩
    simp only [Set.mem_prod, Set.mem_image, Prod.exists]
    constructor
    · intro hxy
      exact ⟨⟨x, y, hxy, rfl⟩, ⟨x, y, hxy, rfl⟩⟩
    · rintro ⟨⟨x', y', hx'y', rfl⟩, ⟨x'', y'', hx''y'', rfl⟩⟩
      exact (h _ _ _ _ hx'y' hx''y'').2

-- Internal: leaf rectangles relative to a constraint A × B.
private def leafRectanglesAux (p : DetProtocol X Y α) (A : Set X) (B : Set Y) :
    Set (Set (X × Y)) :=
  match p with
  | output _  => {A ×ˢ B}
  | alice f P => leafRectanglesAux (P false) (A ∩ {x | f x = false}) B ∪
                 leafRectanglesAux (P true)  (A ∩ {x | f x = true})  B
  | bob   f P => leafRectanglesAux (P false) A (B ∩ {y | f y = false}) ∪
                 leafRectanglesAux (P true)  A (B ∩ {y | f y = true})

-- The set of leaf rectangles of a protocol over the full input space X × Y.
def leafRectangles (p : DetProtocol X Y α) : Set (Set (X × Y)) :=
  leafRectanglesAux p Set.univ Set.univ

private lemma aux_isRectangle (p : DetProtocol X Y α) (A : Set X) (B : Set Y)
    (R : Set (X × Y)) (hR : R ∈ leafRectanglesAux p A B) : isRectangle R := by
  induction p generalizing A B with
  | output _ =>
    simp only [leafRectanglesAux, Set.mem_singleton_iff] at hR
    exact ⟨A, B, hR⟩
  | alice f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with h | h
    · exact ih false _ _ h
    · exact ih true  _ _ h
  | bob f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with h | h
    · exact ih false _ _ h
    · exact ih true  _ _ h

lemma leafRectangles_isRectangle (p : DetProtocol X Y α)
    (R : Set (X × Y)) (hR : R ∈ leafRectangles p) : isRectangle R :=
  aux_isRectangle p Set.univ Set.univ R hR

private lemma aux_subset (p : DetProtocol X Y α) (A : Set X) (B : Set Y)
    (R : Set (X × Y)) (hR : R ∈ leafRectanglesAux p A B) : R ⊆ A ×ˢ B := by
  induction p generalizing A B with
  | output _ =>
    simp only [leafRectanglesAux, Set.mem_singleton_iff] at hR
    subst hR; exact le_refl _
  | alice f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with h | h
    · exact (ih false _ _ h).trans (by intro ⟨x, y⟩ ⟨hx, hy⟩; exact ⟨hx.1, hy⟩)
    · exact (ih true  _ _ h).trans (by intro ⟨x, y⟩ ⟨hx, hy⟩; exact ⟨hx.1, hy⟩)
  | bob f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with h | h
    · exact (ih false _ _ h).trans (by intro ⟨x, y⟩ ⟨hx, hy⟩; exact ⟨hx, hy.1⟩)
    · exact (ih true  _ _ h).trans (by intro ⟨x, y⟩ ⟨hx, hy⟩; exact ⟨hx, hy.1⟩)

private lemma aux_cover (p : DetProtocol X Y α) (A : Set X) (B : Set Y) :
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

private lemma aux_disjoint (p : DetProtocol X Y α) (A : Set X) (B : Set Y)
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

-- Lemma 1.4: the leaf rectangles of a protocol partition X × Y.
lemma leafRectangles_cover (p : DetProtocol X Y α) :
    ⋃₀ leafRectangles p = Set.univ :=
  Set.eq_univ_of_univ_subset (by simpa using aux_cover p Set.univ Set.univ)

lemma leafRectangles_disjoint (p : DetProtocol X Y α)
    (R S : Set (X × Y)) (hR : R ∈ leafRectangles p) (hS : S ∈ leafRectangles p)
    (hne : R ≠ S) : Disjoint R S :=
  aux_disjoint p Set.univ Set.univ R S hR hS hne


def isMono (S : Set (X × Y)) (g : X → Y → α) : Prop :=
  ∀ x x' y y', (x, y) ∈ S → (x', y') ∈ S → g x y = g x' y'

private lemma aux_mono (p : DetProtocol X Y α) (A : Set X) (B : Set Y)
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

lemma leafRectangles_mono (p : DetProtocol X Y α)
    (g : X → Y → α) (h_comp : computes p g)
    (R : Set (X × Y)) (hR : R ∈ leafRectangles p) : isMono R g := by
  intro x x' y y' hxy hxy'
  have : p.run x y = p.run x' y' :=
    aux_mono p Set.univ Set.univ R hR x x' y y' hxy hxy'
  simp only [computes] at h_comp
  rw [← congr_fun (congr_fun h_comp x) y, ← congr_fun (congr_fun h_comp x') y']
  exact this


private lemma aux_card (p : DetProtocol X Y α) (A : Set X) (B : Set Y) :
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

lemma leafRectangles_card (p : DetProtocol X Y α) :
    Set.ncard (leafRectangles p) ≤ 2 ^ p.complexity :=
  aux_card p Set.univ Set.univ

/-- Theorem 1.6: if π computes g, then X × Y is partitioned into at most 2^c
monochromatic rectangles with respect to g. -/
theorem rectangle_partition (p : DetProtocol X Y α) (g : X → Y → α) (h_comp : computes p g) :
    (∀ R ∈ leafRectangles p, isMono R g) ∧
    Set.ncard (leafRectangles p) ≤ 2 ^ p.complexity :=
  ⟨fun R hR => leafRectangles_mono p g h_comp R hR, leafRectangles_card p⟩

end DetProtocol
