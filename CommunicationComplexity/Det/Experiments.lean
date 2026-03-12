import CommunicationComplexity.Det.Basic

namespace DetProtocol

/-This file for basic facts about protocols rather than basic definitions?
Unsure what the best structure is-/

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
  | output _      => {A ×ˢ B}
  | alice f P0 P1 => leafRectanglesAux P0 (A ∩ {x | f x = false}) B ∪
                     leafRectanglesAux P1 (A ∩ {x | f x = true})  B
  | bob   f P0 P1 => leafRectanglesAux P0 A (B ∩ {y | f y = false}) ∪
                     leafRectanglesAux P1 A (B ∩ {y | f y = true})

-- The set of leaf rectangles of a protocol over the full input space X × Y.
def leafRectangles (p : DetProtocol X Y α) : Set (Set (X × Y)) :=
  leafRectanglesAux p Set.univ Set.univ

private lemma aux_isRectangle (p : DetProtocol X Y α) (A : Set X) (B : Set Y)
    (R : Set (X × Y)) (hR : R ∈ leafRectanglesAux p A B) : isRectangle R := by
  induction p generalizing A B with
  | output _ =>
    simp only [leafRectanglesAux, Set.mem_singleton_iff] at hR
    exact ⟨A, B, hR⟩
  | alice f P0 P1 ih0 ih1 =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with h | h
    · exact ih0 _ _ h
    · exact ih1 _ _ h
  | bob f P0 P1 ih0 ih1 =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with h | h
    · exact ih0 _ _ h
    · exact ih1 _ _ h

lemma leafRectangles_isRectangle (p : DetProtocol X Y α)
    (R : Set (X × Y)) (hR : R ∈ leafRectangles p) : isRectangle R :=
  aux_isRectangle p Set.univ Set.univ R hR

private lemma aux_subset (p : DetProtocol X Y α) (A : Set X) (B : Set Y)
    (R : Set (X × Y)) (hR : R ∈ leafRectanglesAux p A B) : R ⊆ A ×ˢ B := by
  induction p generalizing A B with
  | output _ =>
    simp only [leafRectanglesAux, Set.mem_singleton_iff] at hR
    subst hR; exact le_refl _
  | alice f P0 P1 ih0 ih1 =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with h | h
    · exact (ih0 _ _ h).trans (by intro ⟨x, y⟩ ⟨hx, hy⟩; exact ⟨hx.1, hy⟩)
    · exact (ih1 _ _ h).trans (by intro ⟨x, y⟩ ⟨hx, hy⟩; exact ⟨hx.1, hy⟩)
  | bob f P0 P1 ih0 ih1 =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with h | h
    · exact (ih0 _ _ h).trans (by intro ⟨x, y⟩ ⟨hx, hy⟩; exact ⟨hx, hy.1⟩)
    · exact (ih1 _ _ h).trans (by intro ⟨x, y⟩ ⟨hx, hy⟩; exact ⟨hx, hy.1⟩)

private lemma aux_cover (p : DetProtocol X Y α) (A : Set X) (B : Set Y) :
    A ×ˢ B ⊆ ⋃₀ leafRectanglesAux p A B := by
  induction p generalizing A B with
  | output _ =>
    intro xy hxy
    exact Set.mem_sUnion.mpr ⟨_, Set.mem_singleton _, hxy⟩
  | alice f P0 P1 ih0 ih1 =>
    intro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [leafRectanglesAux, Set.sUnion_union]
    cases hf : f x with
    | false => exact Set.mem_union_left  _ (ih0 _ _ ⟨⟨hx, hf⟩, hy⟩)
    | true  => exact Set.mem_union_right _ (ih1 _ _ ⟨⟨hx, hf⟩, hy⟩)
  | bob f P0 P1 ih0 ih1 =>
    intro ⟨x, y⟩ ⟨hx, hy⟩
    simp only [leafRectanglesAux, Set.sUnion_union]
    cases hf : f y with
    | false => exact Set.mem_union_left  _ (ih0 _ _ ⟨hx, ⟨hy, hf⟩⟩)
    | true  => exact Set.mem_union_right _ (ih1 _ _ ⟨hx, ⟨hy, hf⟩⟩)

private lemma aux_disjoint (p : DetProtocol X Y α) (A : Set X) (B : Set Y)
    (R S : Set (X × Y)) (hR : R ∈ leafRectanglesAux p A B) (hS : S ∈ leafRectanglesAux p A B)
    (hne : R ≠ S) : Disjoint R S := by
  induction p generalizing A B with
  | output _ =>
    simp only [leafRectanglesAux, Set.mem_singleton_iff] at hR hS
    exact absurd (hR.trans hS.symm) hne
  | alice f P0 P1 ih0 ih1 =>
    simp only [leafRectanglesAux, Set.mem_union] at hR hS
    rcases hR with hR | hR <;> rcases hS with hS | hS
    · exact ih0 _ _ hR hS
    · apply Set.disjoint_left.mpr; intro xy hxyR hxyS
      have h1 := (aux_subset P0 _ _ R hR hxyR).1.2
      have h2 := (aux_subset P1 _ _ S hS hxyS).1.2
      simp_all
    · apply Set.disjoint_left.mpr; intro xy hxyR hxyS
      have h1 := (aux_subset P1 _ _ R hR hxyR).1.2
      have h2 := (aux_subset P0 _ _ S hS hxyS).1.2
      simp_all
    · exact ih1 _ _ hR hS
  | bob f P0 P1 ih0 ih1 =>
    simp only [leafRectanglesAux, Set.mem_union] at hR hS
    rcases hR with hR | hR <;> rcases hS with hS | hS
    · exact ih0 _ _ hR hS
    · apply Set.disjoint_left.mpr; intro xy hxyR hxyS
      have h1 := (aux_subset P0 _ _ R hR hxyR).2.2
      have h2 := (aux_subset P1 _ _ S hS hxyS).2.2
      simp_all
    · apply Set.disjoint_left.mpr; intro xy hxyR hxyS
      have h1 := (aux_subset P1 _ _ R hR hxyR).2.2
      have h2 := (aux_subset P0 _ _ S hS hxyS).2.2
      simp_all
    · exact ih1 _ _ hR hS

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
  | alice f P0 P1 ih0 ih1 =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with hR | hR
    · have hfx  : f x  = false := (aux_subset P0 _ _ R hR hxy).1.2
      have hfx' : f x' = false := (aux_subset P0 _ _ R hR hxy').1.2
      unfold run
      rw [if_neg (by simp [hfx]), if_neg (by simp [hfx'])]
      exact ih0 _ _ hR
    · have hfx  : f x  = true := (aux_subset P1 _ _ R hR hxy).1.2
      have hfx' : f x' = true := (aux_subset P1 _ _ R hR hxy').1.2
      unfold run
      rw [if_pos (by simp [hfx]), if_pos (by simp [hfx'])]
      exact ih1 _ _ hR
  | bob f P0 P1 ih0 ih1 =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with hR | hR
    · have hfy  : f y  = false := (aux_subset P0 _ _ R hR hxy).2.2
      have hfy' : f y' = false := (aux_subset P0 _ _ R hR hxy').2.2
      unfold run
      rw [if_neg (by simp [hfy]), if_neg (by simp [hfy'])]
      exact ih0 _ _ hR
    · have hfy  : f y  = true := (aux_subset P1 _ _ R hR hxy).2.2
      have hfy' : f y' = true := (aux_subset P1 _ _ R hR hxy').2.2
      unfold run
      rw [if_pos (by simp [hfy]), if_pos (by simp [hfy'])]
      exact ih1 _ _ hR

lemma leafRectangles_mono (p : DetProtocol X Y α)
    (g : X → Y → α) (h_comp : computes p g)
    (R : Set (X × Y)) (hR : R ∈ leafRectangles p) : isMono R g := by
  intro x x' y y' hxy hxy'
  have : p.run x y = p.run x' y' :=
    aux_mono p Set.univ Set.univ R hR x x' y y' hxy hxy'
  simp only [computes] at h_comp
  rw [← congr_fun (congr_fun h_comp x) y, ← congr_fun (congr_fun h_comp x') y']
  exact this


end DetProtocol
