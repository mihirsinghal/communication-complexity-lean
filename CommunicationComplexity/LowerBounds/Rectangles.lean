import CommunicationComplexity.Basic
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
    rcases hR with h | h <;> exact ih _ _ _ h
  | bob f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with h | h <;> exact ih _ _ _ h

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
    rcases hR with h | h <;>
      exact (ih _ _ _ h).trans (by intro ⟨x, y⟩ ⟨hx, hy⟩; exact ⟨hx.1, hy⟩)
  | bob f P ih =>
    simp only [leafRectanglesAux, Set.mem_union] at hR
    rcases hR with h | h <;>
      exact (ih _ _ _ h).trans (by intro ⟨x, y⟩ ⟨hx, hy⟩; exact ⟨hx, hy.1⟩)

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

/-- A set of sets is a monochromatic rectangle partition of `X × Y`
with respect to `g` if every member is a rectangle, every member is
monochromatic for `g`, the members cover `X × Y`, and distinct
members are disjoint. -/
def isMonoRectPartition
    (Part : Set (Set (X × Y))) (g : X → Y → α) : Prop :=
  (∀ R ∈ Part, isRectangle R) ∧
  (∀ R ∈ Part, isMono R g) ∧
  ⋃₀ Part = Set.univ ∧
  (∀ R S, R ∈ Part → S ∈ Part → R ≠ S → Disjoint R S)

namespace isMonoRectPartition

variable {Part : Set (Set (X × Y))} {g : X → Y → α}

/-- Every point is in some member of the partition. -/
theorem exists_mem (h : isMonoRectPartition Part g)
    (p : X × Y) : ∃ R ∈ Part, p ∈ R := by
  have := h.2.2.1 ▸ Set.mem_univ p
  exact Set.mem_sUnion.mp this

/-- If a point is in two members, they must be equal. -/
theorem eq_of_mem (h : isMonoRectPartition Part g)
    {R S : Set (X × Y)} (hR : R ∈ Part) (hS : S ∈ Part)
    {p : X × Y} (hp1 : p ∈ R) (hp2 : p ∈ S) : R = S := by
  by_contra hne
  exact Set.disjoint_left.mp (h.2.2.2 R S hR hS hne) hp1 hp2

/-- Rectangle cross-product: if `(x,y)` and `(x',y')` are in the
same member, then so are `(x',y)` and `(x,y')`. -/
theorem cross_mem (h : isMonoRectPartition Part g)
    {R : Set (X × Y)} (hR : R ∈ Part)
    {x x' : X} {y y' : Y}
    (hxy : (x, y) ∈ R) (hx'y' : (x', y') ∈ R) :
    (x', y) ∈ R ∧ (x, y') ∈ R :=
  (isRectangle_iff R).mp (h.1 R hR) x x' y y' hxy hx'y'

/-- Monochromatic: any two points in the same member have equal
function values. -/
theorem apply_eq (h : isMonoRectPartition Part g)
    {R : Set (X × Y)} (hR : R ∈ Part)
    {x x' : X} {y y' : Y}
    (hxy : (x, y) ∈ R) (hx'y' : (x', y') ∈ R) :
    g x y = g x' y' :=
  h.2.1 R hR x x' y y' hxy hx'y'

end isMonoRectPartition

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
  have := aux_mono p Set.univ Set.univ R hR x x' y y' hxy hxy'
  simp only [computes, funext_iff] at h_comp
  rw [← h_comp x y, ← h_comp x' y']; exact this


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

/-- The leaf rectangles of a protocol computing `g` form a
monochromatic rectangle partition. -/
theorem leafRectangles_isMonoRectPartition
    (p : DetProtocol X Y α) (g : X → Y → α)
    (h_comp : computes p g) :
    isMonoRectPartition (leafRectangles p) g :=
  ⟨fun R hR => leafRectangles_isRectangle p R hR,
   fun R hR => leafRectangles_mono p g h_comp R hR,
   leafRectangles_cover p,
   fun R S hR hS hne =>
     leafRectangles_disjoint p R S hR hS hne⟩

/-- Theorem 1.6: if π computes g, then X × Y is partitioned
into at most 2^c monochromatic rectangles with respect to g. -/
theorem rectangle_partition
    (p : DetProtocol X Y α) (g : X → Y → α)
    (h_comp : computes p g) :
    isMonoRectPartition (leafRectangles p) g ∧
    Set.ncard (leafRectangles p) ≤ 2 ^ p.complexity :=
  ⟨leafRectangles_isMonoRectPartition p g h_comp,
   leafRectangles_card p⟩

/-- Rephrasing of `rectangle_partition` using non-explicit partition.
If the deterministic communication complexity of `g` is at most `n`,
then there exists a monochromatic rectangle partition of `X × Y` with
at most `2^n` rectangles. -/
theorem mono_rectangle_partition_of_det_cc
    (g : X → Y → α) (n : ℕ)
    (h : deterministic_communication_complexity g ≤ n) :
    ∃ Part : Set (Set (X × Y)),
      isMonoRectPartition Part g ∧
      Set.ncard Part ≤ 2 ^ n := by
  obtain ⟨p, hp, hc⟩ := (det_cc_le_iff g n).mp h
  exact ⟨leafRectangles p,
    leafRectangles_isMonoRectPartition p g hp,
    (leafRectangles_card p).trans
      (Nat.pow_le_pow_right (by omega) hc)⟩

/-- Lower bound method: to show `CC(g) ≥ n + 1`, it suffices to
show every monochromatic rectangle partition of `g` has more than
`2^n` elements. -/
theorem det_cc_lower_bound
    (g : X → Y → α) (n : ℕ)
    (h : ∀ Part : Set (Set (X × Y)),
      isMonoRectPartition Part g →
      2 ^ n < Set.ncard Part) :
    (n + 1 : ℕ) ≤ deterministic_communication_complexity g := by
  rw [le_det_cc_iff]
  intro p hp
  have hle : deterministic_communication_complexity g ≤
      p.complexity :=
    (det_cc_le_iff g p.complexity).mpr ⟨p, hp, le_refl _⟩
  obtain ⟨Part, hPart, hCard⟩ :=
    mono_rectangle_partition_of_det_cc g p.complexity hle
  have hsuff := h Part hPart
  by_contra hlt; push_neg at hlt
  have : 2 ^ p.complexity ≤ 2 ^ n :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

end DetProtocol
