import CommunicationComplexity.Deterministic.Rectangle
import Mathlib.MeasureTheory.MeasurableSpace.Defs

namespace CommunicationComplexity

namespace Deterministic.Protocol

variable {X Y α : Type*}

/-- The finite type of leaf rectangles of a protocol. We use this as the transcript alphabet. -/
abbrev Leaf (p : Protocol X Y α) : Type _ :=
  {R : Set (X × Y) // R ∈ p.leafRectangles}

noncomputable instance leafFintype (p : Protocol X Y α) : Fintype p.Leaf :=
  (leafRectangles_finite p).fintype

instance leafMeasurableSpace (p : Protocol X Y α) : MeasurableSpace p.Leaf := ⊤

private theorem exists_leaf_containing (p : Protocol X Y α) (xy : X × Y) :
    ∃ R : p.Leaf, xy ∈ (R : Set (X × Y)) := by
  have hcover : xy ∈ ⋃₀ p.leafRectangles := by
    rw [leafRectangles_cover p]
    simp
  rcases Set.mem_sUnion.mp hcover with ⟨R, hR, hxyR⟩
  exact ⟨⟨R, hR⟩, hxyR⟩

/-- The canonical leaf reached by an input pair. -/
noncomputable def transcript (p : Protocol X Y α) (xy : X × Y) : p.Leaf :=
  Classical.choose (exists_leaf_containing p xy)

/-- The input pair belongs to its transcript leaf. -/
theorem mem_transcript (p : Protocol X Y α) (xy : X × Y) :
    xy ∈ (p.transcript xy : Set (X × Y)) :=
  Classical.choose_spec (exists_leaf_containing p xy)

/-- If an input belongs to a leaf, then the canonical transcript of that input is that leaf. -/
theorem transcript_eq_of_mem_leaf
    (p : Protocol X Y α) (R : p.Leaf) {xy : X × Y}
    (hxy : xy ∈ (R : Set (X × Y))) :
    p.transcript xy = R := by
  by_contra hne
  have hset_ne : (p.transcript xy : Set (X × Y)) ≠ (R : Set (X × Y)) := by
    intro hset
    exact hne (Subtype.ext hset)
  have hdisjoint :=
    leafRectangles_disjoint p (p.transcript xy : Set (X × Y)) (R : Set (X × Y))
      (p.transcript xy).2 R.2 hset_ne
  exact hdisjoint.notMem_of_mem_left (mem_transcript p xy) hxy

/-- The protocol output is constant on any transcript leaf. -/
theorem run_eq_of_mem_transcript
    (p : Protocol X Y α) (xy xy' : X × Y)
    (hxy' : xy' ∈ (p.transcript xy : Set (X × Y))) :
    p.run xy.1 xy.2 = p.run xy'.1 xy'.2 := by
  exact
    leafRectangles_mono p p.run rfl (p.transcript xy : Set (X × Y)) (p.transcript xy).2
      xy.1 xy'.1 xy.2 xy'.2 (mem_transcript p xy) hxy'

/-- Inputs with the same transcript have the same protocol output. -/
theorem run_eq_of_transcript_eq
    (p : Protocol X Y α) {xy xy' : X × Y}
    (h : p.transcript xy = p.transcript xy') :
    p.run xy.1 xy.2 = p.run xy'.1 xy'.2 := by
  apply run_eq_of_mem_transcript p xy xy'
  rw [h]
  exact mem_transcript p xy'

/-- The transcript alphabet has at most one value for each protocol leaf, hence at most
`2 ^ p.complexity` values. -/
theorem card_leaf_le_two_pow_complexity (p : Protocol X Y α) :
    Fintype.card p.Leaf ≤ 2 ^ p.complexity := by
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  exact leafRectangles_card p

end Deterministic.Protocol

end CommunicationComplexity
