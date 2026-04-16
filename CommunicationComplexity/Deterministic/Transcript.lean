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

open Classical in
/-- Swapping Alice and Bob gives an equivalence between the transcript alphabets. -/
noncomputable def leafSwap (p : Protocol X Y α) : p.Leaf ≃ p.swap.Leaf where
  toFun R :=
    ⟨swapInputSet R.1, swapInputSet_mem_leafRectangles_swap p R.2⟩
  invFun R :=
    ⟨swapInputSet R.1, by
      have h := swapInputSet_mem_leafRectangles_swap p.swap R.2
      simpa using h⟩
  left_inv R := by
    apply Subtype.ext
    simp
  right_inv R := by
    apply Subtype.ext
    simp

/-- Pull a transcript leaf back along maps on Alice's and Bob's inputs. -/
def leafComap (p : Protocol X Y α) (fX : X' → X) (fY : Y' → Y) :
    p.Leaf → (p.comap fX fY).Leaf :=
  fun R => ⟨preimageInputSet fX fY R.1,
    preimageInputSet_mem_leafRectangles_comap p fX fY R.2⟩

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

open Classical in
/-- The output associated to a transcript leaf. Empty leaf rectangles are assigned `default`;
on nonempty leaves this is the protocol output on any input in the leaf. -/
noncomputable def leafOutput [Inhabited α] (p : Protocol X Y α) (R : p.Leaf) : α :=
  if h : ∃ xy : X × Y, xy ∈ (R : Set (X × Y)) then
    p.run (Classical.choose h).1 (Classical.choose h).2
  else
    default

open Classical in
/-- Every input in a transcript leaf has that leaf's output. -/
theorem run_eq_leafOutput_of_mem_leaf [Inhabited α]
    (p : Protocol X Y α) (R : p.Leaf) {xy : X × Y}
    (hxy : xy ∈ (R : Set (X × Y))) :
    p.run xy.1 xy.2 = p.leafOutput R := by
  rw [leafOutput]
  have hnonempty : ∃ xy : X × Y, xy ∈ (R : Set (X × Y)) := ⟨xy, hxy⟩
  rw [dif_pos hnonempty]
  exact
    leafRectangles_mono p p.run rfl (R : Set (X × Y)) R.2
      xy.1 (Classical.choose hnonempty).1 xy.2 (Classical.choose hnonempty).2 hxy
      (Classical.choose_spec hnonempty)

/-- The transcript alphabet has at most one value for each protocol leaf, hence at most
`2 ^ p.complexity` values. -/
theorem card_leaf_le_two_pow_complexity (p : Protocol X Y α) :
    Fintype.card p.Leaf ≤ 2 ^ p.complexity := by
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  exact leafRectangles_card p

/-- Swapping a protocol sends the transcript of `(x, y)` to the swapped transcript leaf of
`(y, x)`. -/
theorem leafSwap_transcript (p : Protocol X Y α) (x : X) (y : Y) :
    leafSwap p (p.transcript (x, y)) = p.swap.transcript (y, x) := by
  symm
  apply transcript_eq_of_mem_leaf p.swap
  change (y, x) ∈ swapInputSet ((p.transcript (x, y) : p.Leaf) : Set (X × Y))
  simp [mem_transcript]

/-- Set-level version of `leafSwap_transcript`. -/
theorem swapInputSet_transcript (p : Protocol X Y α) (x : X) (y : Y) :
    swapInputSet ((p.transcript (x, y) : p.Leaf) : Set (X × Y)) =
      ((p.swap.transcript (y, x) : p.swap.Leaf) : Set (Y × X)) := by
  exact congrArg Subtype.val (leafSwap_transcript p x y)

/-- Pulling back a protocol sends the transcript of the mapped input to the transcript of the
original input under the pulled-back protocol. -/
theorem leafComap_transcript (p : Protocol X Y α) (fX : X' → X) (fY : Y' → Y)
    (x' : X') (y' : Y') :
    leafComap p fX fY (p.transcript (fX x', fY y')) =
      (p.comap fX fY).transcript (x', y') := by
  symm
  apply transcript_eq_of_mem_leaf (p.comap fX fY)
  change (x', y') ∈
    preimageInputSet fX fY ((p.transcript (fX x', fY y') : p.Leaf) : Set (X × Y))
  simp [mem_transcript]

end Deterministic.Protocol

end CommunicationComplexity
