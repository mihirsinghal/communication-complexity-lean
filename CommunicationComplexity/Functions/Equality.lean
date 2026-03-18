import CommunicationComplexity.Basic
import CommunicationComplexity.Deterministic.UpperBounds
import CommunicationComplexity.Deterministic.Rectangle

namespace CommunicationComplexity

namespace Functions.Equality

/-- The equality function on `n`-bit strings. Returns `true` iff the two inputs are equal. -/
def equality (n : ℕ) (x y : Fin n → Bool) : Bool :=
  decide (x = y)

/-- The deterministic communication complexity of equality is at most n + 1:
Alice sends her n-bit input, Bob computes equality and sends one bit. -/
theorem communicationComplexity_le (n : ℕ) :
    Deterministic.communicationComplexity (equality n) ≤ n + 1 := by
  calc Deterministic.communicationComplexity (equality n)
      ≤ Nat.clog 2 (Nat.card (Fin n → Bool)) + Nat.clog 2 (Nat.card Bool) :=
        Deterministic.communicationComplexity_le_clog_card_X_alpha (equality n)
    _ = n + 1 := by
        simp only [Nat.card_eq_fintype_card, Fintype.card_pi, Fintype.card_bool,
          Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.one_lt_ofNat,
          Nat.clog_pow]
        norm_cast

/-- When n = 0, equality has communication complexity 0: both inputs are
the unique empty function, so the output is always `true`. -/
theorem communicationComplexity_zero :
    Deterministic.communicationComplexity (equality 0) = 0 := by
  apply le_antisymm
  · change Deterministic.communicationComplexity (equality 0) ≤ (0 : ℕ)
    rw [Deterministic.communicationComplexity_le_iff]
    exact ⟨Deterministic.Protocol.output true, by
      ext x y; simp [equality, Deterministic.Protocol.run, Subsingleton.elim x y],
      by simp [Deterministic.Protocol.complexity]⟩
  · exact bot_le

open Deterministic.Protocol Rectangle in
/-- The deterministic communication complexity of equality on n-bit strings
is at least n + 1 (for n ≥ 1). Any monochromatic rectangle containing
(x, x) must be {(x, x)}, so there are at least 2^n + 1 rectangles
in any partition, which requires n + 1 bits. -/
theorem le_communicationComplexity (n : ℕ) (hn : 1 ≤ n) :
    (n + 1 : ℕ) ≤ Deterministic.communicationComplexity (equality n) := by
  apply Deterministic.communicationComplexity_lower_bound
  intro Part hPart
  -- Each (x,x) is in some rectangle in Part
  choose rect hrect_mem hrect_in using fun x =>
    monoPartition_point_mem hPart (x, x)
  -- rect is injective: if rect x = rect y, then (x,x) and (y,y)
  -- are in the same rectangle, so (x,y) is too (cross_mem),
  -- and mono gives equality x x = equality x y, forcing x = y.
  have hrect_inj : Function.Injective rect := by
    intro x y hxy
    by_contra hne
    have hxy_mem := (monoPartition_cross_mem hPart (hrect_mem x)
      (hrect_in x) (hxy ▸ hrect_in y)).2
    have := monoPartition_values_eq hPart (hrect_mem x) (hrect_in x) hxy_mem
    simp [equality, hne] at this
  -- The image of rect has size 2^n
  have himage_card :
      Set.ncard (Set.range rect) = 2 ^ n := by
    rw [Set.ncard_range_of_injective hrect_inj]
    simp [Fintype.card_bool, Fintype.card_fin]
  -- Find a "false" rectangle containing (x0, y0) with x0 ≠ y0
  have hx : (fun _ : Fin n => true) ≠ (fun _ : Fin n => false) := by
    intro h; have := congr_fun h ⟨0, hn⟩; simp at this
  set x0 : Fin n → Bool := fun _ => true
  set y0 : Fin n → Bool := fun _ => false
  obtain ⟨R0, hR0_mem, hR0_in⟩ := monoPartition_point_mem hPart (x0, y0)
  -- R0 is not in the image of rect: any rect z is "true"-mono,
  -- but R0 contains (x0, y0) with equality x0 y0 = false.
  have hR0_not_diag : R0 ∉ Set.range rect := by
    rintro ⟨z, rfl⟩
    have := monoPartition_values_eq hPart (hrect_mem z) (hrect_in z) hR0_in
    simp [equality, hx] at this
  -- range rect ∪ {R0} ⊆ Part, giving 2^n < |Part|
  have hinsert : Set.range rect ∪ {R0} ⊆ Part :=
    Set.union_subset (fun R ⟨x, hx⟩ => hx ▸ hrect_mem x)
      (Set.singleton_subset_iff.mpr hR0_mem)
  calc 2 ^ n
      = Set.ncard (Set.range rect) := himage_card.symm
    _ < Set.ncard (Set.range rect ∪ {R0}) := by
        rw [Set.ncard_union_eq (Set.disjoint_singleton_right.mpr
          hR0_not_diag), Set.ncard_singleton]; omega
    _ ≤ Set.ncard Part :=
        Set.ncard_le_ncard hinsert (Set.toFinite Part)

/-- The exact deterministic communication complexity of equality on
`n`-bit strings: 0 when `n = 0`, and `n + 1` otherwise. -/
theorem communicationComplexity_eq (n : ℕ) :
    Deterministic.communicationComplexity (equality n) =
      if n = 0 then 0 else n + 1 := by
  split
  · next h => subst h; exact communicationComplexity_zero
  · next h =>
    apply le_antisymm (communicationComplexity_le n)
    exact le_communicationComplexity n (by omega)

end Functions.Equality

end CommunicationComplexity
