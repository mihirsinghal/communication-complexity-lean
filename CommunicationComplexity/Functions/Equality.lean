import CommunicationComplexity.Basic
import CommunicationComplexity.UpperBounds.Basic
import CommunicationComplexity.LowerBounds.Rectangles

/-- The equality function on `n`-bit strings. Returns `true` iff the two inputs are equal. -/
def EQ (n : ℕ) (x y : Fin n → Bool) : Bool :=
  decide (x = y)

/-- The deterministic communication complexity of EQ is at most n + 1:
Alice sends her n-bit input, Bob computes equality and sends one bit. -/
theorem det_cc_EQ_le (n : ℕ) :
    deterministic_communication_complexity (EQ n) ≤ n + 1 := by
  calc deterministic_communication_complexity (EQ n)
      ≤ Nat.clog 2 (Fintype.card (Fin n → Bool)) + Nat.clog 2 (Fintype.card Bool) :=
        det_cc_le_clog_card_X_alpha (EQ n)
    _ = n + 1 := by
        simp only [Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, Nat.one_lt_ofNat, Nat.clog_pow, ne_eq, WithTop.natCast_ne_top,
          not_false_eq_true, add_right_inj_of_ne_top, Nat.cast_eq_one]
        decide

/-- When n = 0, EQ has communication complexity 0: both inputs are
the unique empty function, so the output is always `true`. -/
theorem det_cc_EQ_zero :
    deterministic_communication_complexity (EQ 0) = 0 := by
  apply le_antisymm
  · change deterministic_communication_complexity (EQ 0) ≤ (0 : ℕ)
    rw [det_cc_le_iff]
    exact ⟨DetProtocol.output true, by
      ext x y; simp [EQ, DetProtocol.run, Subsingleton.elim x y],
      by simp [DetProtocol.complexity]⟩
  · exact bot_le

open DetProtocol in
/-- The deterministic communication complexity of EQ on n-bit strings
is at least n + 1 (for n ≥ 1). Any monochromatic rectangle containing
(x, x) must be {(x, x)}, so there are at least 2^n + 1 rectangles
in any partition, which requires n + 1 bits. -/
theorem le_det_cc_EQ (n : ℕ) (hn : 1 ≤ n) :
    (n + 1 : ℕ) ≤ deterministic_communication_complexity (EQ n) := by
  apply det_cc_lower_bound
  intro Part hPart
  -- Each (x,x) is in some rectangle in Part
  choose rect hrect_mem hrect_in using fun x =>
    hPart.exists_mem (x, x)
  -- rect is injective: if rect x = rect y, then (x,x) and (y,y)
  -- are in the same rectangle, so (x,y) is too (cross_mem),
  -- and mono gives EQ x x = EQ x y, forcing x = y.
  have hrect_inj : Function.Injective rect := by
    intro x y hxy
    by_contra hne
    have hxy_mem := (hPart.cross_mem (hrect_mem x)
      (hrect_in x) (hxy ▸ hrect_in y)).2
    have := hPart.apply_eq (hrect_mem x) (hrect_in x) hxy_mem
    simp [EQ, hne] at this
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
  obtain ⟨R0, hR0_mem, hR0_in⟩ := hPart.exists_mem (x0, y0)
  -- R0 is not in the image of rect: any rect z is "true"-mono,
  -- but R0 contains (x0, y0) with EQ x0 y0 = false.
  have hR0_not_diag : R0 ∉ Set.range rect := by
    rintro ⟨z, rfl⟩
    have := hPart.apply_eq (hrect_mem z) (hrect_in z) hR0_in
    simp [EQ, hx] at this
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

/-- The exact deterministic communication complexity of EQ on
`n`-bit strings: 0 when `n = 0`, and `n + 1` otherwise. -/
theorem det_cc_EQ (n : ℕ) :
    deterministic_communication_complexity (EQ n) =
      if n = 0 then 0 else n + 1 := by
  split
  · next h => subst h; exact det_cc_EQ_zero
  · next h =>
    apply le_antisymm (det_cc_EQ_le n)
    exact le_det_cc_EQ n (by omega)
