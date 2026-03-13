import CommunicationComplexity.Basic

/-- For finite input types, the deterministic communication complexity of any function
is at most `⌈log₂ |X|⌉ + ⌈log₂ |Y|⌉`, achieved by Alice sending her entire input
followed by Bob sending his. -/
theorem det_cc_le_clog_card {X Y α : Type} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    [DecidableEq X] [DecidableEq Y] (f : X → Y → α) :
    deterministic_communication_complexity f ≤ Nat.clog 2 (Fintype.card X) + Nat.clog 2 (Fintype.card Y) := by
  rw [show (↑(Nat.clog 2 (Fintype.card X)) + ↑(Nat.clog 2 (Fintype.card Y)) : WithTop ℕ) =
    ↑(Nat.clog 2 (Fintype.card X) + Nat.clog 2 (Fintype.card Y)) from (WithTop.coe_add _ _).symm]
  rw [det_cc_le_iff_generalized]
  -- Alice sends her input x, then Bob sends his input y, then output f x y
  refine ⟨DetProtocolGeneralized.alice id (fun x =>
    DetProtocolGeneralized.bob id (fun y =>
      DetProtocolGeneralized.output (f x y))), ?_, ?_⟩
  · -- run correctness: the protocol outputs f x y on inputs (x, y)
    ext x y; simp [DetProtocolGeneralized.run]
  · -- complexity: clog |X| + sup_x (clog |Y| + sup_y 0) = clog |X| + clog |Y|
    simp [DetProtocolGeneralized.complexity]
