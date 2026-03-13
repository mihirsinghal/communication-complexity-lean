import CommunicationComplexity.Basic

/-- For finite input types, the deterministic communication complexity of any function
is at most `⌈log₂ |X|⌉ + ⌈log₂ |Y|⌉`, achieved by Alice sending her entire input
followed by Bob sending his. -/
theorem det_cc_le_clog_card {X Y α : Type} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
    (f : X → Y → α) :
    deterministic_communication_complexity f ≤ Nat.clog 2 (Fintype.card X) + Nat.clog 2 (Fintype.card Y) := by
  rw [show (↑(Nat.clog 2 (Fintype.card X)) + ↑(Nat.clog 2 (Fintype.card Y)) : WithTop ℕ) =
    ↑(Nat.clog 2 (Fintype.card X) + Nat.clog 2 (Fintype.card Y)) from (WithTop.coe_add _ _).symm]
  rw [det_cc_le_iff_generalized]
  -- Alice sends her input x, then Bob sends his input y, then output f x y
  refine ⟨DetProtocolGeneralized.alice id (fun x =>
    DetProtocolGeneralized.bob id (fun y =>
      DetProtocolGeneralized.output (f x y))), ?_, ?_⟩
  · -- run correctness: the protocol outputs f x y on inputs (x, y)
    ext x y; unfold DetProtocolGeneralized.run; rfl
  · -- complexity: clog |X| + sup_x (clog |Y| + sup_y 0) = clog |X| + clog |Y|
    simp [DetProtocolGeneralized.complexity]

/-- The deterministic communication complexity of `f` is at most `⌈log₂ |X|⌉ + ⌈log₂ |α|⌉`,
achieved by Alice sending her input, then Bob computing and sending the output. -/
theorem det_cc_le_clog_card_X_alpha {X Y α : Type} [Fintype X] [Fintype α] [Nonempty X] [Nonempty α]
    (f : X → Y → α) :
    deterministic_communication_complexity f ≤ Nat.clog 2 (Fintype.card X) + Nat.clog 2 (Fintype.card α) := by
  rw [show (↑(Nat.clog 2 (Fintype.card X)) + ↑(Nat.clog 2 (Fintype.card α)) : WithTop ℕ) =
    ↑(Nat.clog 2 (Fintype.card X) + Nat.clog 2 (Fintype.card α)) from (WithTop.coe_add _ _).symm]
  rw [det_cc_le_iff_generalized]
  -- Alice sends her input x, then Bob computes f x y and sends the result
  refine ⟨DetProtocolGeneralized.alice id (fun x =>
    DetProtocolGeneralized.bob (f x) (fun a =>
      DetProtocolGeneralized.output a)), ?_, ?_⟩
  · -- run correctness
    ext x y; unfold DetProtocolGeneralized.run; rfl
  · -- complexity: clog |X| + sup_x (clog |α| + sup_a 0) = clog |X| + clog |α|
    simp [DetProtocolGeneralized.complexity]

/-- The deterministic communication complexity of `f` is at most `⌈log₂ |Y|⌉ + ⌈log₂ |α|⌉`,
achieved by Bob sending his input, then Alice computing and sending the output. -/
theorem det_cc_le_clog_card_Y_alpha {X Y α : Type} [Fintype Y] [Fintype α] [Nonempty Y] [Nonempty α]
    (f : X → Y → α) :
    deterministic_communication_complexity f ≤ Nat.clog 2 (Fintype.card Y) + Nat.clog 2 (Fintype.card α) := by
  rw [show (↑(Nat.clog 2 (Fintype.card Y)) + ↑(Nat.clog 2 (Fintype.card α)) : WithTop ℕ) =
    ↑(Nat.clog 2 (Fintype.card Y) + Nat.clog 2 (Fintype.card α)) from (WithTop.coe_add _ _).symm]
  rw [det_cc_le_iff_generalized]
  -- Bob sends his input y, then Alice computes f x y and sends the result
  refine ⟨DetProtocolGeneralized.bob id (fun y =>
    DetProtocolGeneralized.alice (fun x => f x y) (fun a =>
      DetProtocolGeneralized.output a)), ?_, ?_⟩
  · -- run correctness
    ext x y; unfold DetProtocolGeneralized.run; rfl
  · -- complexity: clog |Y| + sup_y (clog |α| + sup_a 0) = clog |Y| + clog |α|
    simp [DetProtocolGeneralized.complexity]
