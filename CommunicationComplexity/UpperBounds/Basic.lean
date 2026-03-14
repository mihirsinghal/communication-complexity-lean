import CommunicationComplexity.Basic

/-- For finite input types, the deterministic communication complexity of any function
is at most `⌈log₂ |X|⌉ + ⌈log₂ |Y|⌉`, achieved by Alice sending her entire input
followed by Bob sending his. -/
theorem det_cc_le_clog_card {X Y α : Type} [Finite X] [Finite Y] [Nonempty X] [Nonempty Y]
    (f : X → Y → α) :
    deterministic_communication_complexity f ≤
      Nat.clog 2 (Nat.card X) + Nat.clog 2 (Nat.card Y) := by
  haveI := Fintype.ofFinite X; haveI := Fintype.ofFinite Y
  rw [← Nat.cast_add, det_cc_le_iff_generalized]
  refine ⟨DetProtocolGeneralized.alice id (fun x =>
    DetProtocolGeneralized.bob id (fun y =>
      DetProtocolGeneralized.output (f x y))), ?_, ?_⟩
  · ext x y; unfold DetProtocolGeneralized.run; rfl
  · simp [DetProtocolGeneralized.complexity, Nat.card_eq_fintype_card]

/-- The deterministic communication complexity of `f` is at most `⌈log₂ |X|⌉ + ⌈log₂ |α|⌉`,
achieved by Alice sending her input, then Bob computing and sending the output. -/
theorem det_cc_le_clog_card_X_alpha {X Y α : Type} [Finite X] [Finite α] [Nonempty X] [Nonempty α]
    (f : X → Y → α) :
    deterministic_communication_complexity f ≤
      Nat.clog 2 (Nat.card X) + Nat.clog 2 (Nat.card α) := by
  haveI := Fintype.ofFinite X; haveI := Fintype.ofFinite α
  rw [← Nat.cast_add, det_cc_le_iff_generalized]
  refine ⟨DetProtocolGeneralized.alice id (fun x =>
    DetProtocolGeneralized.bob (f x) (fun a =>
      DetProtocolGeneralized.output a)), ?_, ?_⟩
  · ext x y; unfold DetProtocolGeneralized.run; rfl
  · simp [DetProtocolGeneralized.complexity, Nat.card_eq_fintype_card]

/-- The deterministic communication complexity of `f` is at most `⌈log₂ |Y|⌉ + ⌈log₂ |α|⌉`,
achieved by Bob sending his input, then Alice computing and sending the output. -/
theorem det_cc_le_clog_card_Y_alpha {X Y α : Type} [Finite Y] [Finite α] [Nonempty Y] [Nonempty α]
    (f : X → Y → α) :
    deterministic_communication_complexity f ≤
      Nat.clog 2 (Nat.card Y) + Nat.clog 2 (Nat.card α) := by
  haveI := Fintype.ofFinite Y; haveI := Fintype.ofFinite α
  rw [← Nat.cast_add, det_cc_le_iff_generalized]
  refine ⟨DetProtocolGeneralized.bob id (fun y =>
    DetProtocolGeneralized.alice (fun x => f x y) (fun a =>
      DetProtocolGeneralized.output a)), ?_, ?_⟩
  · ext x y; unfold DetProtocolGeneralized.run; rfl
  · simp [DetProtocolGeneralized.complexity, Nat.card_eq_fintype_card]
