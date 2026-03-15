import CommunicationComplexity.Basic

namespace CommunicationComplexity

namespace Deterministic

/-- For finite input types, the deterministic communication complexity of any function
is at most `⌈log₂ |X|⌉ + ⌈log₂ |Y|⌉`, achieved by Alice sending her entire input
followed by Bob sending his. -/
theorem communicationComplexity_le_clog_card {X Y α : Type} [Finite X] [Finite Y] [Nonempty X] [Nonempty Y]
    (f : X → Y → α) :
    communicationComplexity f ≤
      Nat.clog 2 (Nat.card X) + Nat.clog 2 (Nat.card Y) := by
  haveI := Fintype.ofFinite X; haveI := Fintype.ofFinite Y
  rw [← Nat.cast_add, communicationComplexity_le_iff_finiteMessage]
  refine ⟨FiniteMessage.Protocol.alice id (fun x =>
    FiniteMessage.Protocol.bob id (fun y =>
      FiniteMessage.Protocol.output (f x y))), ?_, ?_⟩
  · ext x y; unfold FiniteMessage.Protocol.run; rfl
  · simp [FiniteMessage.Protocol.complexity, Nat.card_eq_fintype_card]

/-- The deterministic communication complexity of `f` is at most `⌈log₂ |X|⌉ + ⌈log₂ |α|⌉`,
achieved by Alice sending her input, then Bob computing and sending the output. -/
theorem communicationComplexity_le_clog_card_X_alpha {X Y α : Type} [Finite X] [Finite α] [Nonempty X] [Nonempty α]
    (f : X → Y → α) :
    communicationComplexity f ≤
      Nat.clog 2 (Nat.card X) + Nat.clog 2 (Nat.card α) := by
  haveI := Fintype.ofFinite X; haveI := Fintype.ofFinite α
  rw [← Nat.cast_add, communicationComplexity_le_iff_finiteMessage]
  refine ⟨FiniteMessage.Protocol.alice id (fun x =>
    FiniteMessage.Protocol.bob (f x) (fun a =>
      FiniteMessage.Protocol.output a)), ?_, ?_⟩
  · ext x y; unfold FiniteMessage.Protocol.run; rfl
  · simp [FiniteMessage.Protocol.complexity, Nat.card_eq_fintype_card]

/-- The deterministic communication complexity of `f` is at most `⌈log₂ |Y|⌉ + ⌈log₂ |α|⌉`,
achieved by Bob sending his input, then Alice computing and sending the output. -/
theorem communicationComplexity_le_clog_card_Y_alpha {X Y α : Type} [Finite Y] [Finite α] [Nonempty Y] [Nonempty α]
    (f : X → Y → α) :
    communicationComplexity f ≤
      Nat.clog 2 (Nat.card Y) + Nat.clog 2 (Nat.card α) := by
  haveI := Fintype.ofFinite Y; haveI := Fintype.ofFinite α
  rw [← Nat.cast_add, communicationComplexity_le_iff_finiteMessage]
  refine ⟨FiniteMessage.Protocol.bob id (fun y =>
    FiniteMessage.Protocol.alice (fun x => f x y) (fun a =>
      FiniteMessage.Protocol.output a)), ?_, ?_⟩
  · ext x y; unfold FiniteMessage.Protocol.run; rfl
  · simp [FiniteMessage.Protocol.complexity, Nat.card_eq_fintype_card]

end Deterministic

end CommunicationComplexity
