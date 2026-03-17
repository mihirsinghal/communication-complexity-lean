import Mathlib.Data.ENat.Lattice
import CommunicationComplexity.Deterministic.Basic
import CommunicationComplexity.Deterministic.FiniteMessage

namespace CommunicationComplexity

namespace Internal

@[simp]
theorem enat_iInf_le_coe_iff {ι : Sort*} {f : ι → ENat} {n : ℕ} :
    iInf f ≤ ↑n ↔ ∃ i, f i ≤ ↑n := by
  constructor
  · intro h
    by_contra hne
    push_neg at hne
    apply not_lt.mpr h
    have : ∀ i, (↑(n + 1) : ENat) ≤ f i := fun i => by
      match f i, hne i with
      | none, _ => exact le_top
      | some m, hi =>
        exact WithTop.coe_le_coe.mpr
          (Nat.succ_le_of_lt (WithTop.coe_lt_coe.mp hi))
    exact lt_of_lt_of_le
      (WithTop.coe_lt_coe.mpr (Nat.lt_succ_self n))
      (le_iInf this)
  · rintro ⟨i, hi⟩
    exact (iInf_le f i).trans hi

end Internal

namespace Deterministic

noncomputable def communicationComplexity
    {X Y α} (f : X → Y → α) : ENat :=
  ⨅ (p : Protocol X Y α) (_ : p.computes f),
    (p.complexity : ENat)

theorem communicationComplexity_le_iff
    {X Y α} (f : X → Y → α) (n : ℕ) :
    communicationComplexity f ≤ n ↔
      ∃ p : Protocol X Y α,
        p.computes f ∧ p.complexity ≤ n := by
  simp only [communicationComplexity,
    Internal.enat_iInf_le_coe_iff, Nat.cast_le, exists_prop]

theorem communicationComplexity_le_iff_finiteMessage
    {X Y α} (f : X → Y → α) (n : ℕ) :
    communicationComplexity f ≤ n ↔
      ∃ p : FiniteMessage.Protocol X Y α,
        p.run = f ∧ p.complexity ≤ n := by
  rw [communicationComplexity_le_iff]
  constructor
  · rintro ⟨p, hp, hc⟩
    obtain ⟨P, hP_run, hP_comp⟩ :=
      FiniteMessage.Protocol.ofProtocol_equiv p
    exact ⟨P, hP_run.trans hp, hP_comp ▸ hc⟩
  · rintro ⟨p, hp, hc⟩
    obtain ⟨P, hP_run, hP_comp⟩ :=
      FiniteMessage.Protocol.toProtocol p
    exact ⟨P, hP_run.trans hp, hP_comp ▸ hc⟩

theorem le_communicationComplexity_iff
    {X Y α} (f : X → Y → α) (n : ℕ) :
    (n : ENat) ≤ communicationComplexity f ↔
      ∀ p : Protocol X Y α,
        p.computes f → n ≤ p.complexity := by
  simp only [communicationComplexity,
    le_iInf_iff, Nat.cast_le]

end Deterministic

end CommunicationComplexity
