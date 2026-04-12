import CommunicationComplexity.Functions.Disjointness

namespace CommunicationComplexity

namespace Functions.Disjointness

open Deterministic.Protocol Rectangle in
/-- For `n ≥ 1`, disjointness on subsets of `[n]` has deterministic
communication complexity at least `n + 1`. -/
theorem le_communicationComplexity (n : ℕ) (hn : 1 ≤ n) :
    (n + 1 : ℕ) ≤ Deterministic.communicationComplexity (disjointness n) := by
  apply Deterministic.communicationComplexity_lower_bound
  intro Part hPart
  choose rect hrect_mem hrect_in using fun X : Set (Fin n) =>
    monoPartition_point_mem hPart (X, Xᶜ)
  have hrect_inj : Function.Injective rect := by
    intro X X' hXX
    have hsub :=
      foolingSet_isFoolingSet n (rect X) (hPart.1 _ (hrect_mem X)) (hPart.2.1 _ (hrect_mem X))
    have hp : (X, Xᶜ) ∈ foolingSet n ∩ rect X := by
      simp [foolingSet, hrect_in X]
    have hq : (X', X'ᶜ) ∈ foolingSet n ∩ rect X := by
      simp [foolingSet, hXX ▸ hrect_in X']
    exact congrArg Prod.fst (hsub hp hq)
  have himage_card :
      Set.ncard (Set.range rect) = 2 ^ n := by
    simpa [Fintype.card_set, Fintype.card_fin] using
      Set.ncard_range_of_injective hrect_inj
  let i0 : Fin n := ⟨0, hn⟩
  let x0 : Set (Fin n) := {i0}
  let y0 : Set (Fin n) := {i0}
  obtain ⟨R0, hR0_mem, hR0_in⟩ := monoPartition_point_mem hPart (x0, y0)
  have hR0_not_diag : R0 ∉ Set.range rect := by
    rintro ⟨X, rfl⟩
    have hval := monoPartition_values_eq hPart (hrect_mem X) (hrect_in X) hR0_in
    have htrue : disjointness n X Xᶜ = true := by
      simpa [disjointness] using (disjoint_compl_right : Disjoint X Xᶜ)
    have hne : disjointness n x0 y0 ≠ true := by
      unfold disjointness
      simp only [ne_eq, decide_eq_true_eq]
      intro hdisj
      rw [Set.disjoint_left] at hdisj
      have hnot : i0 ∉ y0 := hdisj (by simp [x0])
      exact hnot (by simp [y0])
    rw [htrue] at hval
    exact (hne hval.symm).elim
  have hinsert : insert R0 (Set.range rect) ⊆ Part :=
    Set.insert_subset hR0_mem (fun R ⟨X, hX⟩ => hX ▸ hrect_mem X)
  calc 2 ^ n
      = Set.ncard (Set.range rect) := himage_card.symm
    _ < Set.ncard (insert R0 (Set.range rect)) := by
        rw [Set.ncard_insert_of_notMem hR0_not_diag, himage_card]
        omega
    _ ≤ Set.ncard Part :=
        Set.ncard_le_ncard hinsert (Set.toFinite Part)

/-- For `n ≥ 1`, the deterministic communication complexity of
disjointness on subsets of `[n]` is exactly `n + 1`. -/
theorem communicationComplexity_eq (n : ℕ) (hn : 1 ≤ n) :
    Deterministic.communicationComplexity (disjointness n) = n + 1 := by
  apply le_antisymm (communicationComplexity_le n)
  exact le_communicationComplexity n hn

end Functions.Disjointness

end CommunicationComplexity
