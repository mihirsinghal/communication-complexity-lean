import CommunicationComplexity.Rectangle.Basic
import Mathlib.Data.Set.SymmDiff

namespace CommunicationComplexity

namespace Functions.Disjointness

open Rectangle
open scoped symmDiff

/-- The set disjointness function on subsets of `[n]`. -/
noncomputable def disjointness (n : ℕ) (X Y : Set (Fin n)) : Bool :=
  by
    classical
    exact decide (Disjoint X Y)

/-- The candidate fooling set for disjointness: pairs `(X, Xᶜ)`. -/
def foolingSet (n : ℕ) : Set (Set (Fin n) × Set (Fin n)) :=
  {p | p.2 = p.1ᶜ}

/-- Claim 1.21: the pairs `(X, Xᶜ)` form a fooling set for disjointness. -/
theorem foolingSet_isFoolingSet (n : ℕ) :
    IsFoolingSet (foolingSet n) (disjointness n) := by
  intro R hR hmono
  intro p hp q hq
  rcases p with ⟨X, Y⟩
  rcases q with ⟨X', Y'⟩
  simp [foolingSet] at hp hq
  rcases hp with ⟨rfl, hpR⟩
  rcases hq with ⟨rfl, hqR⟩
  by_cases hXX' : X = X'
  · subst hXX'
    rfl
  · have hcross := (IsRectangle_iff R).mp hR X X' Xᶜ X'ᶜ hpR hqR
    obtain ⟨i, hi⟩ : (X ∆ X').Nonempty := Set.symmDiff_nonempty.mpr hXX'
    rw [Set.mem_symmDiff] at hi
    rcases hi with hi | hi
    · have hval := hmono X X Xᶜ X'ᶜ hpR hcross.2
      have htrue : disjointness n X Xᶜ = true := by
        simpa [disjointness] using (disjoint_compl_right : Disjoint X Xᶜ)
      have hne : disjointness n X X'ᶜ ≠ true := by
        unfold disjointness
        simp
        intro hdisj
        rw [Set.disjoint_left] at hdisj
        exact hdisj hi.1 hi.2
      rw [htrue] at hval
      exact (hne hval.symm).elim
    · have hval := hmono X' X' X'ᶜ Xᶜ hqR hcross.1
      have htrue : disjointness n X' X'ᶜ = true := by
        simpa [disjointness] using (disjoint_compl_right : Disjoint X' X'ᶜ)
      have hne : disjointness n X' Xᶜ ≠ true := by
        unfold disjointness
        simp
        intro hdisj
        rw [Set.disjoint_left] at hdisj
        exact hdisj hi.1 hi.2
      rw [htrue] at hval
      exact (hne hval.symm).elim

end Functions.Disjointness

end CommunicationComplexity
