import CommunicationComplexity.Basic
import CommunicationComplexity.Deterministic.UpperBounds
import CommunicationComplexity.Deterministic.Rectangle
import Mathlib.Data.Set.SymmDiff
import Mathlib.Data.Fintype.Powerset

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
  intro R hR hmono p hp q hq
  rcases p with ⟨X, Y⟩
  rcases q with ⟨X', Y'⟩
  simp only [foolingSet, Set.mem_inter_iff, Set.mem_setOf_eq] at hp hq
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
        simp only [ne_eq, decide_eq_true_eq]
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
        simp only [ne_eq, decide_eq_true_eq]
        intro hdisj
        rw [Set.disjoint_left] at hdisj
        exact hdisj hi.1 hi.2
      rw [htrue] at hval
      exact (hne hval.symm).elim

/-- The fooling set for disjointness has size `2^n`. -/
theorem foolingSet_card (n : ℕ) :
    Set.ncard (foolingSet n) = 2 ^ n := by
  let f : Set (Fin n) → Set (Fin n) × Set (Fin n) := fun X => (X, Xᶜ)
  have hf : Function.Injective f := by
    intro X X' h
    exact congrArg Prod.fst h
  calc Set.ncard (foolingSet n)
      = Set.ncard (Set.range f) := by
          congr
          ext p
          rcases p with ⟨X, Y⟩
          simp [f, foolingSet, eq_comm]
    _ = 2 ^ n := by
          simpa [Nat.card_eq_fintype_card, Fintype.card_set, Fintype.card_fin] using
            Set.ncard_range_of_injective hf

/-- The deterministic communication complexity of disjointness is at most `n + 1`:
Alice sends her set, and Bob sends one bit for the answer. -/
theorem communicationComplexity_le (n : ℕ) :
    Deterministic.communicationComplexity (disjointness n) ≤ n + 1 := by
  calc Deterministic.communicationComplexity (disjointness n)
      ≤ Nat.clog 2 (Nat.card (Set (Fin n))) + Nat.clog 2 (Nat.card Bool) :=
        Deterministic.communicationComplexity_le_clog_card_X_alpha (disjointness n)
    _ = n + 1 := by
        have hbool : Nat.clog 2 2 = 1 := by decide
        simp only [Nat.card_eq_fintype_card, Fintype.card_set, Fintype.card_fin,
          Fintype.card_bool, Nat.one_lt_ofNat, Nat.clog_pow]
        rw [hbool]
        norm_num

end Functions.Disjointness

end CommunicationComplexity
