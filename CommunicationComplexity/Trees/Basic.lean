import Mathlib.Data.Tree.Basic
import CommunicationComplexity.Deterministic.Basic

namespace CommunicationComplexity

variable {X Y α : Type*}

namespace Deterministic.Protocol

def shape : Protocol X Y α → Tree Unit
| .output _  => .nil
| .alice _ P => .node () (shape (P false)) (shape (P true))
| .bob   _ P => .node () (shape (P false)) (shape (P true))

/-- The number of leaves (output nodes) in a protocol, defined via its tree shape. -/
def numLeaves (p : Protocol X Y α) : ℕ := p.shape.numLeaves

end Deterministic.Protocol

namespace TreeLemma

private inductive IsSubtree : _root_.Tree α → _root_.Tree α → Prop where
| refl  : ∀ t, IsSubtree t t
| left  : ∀ s l r, IsSubtree s l → IsSubtree s (.node v l r)
| right : ∀ s l r, IsSubtree s r → IsSubtree s (.node v l r)

private lemma IsSubtree.trans (h1 : IsSubtree s t) (h2 : IsSubtree t u) :
    IsSubtree s u := by
  induction h2 with
  | refl t'             => exact h1
  | left s' l r hl ihl  => exact left s l r (ihl h1)
  | right s' l r hr ihr => exact right s l r (ihr h1)

private lemma balanced_aux (t : _root_.Tree α) (n : ℕ) (hn : 1 < n)
    (h : 3 * t.numLeaves ≥ 2 * n) :
    ∃ (s : _root_.Tree α), IsSubtree s t ∧
      3 * s.numLeaves ≥ n ∧ 3 * s.numLeaves < 2 * n := by
  induction t with
  | nil => simp [_root_.Tree.numLeaves] at h; omega
  | node _ l r ih_l ih_r =>
    by_cases hl : l.numLeaves ≥ r.numLeaves
    · by_cases hlt : 3 * l.numLeaves < 2 * n
      · exact ⟨l, IsSubtree.left _ _ _ (IsSubtree.refl _),
               by simp [_root_.Tree.numLeaves] at h; omega, hlt⟩
      · obtain ⟨s, hs, hlb, hub⟩ := ih_l (by omega)
        exact ⟨s, hs.trans (IsSubtree.left _ _ _ (IsSubtree.refl _)), hlb, hub⟩
    · by_cases hlt : 3 * r.numLeaves < 2 * n
      · exact ⟨r, IsSubtree.right _ _ _ (IsSubtree.refl _),
               by simp [_root_.Tree.numLeaves] at h; omega, hlt⟩
      · obtain ⟨s, hs, hlb, hub⟩ := ih_r (by omega)
        exact ⟨s, hs.trans (IsSubtree.right _ _ _ (IsSubtree.refl _)), hlb, hub⟩

/-- Lemma 1.8: every binary tree with > 1 leaves has a subtree with
    between n/3 and 2n/3 leaves (where n = total leaves). -/
theorem balanced_subtree (t : _root_.Tree α) (hn : 1 < t.numLeaves) :
    ∃ s : _root_.Tree α, IsSubtree s t ∧ 3 * s.numLeaves ≥ t.numLeaves ∧
         3 * s.numLeaves < 2 * t.numLeaves := by
  obtain ⟨v, l, r, rfl⟩ : ∃ v l r, t = _root_.Tree.node v l r := by
    match t with
    | .nil => simp [_root_.Tree.numLeaves] at hn
    | .node v l r => exact ⟨v, l, r, rfl⟩
  simp only [_root_.Tree.numLeaves] at *
  by_cases hl : l.numLeaves ≥ r.numLeaves
  · by_cases hlt : 3 * l.numLeaves < 2 * (l.numLeaves + r.numLeaves)
    · exact ⟨l, IsSubtree.left _ _ _ (IsSubtree.refl _), by omega, hlt⟩
    · obtain ⟨s, hs, hlb, hub⟩ :=
          balanced_aux l (l.numLeaves + r.numLeaves) hn (by omega)
      exact ⟨s, hs.trans (IsSubtree.left _ _ _ (IsSubtree.refl _)), hlb, hub⟩
  · by_cases hlt : 3 * r.numLeaves < 2 * (l.numLeaves + r.numLeaves)
    · exact ⟨r, IsSubtree.right _ _ _ (IsSubtree.refl _), by omega, hlt⟩
    · obtain ⟨s, hs, hlb, hub⟩ :=
          balanced_aux r (l.numLeaves + r.numLeaves) hn (by omega)
      exact ⟨s, hs.trans (IsSubtree.right _ _ _ (IsSubtree.refl _)), hlb, hub⟩

end TreeLemma

end CommunicationComplexity
