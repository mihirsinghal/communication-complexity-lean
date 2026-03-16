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

private inductive TreeIsSubtree : Tree α → Tree α → Prop where
| refl  : ∀ t, TreeIsSubtree t t
| left  : ∀ s l r, TreeIsSubtree s l → TreeIsSubtree s (.node v l r)
| right : ∀ s l r, TreeIsSubtree s r → TreeIsSubtree s (.node v l r)

private lemma TreeIsSubtree.trans (h1 : TreeIsSubtree s t) (h2 : TreeIsSubtree t u) :
    TreeIsSubtree s u := by
  induction h2 with
  | refl t'             => exact h1
  | left s' l r hl ihl  => exact left s l r (ihl h1)
  | right s' l r hr ihr => exact right s l r (ihr h1)

private lemma tree_balanced_subtree_aux (t : Tree α) (n : ℕ) (hn : 1 < n)
    (h : 3 * t.numLeaves ≥ 2 * n) :
    ∃ (s : Tree α), TreeIsSubtree s t ∧
      3 * s.numLeaves ≥ n ∧ 3 * s.numLeaves < 2 * n := by
  induction t with
  | nil => simp [Tree.numLeaves] at h; omega
  | node _ l r ih_l ih_r =>
    by_cases hl : l.numLeaves ≥ r.numLeaves
    · by_cases hlt : 3 * l.numLeaves < 2 * n
      · exact ⟨l, TreeIsSubtree.left _ _ _ (TreeIsSubtree.refl _),
               by simp [Tree.numLeaves] at h; omega, hlt⟩
      · obtain ⟨s, hs, hlb, hub⟩ := ih_l (by omega)
        exact ⟨s, hs.trans (TreeIsSubtree.left _ _ _ (TreeIsSubtree.refl _)), hlb, hub⟩
    · by_cases hlt : 3 * r.numLeaves < 2 * n
      · exact ⟨r, TreeIsSubtree.right _ _ _ (TreeIsSubtree.refl _),
               by simp [Tree.numLeaves] at h; omega, hlt⟩
      · obtain ⟨s, hs, hlb, hub⟩ := ih_r (by omega)
        exact ⟨s, hs.trans (TreeIsSubtree.right _ _ _ (TreeIsSubtree.refl _)), hlb, hub⟩

/-- Lemma 1.8: every binary tree with > 1 leaves has a subtree with
    between n/3 and 2n/3 leaves (where n = total leaves). -/
theorem tree_balanced_subtree (t : Tree α) (hn : 1 < t.numLeaves) :
    ∃ s : Tree α, TreeIsSubtree s t ∧ 3 * s.numLeaves ≥ t.numLeaves ∧
         3 * s.numLeaves < 2 * t.numLeaves := by
  obtain ⟨v, l, r, rfl⟩ : ∃ v l r, t = Tree.node v l r := by
    match t with
    | .nil => simp [Tree.numLeaves] at hn
    | .node v l r => exact ⟨v, l, r, rfl⟩
  simp only [Tree.numLeaves] at *
  by_cases hl : l.numLeaves ≥ r.numLeaves
  · by_cases hlt : 3 * l.numLeaves < 2 * (l.numLeaves + r.numLeaves)
    · exact ⟨l, TreeIsSubtree.left _ _ _ (TreeIsSubtree.refl _), by omega, hlt⟩
    · obtain ⟨s, hs, hlb, hub⟩ :=
          tree_balanced_subtree_aux l (l.numLeaves + r.numLeaves) hn (by omega)
      exact ⟨s, hs.trans (TreeIsSubtree.left _ _ _ (TreeIsSubtree.refl _)), hlb, hub⟩
  · by_cases hlt : 3 * r.numLeaves < 2 * (l.numLeaves + r.numLeaves)
    · exact ⟨r, TreeIsSubtree.right _ _ _ (TreeIsSubtree.refl _), by omega, hlt⟩
    · obtain ⟨s, hs, hlb, hub⟩ :=
          tree_balanced_subtree_aux r (l.numLeaves + r.numLeaves) hn (by omega)
      exact ⟨s, hs.trans (TreeIsSubtree.right _ _ _ (TreeIsSubtree.refl _)), hlb, hub⟩

end CommunicationComplexity
