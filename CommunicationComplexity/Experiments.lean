import CommunicationComplexity.LowerBounds.Rectangles
import CommunicationComplexity.Trees.Basic

namespace DetProtocol

variable {X Y α : Type*}

/-- `IsSubprotocol s p` means `s` is a (rooted) subtree of protocol `p`. -/
inductive IsSubprotocol : DetProtocol X Y α → DetProtocol X Y α → Prop where
| refl : ∀ p, IsSubprotocol p p
| alice_false : ∀ f P s, IsSubprotocol s (P false) → IsSubprotocol s (DetProtocol.alice f P)
| alice_true  : ∀ f P s, IsSubprotocol s (P true)  → IsSubprotocol s (DetProtocol.alice f P)
| bob_false   : ∀ f P s, IsSubprotocol s (P false) → IsSubprotocol s (DetProtocol.bob f P)
| bob_true    : ∀ f P s, IsSubprotocol s (P true)  → IsSubprotocol s (DetProtocol.bob f P)

lemma IsSubprotocol.trans
    {s t u : DetProtocol X Y α}
    (h1 : IsSubprotocol s t) (h2 : IsSubprotocol t u) : IsSubprotocol s u := by
  induction h2 with
  | refl _ => exact h1
  | alice_false f P t ht ih => exact IsSubprotocol.alice_false f P s (ih h1)
  | alice_true f P t ht ih => exact IsSubprotocol.alice_true f P s (ih h1)
  | bob_false f P t ht ih => exact IsSubprotocol.bob_false f P s (ih h1)
  | bob_true f P t ht ih => exact IsSubprotocol.bob_true f P s (ih h1)

private lemma balanced_aux (p : DetProtocol X Y α) (n : ℕ) (hn : 1 < n)
    (h : 3 * p.numLeaves ≥ 2 * n) :
    ∃ s : DetProtocol X Y α,
      IsSubprotocol s p ∧ 3 * s.numLeaves ≥ n ∧ 3 * s.numLeaves < 2 * n := by
  induction p with
  | output v =>
    simp [DetProtocol.numLeaves, DetProtocol.shape] at h
    omega
  | alice f P ih =>
    have hsum : (DetProtocol.alice f P).numLeaves =
        (P false).numLeaves + (P true).numLeaves := by
      simp [DetProtocol.numLeaves, DetProtocol.shape]
    have htot : 3 * ((P false).numLeaves + (P true).numLeaves) ≥ 2 * n := by
      simpa [hsum] using h
    by_cases hcmp : (P false).numLeaves ≥ (P true).numLeaves
    · by_cases hlt : 3 * (P false).numLeaves < 2 * n
      · refine ⟨P false, IsSubprotocol.alice_false f P (P false) (IsSubprotocol.refl _), ?_, hlt⟩
        omega
      · have hchild : 3 * (P false).numLeaves ≥ 2 * n := by omega
        obtain ⟨s, hs, hs1, hs2⟩ := ih false hchild
        exact ⟨s, hs.trans (IsSubprotocol.alice_false f P (P false) (IsSubprotocol.refl _)), hs1, hs2⟩
    · by_cases hlt : 3 * (P true).numLeaves < 2 * n
      · refine ⟨P true, IsSubprotocol.alice_true f P (P true) (IsSubprotocol.refl _), ?_, hlt⟩
        omega
      · have hchild : 3 * (P true).numLeaves ≥ 2 * n := by omega
        obtain ⟨s, hs, hs1, hs2⟩ := ih true hchild
        exact ⟨s, hs.trans (IsSubprotocol.alice_true f P (P true) (IsSubprotocol.refl _)), hs1, hs2⟩
  | bob f P ih =>
    have hsum : (DetProtocol.bob f P).numLeaves =
        (P false).numLeaves + (P true).numLeaves := by
      simp [DetProtocol.numLeaves, DetProtocol.shape]
    have htot : 3 * ((P false).numLeaves + (P true).numLeaves) ≥ 2 * n := by
      simpa [hsum] using h
    by_cases hcmp : (P false).numLeaves ≥ (P true).numLeaves
    · by_cases hlt : 3 * (P false).numLeaves < 2 * n
      · refine ⟨P false, IsSubprotocol.bob_false f P (P false) (IsSubprotocol.refl _), ?_, hlt⟩
        omega
      · have hchild : 3 * (P false).numLeaves ≥ 2 * n := by omega
        obtain ⟨s, hs, hs1, hs2⟩ := ih false hchild
        exact ⟨s, hs.trans (IsSubprotocol.bob_false f P (P false) (IsSubprotocol.refl _)), hs1, hs2⟩
    · by_cases hlt : 3 * (P true).numLeaves < 2 * n
      · refine ⟨P true, IsSubprotocol.bob_true f P (P true) (IsSubprotocol.refl _), ?_, hlt⟩
        omega
      · have hchild : 3 * (P true).numLeaves ≥ 2 * n := by omega
        obtain ⟨s, hs, hs1, hs2⟩ := ih true hchild
        exact ⟨s, hs.trans (IsSubprotocol.bob_true f P (P true) (IsSubprotocol.refl _)), hs1, hs2⟩

/-- Protocol-level version of Lemma 1.8. -/
theorem balanced_subprotocol (p : DetProtocol X Y α) (hn : 1 < p.numLeaves) :
    ∃ s : DetProtocol X Y α,
      IsSubprotocol s p ∧ 3 * s.numLeaves ≥ p.numLeaves ∧
      3 * s.numLeaves < 2 * p.numLeaves := by
  induction p with
  | output v =>
    simp [DetProtocol.numLeaves, DetProtocol.shape] at hn
  | alice f P ih =>
    have hsum : (DetProtocol.alice f P).numLeaves =
        (P false).numLeaves + (P true).numLeaves := by
      simp [DetProtocol.numLeaves, DetProtocol.shape]
    have hn' : 1 < (P false).numLeaves + (P true).numLeaves := by
      simpa [hsum] using hn
    by_cases hcmp : (P false).numLeaves ≥ (P true).numLeaves
    · by_cases hlt : 3 * (P false).numLeaves < 2 * ((P false).numLeaves + (P true).numLeaves)
      · refine ⟨P false, IsSubprotocol.alice_false f P (P false) (IsSubprotocol.refl _), ?_, ?_⟩
        · simpa [hsum] using (show 3 * (P false).numLeaves ≥ (P false).numLeaves + (P true).numLeaves by omega)
        · simpa [hsum] using hlt
      · obtain ⟨s, hs, hs1, hs2⟩ :=
          balanced_aux (P false) ((P false).numLeaves + (P true).numLeaves) hn' (by omega)
        refine ⟨s, hs.trans (IsSubprotocol.alice_false f P (P false) (IsSubprotocol.refl _)), hs1, ?_⟩
        simpa [hsum] using hs2
    · by_cases hlt : 3 * (P true).numLeaves < 2 * ((P false).numLeaves + (P true).numLeaves)
      · refine ⟨P true, IsSubprotocol.alice_true f P (P true) (IsSubprotocol.refl _), ?_, ?_⟩
        · simpa [hsum] using (show 3 * (P true).numLeaves ≥ (P false).numLeaves + (P true).numLeaves by omega)
        · simpa [hsum] using hlt
      · obtain ⟨s, hs, hs1, hs2⟩ :=
          balanced_aux (P true) ((P false).numLeaves + (P true).numLeaves) hn' (by omega)
        refine ⟨s, hs.trans (IsSubprotocol.alice_true f P (P true) (IsSubprotocol.refl _)), hs1, ?_⟩
        simpa [hsum] using hs2
  | bob f P ih =>
    have hsum : (DetProtocol.bob f P).numLeaves =
        (P false).numLeaves + (P true).numLeaves := by
      simp [DetProtocol.numLeaves, DetProtocol.shape]
    have hn' : 1 < (P false).numLeaves + (P true).numLeaves := by
      simpa [hsum] using hn
    by_cases hcmp : (P false).numLeaves ≥ (P true).numLeaves
    · by_cases hlt : 3 * (P false).numLeaves < 2 * ((P false).numLeaves + (P true).numLeaves)
      · refine ⟨P false, IsSubprotocol.bob_false f P (P false) (IsSubprotocol.refl _), ?_, ?_⟩
        · simpa [hsum] using (show 3 * (P false).numLeaves ≥ (P false).numLeaves + (P true).numLeaves by omega)
        · simpa [hsum] using hlt
      · obtain ⟨s, hs, hs1, hs2⟩ :=
          balanced_aux (P false) ((P false).numLeaves + (P true).numLeaves) hn' (by omega)
        refine ⟨s, hs.trans (IsSubprotocol.bob_false f P (P false) (IsSubprotocol.refl _)), hs1, ?_⟩
        simpa [hsum] using hs2
    · by_cases hlt : 3 * (P true).numLeaves < 2 * ((P false).numLeaves + (P true).numLeaves)
      · refine ⟨P true, IsSubprotocol.bob_true f P (P true) (IsSubprotocol.refl _), ?_, ?_⟩
        · simpa [hsum] using (show 3 * (P true).numLeaves ≥ (P false).numLeaves + (P true).numLeaves by omega)
        · simpa [hsum] using hlt
      · obtain ⟨s, hs, hs1, hs2⟩ :=
          balanced_aux (P true) ((P false).numLeaves + (P true).numLeaves) hn' (by omega)
        refine ⟨s, hs.trans (IsSubprotocol.bob_true f P (P true) (IsSubprotocol.refl _)), hs1, ?_⟩
        simpa [hsum] using hs2

/-- Type-valued witness for a subtree embedding, used for data-carrying recursion. -/
inductive SubprotocolPath : DetProtocol X Y α → DetProtocol X Y α → Type _ where
| refl : ∀ p, SubprotocolPath p p
| alice_false : ∀ f P s, SubprotocolPath s (P false) → SubprotocolPath s (DetProtocol.alice f P)
| alice_true  : ∀ f P s, SubprotocolPath s (P true)  → SubprotocolPath s (DetProtocol.alice f P)
| bob_false   : ∀ f P s, SubprotocolPath s (P false) → SubprotocolPath s (DetProtocol.bob f P)
| bob_true    : ∀ f P s, SubprotocolPath s (P true)  → SubprotocolPath s (DetProtocol.bob f P)

def SubprotocolPath.toIsSubprotocol {s p : DetProtocol X Y α} :
    SubprotocolPath s p → IsSubprotocol s p
  | .refl p => IsSubprotocol.refl p
  | .alice_false f P s hs => IsSubprotocol.alice_false f P s (hs.toIsSubprotocol)
  | .alice_true f P s hs => IsSubprotocol.alice_true f P s (hs.toIsSubprotocol)
  | .bob_false f P s hs => IsSubprotocol.bob_false f P s (hs.toIsSubprotocol)
  | .bob_true f P s hs => IsSubprotocol.bob_true f P s (hs.toIsSubprotocol)

theorem path_exists_of_isSubprotocol {s p : DetProtocol X Y α}
    (hsp : IsSubprotocol s p) : Nonempty (SubprotocolPath s p) := by
  induction hsp with
  | refl p => exact ⟨SubprotocolPath.refl p⟩
  | alice_false f P s hs ih =>
    rcases ih with ⟨t⟩
    exact ⟨SubprotocolPath.alice_false f P s t⟩
  | alice_true f P s hs ih =>
    rcases ih with ⟨t⟩
    exact ⟨SubprotocolPath.alice_true f P s t⟩
  | bob_false f P s hs ih =>
    rcases ih with ⟨t⟩
    exact ⟨SubprotocolPath.bob_false f P s t⟩
  | bob_true f P s hs ih =>
    rcases ih with ⟨t⟩
    exact ⟨SubprotocolPath.bob_true f P s t⟩

noncomputable def choosePath {s p : DetProtocol X Y α}
    (hsp : IsSubprotocol s p) : SubprotocolPath s p :=
  Classical.choice (path_exists_of_isSubprotocol hsp)

lemma SubprotocolPath.numLeaves_le {s p : DetProtocol X Y α}
    (hsp : SubprotocolPath s p) : s.numLeaves ≤ p.numLeaves := by
  induction hsp with
  | refl p =>
    exact le_rfl
  | alice_false f P s hs ih =>
    have hchild : (P false).numLeaves ≤ (DetProtocol.alice f P).numLeaves := by
      simp [DetProtocol.numLeaves, DetProtocol.shape]
    exact ih.trans hchild
  | alice_true f P s hs ih =>
    have hchild : (P true).numLeaves ≤ (DetProtocol.alice f P).numLeaves := by
      simp [DetProtocol.numLeaves, DetProtocol.shape]
    exact ih.trans hchild
  | bob_false f P s hs ih =>
    have hchild : (P false).numLeaves ≤ (DetProtocol.bob f P).numLeaves := by
      simp [DetProtocol.numLeaves, DetProtocol.shape]
    exact ih.trans hchild
  | bob_true f P s hs ih =>
    have hchild : (P true).numLeaves ≤ (DetProtocol.bob f P).numLeaves := by
      simp [DetProtocol.numLeaves, DetProtocol.shape]
    exact ih.trans hchild

/-- Alice-side predicate set for the inputs that reach a chosen subprotocol path. -/
def reachXPath {s p : DetProtocol X Y α} (hsp : SubprotocolPath s p) : Set X :=
  match hsp with
  | SubprotocolPath.refl _ => Set.univ
  | SubprotocolPath.alice_false f P s hs => reachXPath hs ∩ {x | f x = false}
  | SubprotocolPath.alice_true f P s hs => reachXPath hs ∩ {x | f x = true}
  | SubprotocolPath.bob_false _ _ _ hs => reachXPath hs
  | SubprotocolPath.bob_true _ _ _ hs => reachXPath hs

/-- Bob-side predicate set for the inputs that reach a chosen subprotocol path. -/
def reachYPath {s p : DetProtocol X Y α} (hsp : SubprotocolPath s p) : Set Y :=
  match hsp with
  | SubprotocolPath.refl _ => Set.univ
  | SubprotocolPath.alice_false _ _ _ hs => reachYPath hs
  | SubprotocolPath.alice_true _ _ _ hs => reachYPath hs
  | SubprotocolPath.bob_false f P s hs => reachYPath hs ∩ {y | f y = false}
  | SubprotocolPath.bob_true f P s hs => reachYPath hs ∩ {y | f y = true}

def reachesPath {s p : DetProtocol X Y α} (hsp : SubprotocolPath s p) (x : X) (y : Y) : Prop :=
  x ∈ reachXPath hsp ∧ y ∈ reachYPath hsp

def reachX {s p : DetProtocol X Y α} (hsp : IsSubprotocol s p) : Set X :=
  reachXPath (choosePath hsp)

def reachY {s p : DetProtocol X Y α} (hsp : IsSubprotocol s p) : Set Y :=
  reachYPath (choosePath hsp)

def reaches {s p : DetProtocol X Y α} (hsp : IsSubprotocol s p) (x : X) (y : Y) : Prop :=
  x ∈ reachX hsp ∧ y ∈ reachY hsp

lemma subprotocol_run_eq_of_reachesPath
    {s p : DetProtocol X Y α} (hsp : SubprotocolPath s p) {x : X} {y : Y}
    (hxy : reachesPath hsp x y) : p.run x y = s.run x y := by
  induction hsp with
  | refl _ =>
    rfl
  | alice_false f P s hs ih =>
    rcases hxy with ⟨hx, hy⟩
    have hfx : f x = false := hx.2
    simpa [reachesPath, reachXPath, reachYPath, DetProtocol.run, hfx] using ih ⟨hx.1, hy⟩
  | alice_true f P s hs ih =>
    rcases hxy with ⟨hx, hy⟩
    have hfx : f x = true := hx.2
    simpa [reachesPath, reachXPath, reachYPath, DetProtocol.run, hfx] using ih ⟨hx.1, hy⟩
  | bob_false f P s hs ih =>
    rcases hxy with ⟨hx, hy⟩
    have hfy : f y = false := hy.2
    simpa [reachesPath, reachXPath, reachYPath, DetProtocol.run, hfy] using ih ⟨hx, hy.1⟩
  | bob_true f P s hs ih =>
    rcases hxy with ⟨hx, hy⟩
    have hfy : f y = true := hy.2
    simpa [reachesPath, reachXPath, reachYPath, DetProtocol.run, hfy] using ih ⟨hx, hy.1⟩

lemma subprotocol_run_eq_of_reaches
    {s p : DetProtocol X Y α} (hsp : IsSubprotocol s p) {x : X} {y : Y}
    (hxy : reaches hsp x y) : p.run x y = s.run x y := by
  simpa [reaches, reachX, reachY] using
    (subprotocol_run_eq_of_reachesPath (choosePath hsp) hxy)

/-- Pick a canonical output value from a protocol (leftmost leaf). -/
def chooseOutput : DetProtocol X Y α → α
  | .output a => a
  | .alice _ P => chooseOutput (P false)
  | .bob _ P => chooseOutput (P false)

def erasePath {s p : DetProtocol X Y α} (hsp : SubprotocolPath s p) :
    DetProtocol X Y α :=
  match hsp with
  | .refl p => .output (chooseOutput p)
  | .alice_false f P s hs =>
      .alice f (fun b =>
        match b with
        | false => erasePath hs
        | true => P true)
  | .alice_true f P s hs =>
      .alice f (fun b =>
        match b with
        | false => P false
        | true => erasePath hs)
  | .bob_false f P s hs =>
      .bob f (fun b =>
        match b with
        | false => erasePath hs
        | true => P true)
  | .bob_true f P s hs =>
      .bob f (fun b =>
        match b with
        | false => P false
        | true => erasePath hs)

lemma erasePath_numLeaves {s p : DetProtocol X Y α} (hsp : SubprotocolPath s p) :
    (erasePath hsp).numLeaves = p.numLeaves - s.numLeaves + 1 := by
  induction hsp with
  | refl p =>
    simp [erasePath, DetProtocol.numLeaves, DetProtocol.shape]
  | alice_false f P s hs ih =>
    have hle : s.numLeaves ≤ (P false).numLeaves := SubprotocolPath.numLeaves_le hs
    calc
      (erasePath (SubprotocolPath.alice_false f P s hs)).numLeaves
          = (erasePath hs).numLeaves + (P true).numLeaves := by
              simp [erasePath, DetProtocol.numLeaves, DetProtocol.shape]
      _ = ((P false).numLeaves - s.numLeaves + 1) + (P true).numLeaves := by
            rw [ih]
      _ = (DetProtocol.alice f P).numLeaves - s.numLeaves + 1 := by
            have hle' : s.shape.numLeaves ≤ (P false).shape.numLeaves := by
              simpa [DetProtocol.numLeaves] using hle
            simp [DetProtocol.numLeaves, DetProtocol.shape]
            omega
  | alice_true f P s hs ih =>
    have hle : s.numLeaves ≤ (P true).numLeaves := SubprotocolPath.numLeaves_le hs
    calc
      (erasePath (SubprotocolPath.alice_true f P s hs)).numLeaves
          = (P false).numLeaves + (erasePath hs).numLeaves := by
              simp [erasePath, DetProtocol.numLeaves, DetProtocol.shape]
      _ = (P false).numLeaves + ((P true).numLeaves - s.numLeaves + 1) := by
            rw [ih]
      _ = (DetProtocol.alice f P).numLeaves - s.numLeaves + 1 := by
            have hle' : s.shape.numLeaves ≤ (P true).shape.numLeaves := by
              simpa [DetProtocol.numLeaves] using hle
            simp [DetProtocol.numLeaves, DetProtocol.shape]
            omega
  | bob_false f P s hs ih =>
    have hle : s.numLeaves ≤ (P false).numLeaves := SubprotocolPath.numLeaves_le hs
    calc
      (erasePath (SubprotocolPath.bob_false f P s hs)).numLeaves
          = (erasePath hs).numLeaves + (P true).numLeaves := by
              simp [erasePath, DetProtocol.numLeaves, DetProtocol.shape]
      _ = ((P false).numLeaves - s.numLeaves + 1) + (P true).numLeaves := by
            rw [ih]
      _ = (DetProtocol.bob f P).numLeaves - s.numLeaves + 1 := by
            have hle' : s.shape.numLeaves ≤ (P false).shape.numLeaves := by
              simpa [DetProtocol.numLeaves] using hle
            simp [DetProtocol.numLeaves, DetProtocol.shape]
            omega
  | bob_true f P s hs ih =>
    have hle : s.numLeaves ≤ (P true).numLeaves := SubprotocolPath.numLeaves_le hs
    calc
      (erasePath (SubprotocolPath.bob_true f P s hs)).numLeaves
          = (P false).numLeaves + (erasePath hs).numLeaves := by
              simp [erasePath, DetProtocol.numLeaves, DetProtocol.shape]
      _ = (P false).numLeaves + ((P true).numLeaves - s.numLeaves + 1) := by
            rw [ih]
      _ = (DetProtocol.bob f P).numLeaves - s.numLeaves + 1 := by
            have hle' : s.shape.numLeaves ≤ (P true).shape.numLeaves := by
              simpa [DetProtocol.numLeaves] using hle
            simp [DetProtocol.numLeaves, DetProtocol.shape]
            omega

lemma erasePath_run_outside
    {s p : DetProtocol X Y α} (hsp : SubprotocolPath s p) {x : X} {y : Y}
    (hxy : ¬ reachesPath hsp x y) :
    (erasePath hsp).run x y = p.run x y := by
  induction hsp with
  | refl p =>
    exfalso
    exact hxy (by simp [reachesPath, reachXPath, reachYPath])
  | alice_false f P s hs ih =>
    by_cases hfx : f x = false
    · have hxy' : ¬ reachesPath hs x y := by
        intro hreach
        exact hxy (by simpa [reachesPath, reachXPath, reachYPath, hfx] using hreach)
      have := ih hxy'
      simpa [erasePath, DetProtocol.run, hfx] using this
    · have hfx' : f x = true := by
        cases h : f x <;> simp_all
      simp [erasePath, DetProtocol.run, hfx']
  | alice_true f P s hs ih =>
    by_cases hfx : f x = true
    · have hxy' : ¬ reachesPath hs x y := by
        intro hreach
        exact hxy (by simpa [reachesPath, reachXPath, reachYPath, hfx] using hreach)
      have := ih hxy'
      simpa [erasePath, DetProtocol.run, hfx] using this
    · have hfx' : f x = false := by
        cases h : f x <;> simp_all
      simp [erasePath, DetProtocol.run, hfx']
  | bob_false f P s hs ih =>
    by_cases hfy : f y = false
    · have hxy' : ¬ reachesPath hs x y := by
        intro hreach
        exact hxy (by simpa [reachesPath, reachXPath, reachYPath, hfy] using hreach)
      have := ih hxy'
      simpa [erasePath, DetProtocol.run, hfy] using this
    · have hfy' : f y = true := by
        cases h : f y <;> simp_all
      simp [erasePath, DetProtocol.run, hfy']
  | bob_true f P s hs ih =>
    by_cases hfy : f y = true
    · have hxy' : ¬ reachesPath hs x y := by
        intro hreach
        exact hxy (by simpa [reachesPath, reachXPath, reachYPath, hfy] using hreach)
      have := ih hxy'
      simpa [erasePath, DetProtocol.run, hfy] using this
    · have hfy' : f y = false := by
        cases h : f y <;> simp_all
      simp [erasePath, DetProtocol.run, hfy']

noncomputable def erase {s p : DetProtocol X Y α} (hsp : IsSubprotocol s p) :
    DetProtocol X Y α :=
  erasePath (choosePath hsp)

lemma erase_numLeaves {s p : DetProtocol X Y α} (hsp : IsSubprotocol s p) :
    (erase hsp).numLeaves = p.numLeaves - s.numLeaves + 1 := by
  simpa [erase] using erasePath_numLeaves (choosePath hsp)

lemma erase_run_outside
    {s p : DetProtocol X Y α} (hsp : IsSubprotocol s p) {x : X} {y : Y}
    (hxy : ¬ reaches hsp x y) :
    (erase hsp).run x y = p.run x y := by
  simpa [erase, reaches, reachX, reachY] using
    (erasePath_run_outside (choosePath hsp) hxy)

/-- Delete a selected subtree by splicing; returns `none` only at the root case. -/
def deletePath {s p : DetProtocol X Y α} (hsp : SubprotocolPath s p) :
    Option (DetProtocol X Y α) :=
  match hsp with
  | .refl _ => none
  | .alice_false f P s hs =>
      match deletePath hs with
      | none => some (P true)
      | some q => some (.alice f (fun b => if b then P true else q))
  | .alice_true f P s hs =>
      match deletePath hs with
      | none => some (P false)
      | some q => some (.alice f (fun b => if b then q else P false))
  | .bob_false f P s hs =>
      match deletePath hs with
      | none => some (P true)
      | some q => some (.bob f (fun b => if b then P true else q))
  | .bob_true f P s hs =>
      match deletePath hs with
      | none => some (P false)
      | some q => some (.bob f (fun b => if b then q else P false))

lemma deletePath_ne_none_of_lt {s p : DetProtocol X Y α} (hsp : SubprotocolPath s p)
    (hlt : s.numLeaves < p.numLeaves) : deletePath hsp ≠ none := by
  induction hsp with
  | refl p =>
    exact (Nat.lt_irrefl _ hlt).elim
  | alice_false f P s hs ih =>
    cases hdel : deletePath hs <;> simp [deletePath, hdel]
  | alice_true f P s hs ih =>
    cases hdel : deletePath hs <;> simp [deletePath, hdel]
  | bob_false f P s hs ih =>
    cases hdel : deletePath hs <;> simp [deletePath, hdel]
  | bob_true f P s hs ih =>
    cases hdel : deletePath hs <;> simp [deletePath, hdel]

lemma deletePath_exists_of_lt {s p : DetProtocol X Y α} (hsp : SubprotocolPath s p)
    (hlt : s.numLeaves < p.numLeaves) :
    ∃ q, deletePath hsp = some q := by
  cases hdel : deletePath hsp with
  | none =>
    exfalso
    exact (deletePath_ne_none_of_lt hsp hlt) hdel
  | some q =>
    exact ⟨q, rfl⟩

noncomputable def prunePath {s p : DetProtocol X Y α} (hsp : SubprotocolPath s p)
    (hlt : s.numLeaves < p.numLeaves) : DetProtocol X Y α :=
  Classical.choose (deletePath_exists_of_lt hsp hlt)

lemma prunePath_spec {s p : DetProtocol X Y α} (hsp : SubprotocolPath s p)
    (hlt : s.numLeaves < p.numLeaves) :
    deletePath hsp = some (prunePath hsp hlt) :=
  Classical.choose_spec (deletePath_exists_of_lt hsp hlt)

lemma eq_of_deletePath_none {s p : DetProtocol X Y α} (hsp : SubprotocolPath s p)
    (hnone : deletePath hsp = none) : s = p := by
  cases hsp with
  | refl p =>
    rfl
  | alice_false f P s hs =>
    cases hdel : deletePath hs <;> simp [deletePath, hdel] at hnone
  | alice_true f P s hs =>
    cases hdel : deletePath hs <;> simp [deletePath, hdel] at hnone
  | bob_false f P s hs =>
    cases hdel : deletePath hs <;> simp [deletePath, hdel] at hnone
  | bob_true f P s hs =>
    cases hdel : deletePath hs <;> simp [deletePath, hdel] at hnone

lemma deletePath_numLeaves_of_some {s p : DetProtocol X Y α} (hsp : SubprotocolPath s p)
    {q : DetProtocol X Y α} (hq : deletePath hsp = some q) :
    q.numLeaves = p.numLeaves - s.numLeaves := by
  induction hsp generalizing q with
  | refl p =>
    simp [deletePath] at hq
  | alice_false f P s hs ih =>
    cases hchild : deletePath hs with
    | none =>
      simp [deletePath, hchild] at hq
      subst q
      have hsEq : s = P false := eq_of_deletePath_none hs hchild
      subst hsEq
      simp [DetProtocol.numLeaves, DetProtocol.shape]
    | some qchild =>
      simp [deletePath, hchild] at hq
      subst q
      have hchildEq : qchild.numLeaves = (P false).numLeaves - s.numLeaves :=
        ih hchild
      have hchildEq' : qchild.shape.numLeaves = (P false).shape.numLeaves - s.shape.numLeaves := by
        simpa [DetProtocol.numLeaves] using hchildEq
      have hle : s.numLeaves ≤ (P false).numLeaves := SubprotocolPath.numLeaves_le hs
      have hle' : s.shape.numLeaves ≤ (P false).shape.numLeaves := by
        simpa [DetProtocol.numLeaves] using hle
      simp [DetProtocol.numLeaves, DetProtocol.shape, hchildEq']
      omega
  | alice_true f P s hs ih =>
    cases hchild : deletePath hs with
    | none =>
      simp [deletePath, hchild] at hq
      subst q
      have hsEq : s = P true := eq_of_deletePath_none hs hchild
      subst hsEq
      simp [DetProtocol.numLeaves, DetProtocol.shape]
    | some qchild =>
      simp [deletePath, hchild] at hq
      subst q
      have hchildEq : qchild.numLeaves = (P true).numLeaves - s.numLeaves :=
        ih hchild
      have hchildEq' : qchild.shape.numLeaves = (P true).shape.numLeaves - s.shape.numLeaves := by
        simpa [DetProtocol.numLeaves] using hchildEq
      have hle : s.numLeaves ≤ (P true).numLeaves := SubprotocolPath.numLeaves_le hs
      have hle' : s.shape.numLeaves ≤ (P true).shape.numLeaves := by
        simpa [DetProtocol.numLeaves] using hle
      simp [DetProtocol.numLeaves, DetProtocol.shape, hchildEq']
      omega
  | bob_false f P s hs ih =>
    cases hchild : deletePath hs with
    | none =>
      simp [deletePath, hchild] at hq
      subst q
      have hsEq : s = P false := eq_of_deletePath_none hs hchild
      subst hsEq
      simp [DetProtocol.numLeaves, DetProtocol.shape]
    | some qchild =>
      simp [deletePath, hchild] at hq
      subst q
      have hchildEq : qchild.numLeaves = (P false).numLeaves - s.numLeaves :=
        ih hchild
      have hchildEq' : qchild.shape.numLeaves = (P false).shape.numLeaves - s.shape.numLeaves := by
        simpa [DetProtocol.numLeaves] using hchildEq
      have hle : s.numLeaves ≤ (P false).numLeaves := SubprotocolPath.numLeaves_le hs
      have hle' : s.shape.numLeaves ≤ (P false).shape.numLeaves := by
        simpa [DetProtocol.numLeaves] using hle
      simp [DetProtocol.numLeaves, DetProtocol.shape, hchildEq']
      omega
  | bob_true f P s hs ih =>
    cases hchild : deletePath hs with
    | none =>
      simp [deletePath, hchild] at hq
      subst q
      have hsEq : s = P true := eq_of_deletePath_none hs hchild
      subst hsEq
      simp [DetProtocol.numLeaves, DetProtocol.shape]
    | some qchild =>
      simp [deletePath, hchild] at hq
      subst q
      have hchildEq : qchild.numLeaves = (P true).numLeaves - s.numLeaves :=
        ih hchild
      have hchildEq' : qchild.shape.numLeaves = (P true).shape.numLeaves - s.shape.numLeaves := by
        simpa [DetProtocol.numLeaves] using hchildEq
      have hle : s.numLeaves ≤ (P true).numLeaves := SubprotocolPath.numLeaves_le hs
      have hle' : s.shape.numLeaves ≤ (P true).shape.numLeaves := by
        simpa [DetProtocol.numLeaves] using hle
      simp [DetProtocol.numLeaves, DetProtocol.shape, hchildEq']
      omega

lemma prunePath_numLeaves_of_lt {s p : DetProtocol X Y α} (hsp : SubprotocolPath s p)
    (hlt : s.numLeaves < p.numLeaves) :
    (prunePath hsp hlt).numLeaves = p.numLeaves - s.numLeaves := by
  simpa [prunePath] using deletePath_numLeaves_of_some hsp (prunePath_spec hsp hlt)

lemma reachesPath_of_deletePath_none {s p : DetProtocol X Y α} (hsp : SubprotocolPath s p)
    (hnone : deletePath hsp = none) (x : X) (y : Y) : reachesPath hsp x y := by
  induction hsp with
  | refl p =>
    simp [reachesPath, reachXPath, reachYPath]
  | alice_false f P s hs ih =>
    cases hdel : deletePath hs <;> simp [deletePath, hdel] at hnone
  | alice_true f P s hs ih =>
    cases hdel : deletePath hs <;> simp [deletePath, hdel] at hnone
  | bob_false f P s hs ih =>
    cases hdel : deletePath hs <;> simp [deletePath, hdel] at hnone
  | bob_true f P s hs ih =>
    cases hdel : deletePath hs <;> simp [deletePath, hdel] at hnone

lemma deletePath_run_outside_of_some {s p : DetProtocol X Y α} (hsp : SubprotocolPath s p)
    {q : DetProtocol X Y α} (hq : deletePath hsp = some q) {x : X} {y : Y}
    (hxy : ¬ reachesPath hsp x y) :
    q.run x y = p.run x y := by
  induction hsp generalizing q with
  | refl p =>
    simp [deletePath] at hq
  | alice_false f P s hs ih =>
    cases hchild : deletePath hs with
    | none =>
      have hq' : q = P true := by simpa [deletePath, hchild] using hq.symm
      subst q
      by_cases hfx : f x = false
      · exfalso
        have hreach : reachesPath hs x y := reachesPath_of_deletePath_none hs hchild x y
        exact hxy (by simpa [reachesPath, reachXPath, reachYPath, hfx] using hreach)
      · have hfx' : f x = true := by cases h : f x <;> simp_all
        simp [DetProtocol.run, hfx']
    | some qchild =>
      have hq' : q = alice f (fun b => if b = true then P true else qchild) := by
        simpa [deletePath, hchild] using hq.symm
      subst q
      by_cases hfx : f x = false
      · have hxy' : ¬ reachesPath hs x y := by
          intro hreach
          exact hxy (by simpa [reachesPath, reachXPath, reachYPath, hfx] using hreach)
        have hrec : qchild.run x y = (P false).run x y := ih hchild hxy'
        simp [DetProtocol.run, hfx, hrec]
      · have hfx' : f x = true := by cases h : f x <;> simp_all
        simp [DetProtocol.run, hfx']
  | alice_true f P s hs ih =>
    cases hchild : deletePath hs with
    | none =>
      have hq' : q = P false := by simpa [deletePath, hchild] using hq.symm
      subst q
      by_cases hfx : f x = true
      · exfalso
        have hreach : reachesPath hs x y := reachesPath_of_deletePath_none hs hchild x y
        exact hxy (by simpa [reachesPath, reachXPath, reachYPath, hfx] using hreach)
      · have hfx' : f x = false := by cases h : f x <;> simp_all
        simp [DetProtocol.run, hfx']
    | some qchild =>
      have hq' : q = alice f (fun b => if b = true then qchild else P false) := by
        simpa [deletePath, hchild] using hq.symm
      subst q
      by_cases hfx : f x = true
      · have hxy' : ¬ reachesPath hs x y := by
          intro hreach
          exact hxy (by simpa [reachesPath, reachXPath, reachYPath, hfx] using hreach)
        have hrec : qchild.run x y = (P true).run x y := ih hchild hxy'
        simp [DetProtocol.run, hfx, hrec]
      · have hfx' : f x = false := by cases h : f x <;> simp_all
        simp [DetProtocol.run, hfx']
  | bob_false f P s hs ih =>
    cases hchild : deletePath hs with
    | none =>
      have hq' : q = P true := by simpa [deletePath, hchild] using hq.symm
      subst q
      by_cases hfy : f y = false
      · exfalso
        have hreach : reachesPath hs x y := reachesPath_of_deletePath_none hs hchild x y
        exact hxy (by simpa [reachesPath, reachXPath, reachYPath, hfy] using hreach)
      · have hfy' : f y = true := by cases h : f y <;> simp_all
        simp [DetProtocol.run, hfy']
    | some qchild =>
      have hq' : q = bob f (fun b => if b = true then P true else qchild) := by
        simpa [deletePath, hchild] using hq.symm
      subst q
      by_cases hfy : f y = false
      · have hxy' : ¬ reachesPath hs x y := by
          intro hreach
          exact hxy (by simpa [reachesPath, reachXPath, reachYPath, hfy] using hreach)
        have hrec : qchild.run x y = (P false).run x y := ih hchild hxy'
        simp [DetProtocol.run, hfy, hrec]
      · have hfy' : f y = true := by cases h : f y <;> simp_all
        simp [DetProtocol.run, hfy']
  | bob_true f P s hs ih =>
    cases hchild : deletePath hs with
    | none =>
      have hq' : q = P false := by simpa [deletePath, hchild] using hq.symm
      subst q
      by_cases hfy : f y = true
      · exfalso
        have hreach : reachesPath hs x y := reachesPath_of_deletePath_none hs hchild x y
        exact hxy (by simpa [reachesPath, reachXPath, reachYPath, hfy] using hreach)
      · have hfy' : f y = false := by cases h : f y <;> simp_all
        simp [DetProtocol.run, hfy']
    | some qchild =>
      have hq' : q = bob f (fun b => if b = true then qchild else P false) := by
        simpa [deletePath, hchild] using hq.symm
      subst q
      by_cases hfy : f y = true
      · have hxy' : ¬ reachesPath hs x y := by
          intro hreach
          exact hxy (by simpa [reachesPath, reachXPath, reachYPath, hfy] using hreach)
        have hrec : qchild.run x y = (P true).run x y := ih hchild hxy'
        simp [DetProtocol.run, hfy, hrec]
      · have hfy' : f y = false := by cases h : f y <;> simp_all
        simp [DetProtocol.run, hfy']

lemma prunePath_run_outside_of_lt {s p : DetProtocol X Y α} (hsp : SubprotocolPath s p)
    (hlt : s.numLeaves < p.numLeaves) {x : X} {y : Y}
    (hxy : ¬ reachesPath hsp x y) :
    (prunePath hsp hlt).run x y = p.run x y := by
  exact deletePath_run_outside_of_some hsp (prunePath_spec hsp hlt) hxy

noncomputable def prune {s p : DetProtocol X Y α} (hsp : IsSubprotocol s p)
    (hlt : s.numLeaves < p.numLeaves) : DetProtocol X Y α :=
  prunePath (choosePath hsp) hlt

lemma prune_numLeaves_of_lt {s p : DetProtocol X Y α} (hsp : IsSubprotocol s p)
    (hlt : s.numLeaves < p.numLeaves) :
    (prune hsp hlt).numLeaves = p.numLeaves - s.numLeaves := by
  simpa [prune] using prunePath_numLeaves_of_lt (choosePath hsp) hlt

lemma prune_run_outside_of_lt {s p : DetProtocol X Y α} (hsp : IsSubprotocol s p)
    (hlt : s.numLeaves < p.numLeaves) {x : X} {y : Y}
    (hxy : ¬ reaches hsp x y) :
    (prune hsp hlt).run x y = p.run x y := by
  simpa [prune, reaches, reachX, reachY] using
    (prunePath_run_outside_of_lt (choosePath hsp) hlt hxy)


noncomputable def testSubprotocol {s p : DetProtocol X Y α} (hsp : IsSubprotocol s p)
    (qIn qOut : DetProtocol X Y α) : DetProtocol X Y α :=
  DetProtocol.alice (fun x => by
    classical
    exact decide (x ∈ reachX hsp)) (fun bx =>
    DetProtocol.bob (fun y => by
      classical
      exact decide (y ∈ reachY hsp)) (fun bY =>
        if bx && bY then qIn else qOut))

@[simp] lemma testSubprotocol_complexity
    {s p : DetProtocol X Y α} (hsp : IsSubprotocol s p)
    (qIn qOut : DetProtocol X Y α) :
    (testSubprotocol hsp qIn qOut).complexity =
      2 + max qIn.complexity qOut.complexity := by
  simp [testSubprotocol, DetProtocol.complexity, Nat.max_comm]
  omega

lemma testSubprotocol_run_inside
    {s p qIn qOut : DetProtocol X Y α} (hsp : IsSubprotocol s p) {x : X} {y : Y}
    (hxy : reaches hsp x y) :
    (testSubprotocol hsp qIn qOut).run x y = qIn.run x y := by
  rcases hxy with ⟨hx, hy⟩
  simp [testSubprotocol, DetProtocol.run, hx, hy]

lemma testSubprotocol_run_outside
    {s p qIn qOut : DetProtocol X Y α} (hsp : IsSubprotocol s p) {x : X} {y : Y}
    (hxy : ¬ reaches hsp x y) :
    (testSubprotocol hsp qIn qOut).run x y = qOut.run x y := by
  by_cases hx : x ∈ reachX hsp
  · have hy : y ∉ reachY hsp := by
      intro hy
      exact hxy ⟨hx, hy⟩
    simp [testSubprotocol, DetProtocol.run, hx, hy]
  · simp [testSubprotocol, DetProtocol.run, hx]

private lemma numLeaves_pos (p : DetProtocol X Y α) : 0 < p.numLeaves := by
  cases p with
  | output a =>
    simp [DetProtocol.numLeaves, DetProtocol.shape]
  | alice f P =>
    have h : 0 < (P false).numLeaves := numLeaves_pos (P false)
    have hsum : 0 < (P false).numLeaves + (P true).numLeaves := Nat.add_pos_left h _
    simpa [DetProtocol.numLeaves, DetProtocol.shape] using hsum
  | bob f P =>
    have h : 0 < (P false).numLeaves := numLeaves_pos (P false)
    have hsum : 0 < (P false).numLeaves + (P true).numLeaves := Nat.add_pos_left h _
    simpa [DetProtocol.numLeaves, DetProtocol.shape] using hsum

/-- Theorem 1.7 in the experiments file: balanced simulation with 2-bit subtree tests. -/
theorem theorem_1_7_experiment (p : DetProtocol X Y α) :
    ∃ q : DetProtocol X Y α, q.run = p.run ∧
      3 ^ q.complexity ≤ 2 ^ q.complexity * p.numLeaves ^ 2 := by
  let target : ℕ → Prop := fun n =>
    ∀ p : DetProtocol X Y α, p.numLeaves = n →
      ∃ q : DetProtocol X Y α, q.run = p.run ∧
        3 ^ q.complexity ≤ 2 ^ q.complexity * p.numLeaves ^ 2
  have htarget : ∀ n, target n := by
    intro n
    refine Nat.strongRecOn n ?_
    intro n ih
    intro p hpn
    by_cases hn1 : n = 1
    · refine ⟨p, rfl, ?_⟩
      have hleaf1 : p.numLeaves = 1 := by simpa [hn1] using hpn
      have hcomp0 : p.complexity = 0 := by
        cases p with
        | output a => rfl
        | alice f P =>
          exfalso
          have hs : (P false).shape.numLeaves + (P true).shape.numLeaves = 1 := by
            simpa [DetProtocol.numLeaves, DetProtocol.shape] using hleaf1
          have hp0 : 0 < (P false).shape.numLeaves := by
            simpa [DetProtocol.numLeaves] using numLeaves_pos (P false)
          have hp1 : 0 < (P true).shape.numLeaves := by
            simpa [DetProtocol.numLeaves] using numLeaves_pos (P true)
          omega
        | bob f P =>
          exfalso
          have hs : (P false).shape.numLeaves + (P true).shape.numLeaves = 1 := by
            simpa [DetProtocol.numLeaves, DetProtocol.shape] using hleaf1
          have hp0 : 0 < (P false).shape.numLeaves := by
            simpa [DetProtocol.numLeaves] using numLeaves_pos (P false)
          have hp1 : 0 < (P true).shape.numLeaves := by
            simpa [DetProtocol.numLeaves] using numLeaves_pos (P true)
          omega
      subst hn1
      simp [hcomp0, hpn]
    · have hgt1 : 1 < n := by
        have hnpos : 0 < n := by
          have hp : 0 < p.numLeaves := numLeaves_pos p
          simpa [hpn] using hp
        omega
      have hgt1p : 1 < p.numLeaves := by simpa [hpn] using hgt1
      obtain ⟨s, hsp, hbal_lo, hbal_hi⟩ := balanced_subprotocol p hgt1p
      let m := s.numLeaves
      have hm_lt_p : m < p.numLeaves := by
        dsimp [m]
        omega
      have hm_lt_n : m < n := by
        simpa [hpn, m] using hm_lt_p
      have hm_pos : 0 < m := by
        dsimp [m]
        exact numLeaves_pos s
      have hm_le_n : m ≤ n := hm_lt_n.le
      have hout_lt_n : n - m < n := by
        omega
      obtain ⟨qIn, hRunIn, hBoundIn⟩ := ih m hm_lt_n s rfl
      let pOut := prune hsp hm_lt_p
      have hpOut_leaves : pOut.numLeaves = n - m := by
        dsimp [pOut, m]
        simpa [hpn] using prune_numLeaves_of_lt hsp hm_lt_p
      obtain ⟨qOut, hRunOut, hBoundOut⟩ := ih (n - m) hout_lt_n pOut hpOut_leaves
      let q := testSubprotocol hsp qIn qOut
      refine ⟨q, ?_, ?_⟩
      · ext x y
        by_cases hxy : reaches hsp x y
        · calc
            q.run x y = qIn.run x y := by
              simpa [q] using testSubprotocol_run_inside hsp hxy
            _ = s.run x y := by
              simp [hRunIn]
            _ = p.run x y := by
              symm
              exact subprotocol_run_eq_of_reaches hsp hxy
        · calc
            q.run x y = qOut.run x y := by
              simpa [q] using testSubprotocol_run_outside hsp hxy
            _ = pOut.run x y := by
              simp [hRunOut]
            _ = p.run x y := by
              dsimp [pOut]
              exact prune_run_outside_of_lt hsp hm_lt_p hxy
      · have hInBound' : 3 ^ qIn.complexity ≤ 2 ^ qIn.complexity * m ^ 2 := by
          simpa [m] using hBoundIn
        have hOutBound' : 3 ^ qOut.complexity ≤ 2 ^ qOut.complexity * (n - m) ^ 2 := by
          simpa [hpOut_leaves] using hBoundOut
        have hmaxBound :
            3 ^ max qIn.complexity qOut.complexity ≤
              2 ^ max qIn.complexity qOut.complexity * max (m ^ 2) ((n - m) ^ 2) := by
          by_cases hcmp : qIn.complexity ≤ qOut.complexity
          · have hmax : max qIn.complexity qOut.complexity = qOut.complexity := max_eq_right hcmp
            rw [hmax]
            calc
              3 ^ qOut.complexity ≤ 2 ^ qOut.complexity * (n - m) ^ 2 := hOutBound'
              _ ≤ 2 ^ qOut.complexity * max (m ^ 2) ((n - m) ^ 2) :=
                    Nat.mul_le_mul_left _ (Nat.le_max_right _ _)
          · have hcmp' : qOut.complexity ≤ qIn.complexity := le_of_not_ge hcmp
            have hmax : max qIn.complexity qOut.complexity = qIn.complexity := max_eq_left hcmp'
            rw [hmax]
            calc
              3 ^ qIn.complexity ≤ 2 ^ qIn.complexity * m ^ 2 := hInBound'
              _ ≤ 2 ^ qIn.complexity * max (m ^ 2) ((n - m) ^ 2) :=
                    Nat.mul_le_mul_left _ (Nat.le_max_left _ _)
        have hm2 : 3 * m ≤ 2 * n := by
          omega
        have hout2 : 3 * (n - m) ≤ 2 * n := by
          omega
        have hmSq : 9 * m ^ 2 ≤ 4 * n ^ 2 := by
          have hpow : (3 * m) * (3 * m) ≤ (2 * n) * (2 * n) := Nat.mul_le_mul hm2 hm2
          simpa [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hpow
        have houtSq : 9 * (n - m) ^ 2 ≤ 4 * n ^ 2 := by
          have hpow : (3 * (n - m)) * (3 * (n - m)) ≤ (2 * n) * (2 * n) :=
            Nat.mul_le_mul hout2 hout2
          simpa [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hpow
        have hmaxSq : 9 * max (m ^ 2) ((n - m) ^ 2) ≤ 4 * n ^ 2 := by
          by_cases hcase : m ^ 2 ≤ (n - m) ^ 2
          · rw [max_eq_right hcase]
            exact houtSq
          · rw [max_eq_left (le_of_not_ge hcase)]
            exact hmSq
        have hqComp : q.complexity = 2 + max qIn.complexity qOut.complexity := by
          dsimp [q]
          exact testSubprotocol_complexity hsp qIn qOut
        rw [hqComp]
        have hstep1 :
            3 ^ (2 + max qIn.complexity qOut.complexity) =
              9 * 3 ^ max qIn.complexity qOut.complexity := by
          simp [pow_add, Nat.mul_comm]
        have hstep2 :
            2 ^ (2 + max qIn.complexity qOut.complexity) =
              4 * 2 ^ max qIn.complexity qOut.complexity := by
          simp [pow_add, Nat.mul_comm]
        rw [hstep1, hstep2]
        calc
          9 * 3 ^ max qIn.complexity qOut.complexity
              ≤ 9 * (2 ^ max qIn.complexity qOut.complexity * max (m ^ 2) ((n - m) ^ 2)) :=
                Nat.mul_le_mul_left _ hmaxBound
          _ = 2 ^ max qIn.complexity qOut.complexity * (9 * max (m ^ 2) ((n - m) ^ 2)) := by
                ring
          _ ≤ 2 ^ max qIn.complexity qOut.complexity * (4 * n ^ 2) :=
                Nat.mul_le_mul_left _ hmaxSq
          _ = (4 * 2 ^ max qIn.complexity qOut.complexity) * n ^ 2 := by
                ring
          _ = (4 * 2 ^ max qIn.complexity qOut.complexity) * p.numLeaves ^ 2 := by
                simp [hpn]
  exact htarget p.numLeaves p rfl

end DetProtocol
