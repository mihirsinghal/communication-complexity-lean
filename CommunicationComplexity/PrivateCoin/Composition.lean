import CommunicationComplexity.PrivateCoin.GeneralFiniteMessage
import Mathlib.Algebra.BigOperators.Fin

namespace CommunicationComplexity

namespace PrivateCoin.GeneralFiniteMessage.Protocol

variable {Ω_X Ω_Y Ω_X' Ω_Y' Ω_X1 Ω_X2 Ω_Y1 Ω_Y2 X Y α α₁ α₂ β : Type*}

/-- Map a function over the output of a protocol. -/
def map [Fintype Ω_X] [Fintype Ω_Y] (g : α → β) :
    Protocol Ω_X Ω_Y X Y α → Protocol Ω_X Ω_Y X Y β
  | .output a => .output (g a)
  | alice f P =>
      alice f (fun b => (P b).map g)
  | bob f P =>
      bob f (fun b => (P b).map g)

@[simp]
theorem map_run [Fintype Ω_X] [Fintype Ω_Y] (g : α → β)
    (p : Protocol Ω_X Ω_Y X Y α) (x : X) (y : Y) (ω_x : Ω_X) (ω_y : Ω_Y) :
    (p.map g).run x y ω_x ω_y = g (p.run x y ω_x ω_y) := by
  induction p with
  | output a => simp [map, run]
  | alice f P ih => simp only [map, run]; exact ih _
  | bob f P ih => simp only [map, run]; exact ih _

@[simp]
theorem map_complexity [Fintype Ω_X] [Fintype Ω_Y] (g : α → β)
    (p : Protocol Ω_X Ω_Y X Y α) :
    (p.map g).complexity = p.complexity := by
  induction p with
  | output a => simp [map, complexity]
  | alice f P ih => simp only [map, complexity, ih]
  | bob f P ih => simp only [map, complexity, ih]

/-- Reindex both randomness spaces of a protocol. -/
def comapRandomness [Fintype Ω_X] [Fintype Ω_Y] [Fintype Ω_X'] [Fintype Ω_Y']
    (hX : Ω_X' → Ω_X) (hY : Ω_Y' → Ω_Y) :
    Protocol Ω_X Ω_Y X Y α → Protocol Ω_X' Ω_Y' X Y α
  | .output a => .output a
  | alice f P =>
      alice (fun x ω => f x (hX ω))
        (fun b => (P b).comapRandomness hX hY)
  | bob f P =>
      bob (fun y ω => f y (hY ω))
        (fun b => (P b).comapRandomness hX hY)

@[simp]
theorem comapRandomness_run [Fintype Ω_X] [Fintype Ω_Y] [Fintype Ω_X'] [Fintype Ω_Y']
    (hX : Ω_X' → Ω_X) (hY : Ω_Y' → Ω_Y) (p : Protocol Ω_X Ω_Y X Y α)
    (x : X) (y : Y) (ω_x : Ω_X') (ω_y : Ω_Y') :
    (p.comapRandomness hX hY).run x y ω_x ω_y = p.run x y (hX ω_x) (hY ω_y) := by
  induction p with
  | output a => simp [comapRandomness, run]
  | alice f P ih => simp only [comapRandomness, run]; exact ih _
  | bob f P ih => simp only [comapRandomness, run]; exact ih _

@[simp]
theorem comapRandomness_complexity [Fintype Ω_X] [Fintype Ω_Y] [Fintype Ω_X'] [Fintype Ω_Y']
    (hX : Ω_X' → Ω_X) (hY : Ω_Y' → Ω_Y) (p : Protocol Ω_X Ω_Y X Y α) :
    (p.comapRandomness hX hY).complexity = p.complexity := by
  induction p with
  | output a => simp [comapRandomness, complexity]
  | alice f P ih => simp only [comapRandomness, complexity, ih]
  | bob f P ih => simp only [comapRandomness, complexity, ih]

variable [Fintype Ω_X1] [Fintype Ω_X2] [Fintype Ω_Y1] [Fintype Ω_Y2]

/-- Product of two private-coin protocols. Runs `p1` using the first
component of each coin space, then `p2` using the second, and pairs
their outputs. The total complexity is the sum. -/
def prod
    (p1 : Protocol Ω_X1 Ω_Y1 X Y α₁) (p2 : Protocol Ω_X2 Ω_Y2 X Y α₂) :
    Protocol (Ω_X1 × Ω_X2) (Ω_Y1 × Ω_Y2) X Y (α₁ × α₂) :=
  match p1 with
  | .output a1 =>
      (p2.comapRandomness Prod.snd Prod.snd).map (fun a2 => (a1, a2))
  | alice f P =>
      alice (fun x ω => f x ω.1)
        (fun b => (P b).prod p2)
  | bob f P =>
      bob (fun y ω => f y ω.1)
        (fun b => (P b).prod p2)

@[simp]
theorem prod_run
    (p1 : Protocol Ω_X1 Ω_Y1 X Y α₁) (p2 : Protocol Ω_X2 Ω_Y2 X Y α₂)
    (x : X) (y : Y) (ω_x : Ω_X1 × Ω_X2) (ω_y : Ω_Y1 × Ω_Y2) :
    (p1.prod p2).run x y ω_x ω_y =
      (p1.run x y ω_x.1 ω_y.1, p2.run x y ω_x.2 ω_y.2) := by
  induction p1 with
  | output a1 => simp [prod, run]
  | alice f P ih => simp only [prod, run]; exact ih _
  | bob f P ih => simp only [prod, run]; exact ih _

private theorem finset_sup_add_const {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℕ) (c : ℕ) :
    Finset.univ.sup (fun i => f i + c) =
      Finset.univ.sup f + c := by
  apply le_antisymm
  · apply Finset.sup_le; intro i _
    exact Nat.add_le_add (Finset.le_sup (Finset.mem_univ i)) le_rfl
  · have ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty f
    rw [hj]
    exact Finset.le_sup (f := fun i => f i + c) (Finset.mem_univ j)

theorem prod_complexity
    (p1 : Protocol Ω_X1 Ω_Y1 X Y α₁) (p2 : Protocol Ω_X2 Ω_Y2 X Y α₂) :
    (p1.prod p2).complexity =
      p1.complexity + p2.complexity := by
  induction p1 with
  | output a1 => simp [prod, complexity]
  | alice f P ih =>
    simp only [prod, complexity, ih]
    rw [finset_sup_add_const]; omega
  | bob f P ih =>
    simp only [prod, complexity, ih]
    rw [finset_sup_add_const]; omega

/-- Bind: replace each output `a` in `p` with `q a`. -/
def bind [Fintype Ω_X] [Fintype Ω_Y] :
    Protocol Ω_X Ω_Y X Y α → (α → Protocol Ω_X Ω_Y X Y β) →
      Protocol Ω_X Ω_Y X Y β
  | .output a, q => q a
  | alice f P, q =>
      alice f (fun b => (P b).bind q)
  | bob f P, q =>
      bob f (fun b => (P b).bind q)

@[simp]
theorem bind_run [Fintype Ω_X] [Fintype Ω_Y]
    (p : Protocol Ω_X Ω_Y X Y α) (q : α → Protocol Ω_X Ω_Y X Y β)
    (x : X) (y : Y) (ω_x : Ω_X) (ω_y : Ω_Y) :
    (p.bind q).run x y ω_x ω_y = (q (p.run x y ω_x ω_y)).run x y ω_x ω_y := by
  induction p with
  | output a => simp [bind, run]
  | alice f P ih => simp only [bind, run]; exact ih _
  | bob f P ih => simp only [bind, run]; exact ih _

variable {k : ℕ}
  {Ω_Xf : Fin k → Type*} [∀ i, Fintype (Ω_Xf i)]
  {Ω_Yf : Fin k → Type*} [∀ i, Fintype (Ω_Yf i)]
  {αf : Fin k → Type*}

/-- Pi (k-fold product) of private-coin protocols with heterogeneous
randomness and output types. Runs each `p i` independently using the
`i`-th component of each coin space, collecting outputs into
`(i : Fin k) → αf i`. -/
-- Uses arrow-style binders because structural recursion on `k` requires
-- rebinding all dependent types (including Fintype instances) at each level.
def pi :
    {k : ℕ} →
    {Ω_Xf : Fin k → Type*} → [∀ i, Fintype (Ω_Xf i)] →
    {Ω_Yf : Fin k → Type*} → [∀ i, Fintype (Ω_Yf i)] →
    {αf : Fin k → Type*} →
    ((i : Fin k) → Protocol (Ω_Xf i) (Ω_Yf i) X Y (αf i)) →
      Protocol ((i : Fin k) → Ω_Xf i) ((i : Fin k) → Ω_Yf i) X Y ((i : Fin k) → αf i)
  | 0, _, _, _, _, _, _ => .output (fun i => i.elim0)
  | _ + 1, _, _, _, _, _, p =>
      let head := (p 0).comapRandomness (· 0 : ((i : Fin (_ + 1)) → _) → _)
                    (· 0 : ((i : Fin (_ + 1)) → _) → _)
      let tail := (pi (fun i => p i.succ)).comapRandomness
                    (fun (ω : (i : Fin (_ + 1)) → _) (i : Fin _) => ω i.succ)
                    (fun (ω : (i : Fin (_ + 1)) → _) (i : Fin _) => ω i.succ)
      head.bind (fun a => tail.map (fun as => Fin.cons a as))

theorem bind_complexity_const [Fintype Ω_X] [Fintype Ω_Y]
    (p : Protocol Ω_X Ω_Y X Y α) (q : α → Protocol Ω_X Ω_Y X Y β)
    (c : ℕ) (hc : ∀ a, (q a).complexity = c) :
    (p.bind q).complexity = p.complexity + c := by
  induction p with
  | output a => simp [bind, complexity, hc]
  | alice f P ih =>
    simp only [bind, complexity, ih]
    rw [finset_sup_add_const]; omega
  | bob f P ih =>
    simp only [bind, complexity, ih]
    rw [finset_sup_add_const]; omega

@[simp]
theorem pi_run
    (p : (i : Fin k) → Protocol (Ω_Xf i) (Ω_Yf i) X Y (αf i))
    (x : X) (y : Y) (ω_x : (i : Fin k) → Ω_Xf i) (ω_y : (i : Fin k) → Ω_Yf i) :
    (pi p).run x y ω_x ω_y =
      fun i => (p i).run x y (ω_x i) (ω_y i) := by
  induction k with
  | zero =>
    simp only [pi, run]
    ext i; exact i.elim0
  | succ k ih =>
    simp only [pi, bind_run, comapRandomness_run, map_run, ih]
    ext i; refine Fin.cases ?_ ?_ i
    · simp [Fin.cons]
    · intro j; simp [Fin.cons]

theorem pi_complexity
    (p : (i : Fin k) → Protocol (Ω_Xf i) (Ω_Yf i) X Y (αf i)) :
    (pi p).complexity =
      ∑ i, (p i).complexity := by
  induction k with
  | zero =>
    simp only [pi, complexity, Finset.univ_eq_empty, Finset.sum_empty]
  | succ k ih =>
    simp only [pi]
    have htail : ∀ a,
        (((pi (fun i => p i.succ)).comapRandomness
          (fun (ω : (i : Fin (_ + 1)) → _) (i : Fin _) => ω i.succ)
          (fun (ω : (i : Fin (_ + 1)) → _) (i : Fin _) => ω i.succ)).map
          (fun as => Fin.cons a as)).complexity =
        ∑ i : Fin k, (p i.succ).complexity := by
      intro a; simp [ih]
    rw [bind_complexity_const _ _ _ htail, Fin.sum_univ_succ]; simp

end PrivateCoin.GeneralFiniteMessage.Protocol

end CommunicationComplexity
