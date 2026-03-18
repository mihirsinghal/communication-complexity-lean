import CommunicationComplexity.PublicCoin.GeneralFiniteMessage
import Mathlib.Algebra.BigOperators.Fin

namespace CommunicationComplexity

namespace PublicCoin.GeneralFiniteMessage.Protocol

variable {Ω Ω₁ Ω₂ X Y α α₁ α₂ β : Type*}

/-- Map a function over the output of a protocol. -/
def map [Fintype Ω] (g : α → β) :
    Protocol Ω X Y α → Protocol Ω X Y β
  | .output a => .output (g a)
  | alice f P =>
      alice f (fun b => (P b).map g)
  | bob f P =>
      bob f (fun b => (P b).map g)

@[simp]
theorem map_run [Fintype Ω] (g : α → β)
    (p : Protocol Ω X Y α) (x : X) (y : Y) (ω : Ω) :
    (p.map g).run x y ω = g (p.run x y ω) := by
  induction p with
  | output a => simp [map, run]
  | alice f P ih => simp only [map, run]; exact ih _
  | bob f P ih => simp only [map, run]; exact ih _

@[simp]
theorem map_complexity [Fintype Ω] (g : α → β)
    (p : Protocol Ω X Y α) :
    (p.map g).complexity = p.complexity := by
  induction p with
  | output a => simp [map, complexity]
  | alice f P ih => simp only [map, complexity, ih]
  | bob f P ih => simp only [map, complexity, ih]

variable {Ω' : Type*}

/-- Reindex the randomness space of a protocol via a map `h : Ω' → Ω`. -/
def comapRandomness [Fintype Ω] [Fintype Ω'] (h : Ω' → Ω) :
    Protocol Ω X Y α → Protocol Ω' X Y α
  | .output a => .output a
  | alice f P =>
      alice (fun x ω => f x (h ω))
        (fun b => (P b).comapRandomness h)
  | bob f P =>
      bob (fun y ω => f y (h ω))
        (fun b => (P b).comapRandomness h)

@[simp]
theorem comapRandomness_run [Fintype Ω] [Fintype Ω']
    (h : Ω' → Ω) (p : Protocol Ω X Y α)
    (x : X) (y : Y) (ω : Ω') :
    (p.comapRandomness h).run x y ω = p.run x y (h ω) := by
  induction p with
  | output a => simp [comapRandomness, run]
  | alice f P ih => simp only [comapRandomness, run]; exact ih _
  | bob f P ih => simp only [comapRandomness, run]; exact ih _

@[simp]
theorem comapRandomness_complexity [Fintype Ω] [Fintype Ω']
    (h : Ω' → Ω) (p : Protocol Ω X Y α) :
    (p.comapRandomness h).complexity = p.complexity := by
  induction p with
  | output a => simp [comapRandomness, complexity]
  | alice f P ih => simp only [comapRandomness, complexity, ih]
  | bob f P ih => simp only [comapRandomness, complexity, ih]

variable [Fintype Ω₁] [Fintype Ω₂]

/-- Product of two public-coin protocols. Runs `p1` using the first
component of `Ω₁ × Ω₂`, then `p2` using the second, and pairs their
outputs. The total complexity is the sum. -/
def prod
    (p1 : Protocol Ω₁ X Y α₁) (p2 : Protocol Ω₂ X Y α₂) :
    Protocol (Ω₁ × Ω₂) X Y (α₁ × α₂) :=
  match p1 with
  | .output a1 =>
      (p2.comapRandomness Prod.snd).map (fun a2 => (a1, a2))
  | alice f P =>
      alice (fun x ω => f x ω.1)
        (fun b => (P b).prod p2)
  | bob f P =>
      bob (fun y ω => f y ω.1)
        (fun b => (P b).prod p2)

@[simp]
theorem prod_run
    (p1 : Protocol Ω₁ X Y α₁) (p2 : Protocol Ω₂ X Y α₂)
    (x : X) (y : Y) (ω : Ω₁ × Ω₂) :
    (p1.prod p2).run x y ω =
      (p1.run x y ω.1, p2.run x y ω.2) := by
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
    (p1 : Protocol Ω₁ X Y α₁) (p2 : Protocol Ω₂ X Y α₂) :
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
def bind [Fintype Ω] :
    Protocol Ω X Y α → (α → Protocol Ω X Y β) →
      Protocol Ω X Y β
  | .output a, q => q a
  | alice f P, q =>
      alice f (fun b => (P b).bind q)
  | bob f P, q =>
      bob f (fun b => (P b).bind q)

@[simp]
theorem bind_run [Fintype Ω]
    (p : Protocol Ω X Y α) (q : α → Protocol Ω X Y β)
    (x : X) (y : Y) (ω : Ω) :
    (p.bind q).run x y ω = (q (p.run x y ω)).run x y ω := by
  induction p with
  | output a => simp [bind, run]
  | alice f P ih => simp only [bind, run]; exact ih _
  | bob f P ih => simp only [bind, run]; exact ih _

variable {k : ℕ} {Ωf : Fin k → Type*} [∀ i, Fintype (Ωf i)]
  {αf : Fin k → Type*}

/-- Pi (k-fold product) of protocols with heterogeneous randomness and
output types. Runs each `p i` independently using the `i`-th component
of the shared randomness `(i : Fin k) → Ωf i`, collecting outputs into
`(i : Fin k) → αf i`. -/
-- Uses arrow-style binders because structural recursion on `k` requires
-- rebinding all dependent types (including Fintype instances) at each level.
def pi :
    {k : ℕ} → {Ωf : Fin k → Type*} → [∀ i, Fintype (Ωf i)] →
    {αf : Fin k → Type*} →
    ((i : Fin k) → Protocol (Ωf i) X Y (αf i)) →
      Protocol ((i : Fin k) → Ωf i) X Y ((i : Fin k) → αf i)
  | 0, _, _, _, _ => .output (fun i => i.elim0)
  | _ + 1, _, _, _, p =>
      let head := (p 0).comapRandomness (· 0 : ((i : Fin (_ + 1)) → _) → _)
      let tail := (pi (fun i => p i.succ)).comapRandomness
                    (fun (ω : (i : Fin (_ + 1)) → _) (i : Fin _) => ω i.succ)
      head.bind (fun a => tail.map (fun as => Fin.cons a as))

theorem bind_complexity_const [Fintype Ω]
    (p : Protocol Ω X Y α) (q : α → Protocol Ω X Y β)
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
    (p : (i : Fin k) → Protocol (Ωf i) X Y (αf i))
    (x : X) (y : Y) (ω : (i : Fin k) → Ωf i) :
    (pi p).run x y ω =
      fun i => (p i).run x y (ω i) := by
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
    (p : (i : Fin k) → Protocol (Ωf i) X Y (αf i)) :
    (pi p).complexity =
      ∑ i, (p i).complexity := by
  induction k with
  | zero =>
    simp only [pi, complexity, Finset.univ_eq_empty, Finset.sum_empty]
  | succ k ih =>
    simp only [pi]
    have htail : ∀ a,
        (((pi (fun i => p i.succ)).comapRandomness
          (fun (ω : (i : Fin (_ + 1)) → _) (i : Fin _) => ω i.succ)).map
          (fun as => Fin.cons a as)).complexity =
        ∑ i : Fin k, (p i.succ).complexity := by
      intro a; simp [ih]
    rw [bind_complexity_const _ _ _ htail, Fin.sum_univ_succ]; simp

end PublicCoin.GeneralFiniteMessage.Protocol

end CommunicationComplexity
