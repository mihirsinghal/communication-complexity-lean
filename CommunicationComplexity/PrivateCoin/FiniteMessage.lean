import CommunicationComplexity.PrivateCoin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Inv
import Mathlib.Data.Nat.Bitwise

namespace CommunicationComplexity

/-- A generalized randomized two-party communication protocol with
coin flip randomness. At each step, a player sends an element of an
arbitrary finite type `β`. Alice has `nX` coin flips, Bob has `nY`.
Sending a `β`-valued message costs `⌈log₂ |β|⌉` bits. -/
inductive PrivateCoin.FiniteMessage.Protocol
    (nX nY : ℕ) (X Y α : Type*) where
  | output (a : α) :
      PrivateCoin.FiniteMessage.Protocol nX nY X Y α
  | alice {β : Type} [Fintype β] [Nonempty β]
      (f : X → CoinTape nX → β)
      (P : β → PrivateCoin.FiniteMessage.Protocol nX nY X Y α) :
      PrivateCoin.FiniteMessage.Protocol nX nY X Y α
  | bob {β : Type} [Fintype β] [Nonempty β]
      (f : Y → CoinTape nY → β)
      (P : β → PrivateCoin.FiniteMessage.Protocol nX nY X Y α) :
      PrivateCoin.FiniteMessage.Protocol nX nY X Y α

namespace PrivateCoin.FiniteMessage.Protocol

variable {nX nY : ℕ} {X Y α : Type*}

/-- Executes the generalized randomized protocol on inputs `x`, `y`
with coin flips `ω_x`, `ω_y`. -/
def run (p : Protocol nX nY X Y α)
    (x : X) (y : Y)
    (ω_x : CoinTape nX) (ω_y : CoinTape nY) : α :=
  match p with
  | output a => a
  | alice f P => (P (f x ω_x)).run x y ω_x ω_y
  | bob f P => (P (f y ω_y)).run x y ω_x ω_y

/-- The communication complexity of a generalized randomized protocol.
Sending a `β`-valued message costs `⌈log₂ |β|⌉` bits. -/
def complexity : Protocol nX nY X Y α → ℕ
  | output _ => 0
  | alice (β := β) _ P =>
      Nat.clog 2 (Fintype.card β) +
        Finset.univ.sup (fun i => (P i).complexity)
  | bob (β := β) _ P =>
      Nat.clog 2 (Fintype.card β) +
        Finset.univ.sup (fun i => (P i).complexity)

/-- Swaps the roles of Alice and Bob in a finite-message protocol. -/
def swap : Protocol nX nY X Y α → Protocol nY nX Y X α
  | .output a => .output a
  | alice f P =>
      bob f (fun b => (P b).swap)
  | bob f P =>
      alice f (fun b => (P b).swap)

@[simp]
theorem swap_run (p : Protocol nX nY X Y α) (x : X) (y : Y)
    (ω_x : CoinTape nX) (ω_y : CoinTape nY) :
    p.swap.run y x ω_y ω_x = p.run x y ω_x ω_y := by
  induction p with
  | output a => simp [swap, run]
  | alice f P ih => simp only [swap, run]; exact ih _
  | bob f P ih => simp only [swap, run]; exact ih _

@[simp]
theorem swap_complexity (p : Protocol nX nY X Y α) :
    p.swap.complexity = p.complexity := by
  induction p with
  | output a => simp [swap, complexity]
  | alice f P ih => simp only [swap, complexity, ih]
  | bob f P ih => simp only [swap, complexity, ih]

/-- Embed a binary randomized protocol into a generalized randomized
protocol (with `β = Bool` at each step). -/
def ofProtocol :
    PrivateCoin.Protocol nX nY X Y α →
      Protocol nX nY X Y α
  | PrivateCoin.Protocol.output a => output a
  | PrivateCoin.Protocol.alice f P =>
      alice f (fun b => ofProtocol (P b))
  | PrivateCoin.Protocol.bob f P =>
      bob f (fun b => ofProtocol (P b))

theorem ofProtocol_run
    (p : PrivateCoin.Protocol nX nY X Y α)
    (x : X) (y : Y)
    (ω_x : CoinTape nX) (ω_y : CoinTape nY) :
    (ofProtocol p).run x y ω_x ω_y =
      p.run x y ω_x ω_y := by
  induction p with
  | output a =>
    simp [ofProtocol, run, PrivateCoin.Protocol.run]
  | alice f P ih =>
    simp [ofProtocol, run, PrivateCoin.Protocol.run, ih]
  | bob f P ih =>
    simp [ofProtocol, run, PrivateCoin.Protocol.run, ih]

theorem ofProtocol_complexity
    (p : PrivateCoin.Protocol nX nY X Y α) :
    (ofProtocol p).complexity = p.complexity := by
  induction p with
  | output a =>
    simp [ofProtocol, complexity,
      PrivateCoin.Protocol.complexity]
  | alice f P ih =>
    simp only [ofProtocol, complexity,
      PrivateCoin.Protocol.complexity, ih]
    have : Nat.clog 2 (Fintype.card Bool) = 1 := by decide
    rw [this]
    have : (Finset.univ : Finset Bool) = {false, true} := by
      ext b; simp
    simp [this]
  | bob f P ih =>
    simp only [ofProtocol, complexity,
      PrivateCoin.Protocol.complexity, ih]
    have : Nat.clog 2 (Fintype.card Bool) = 1 := by decide
    rw [this]
    have : (Finset.univ : Finset Bool) = {false, true} := by
      ext b; simp
    simp [this]

-- Helper: build a complete binary tree of alice queries.
private def completeTreeAlice (d : ℕ)
    (query : Fin d → X → CoinTape nX → Bool)
    (Q : (Fin d → Bool) → PrivateCoin.Protocol nX nY X Y α) :
    PrivateCoin.Protocol nX nY X Y α :=
  match d with
  | 0 => Q Fin.elim0
  | d + 1 => PrivateCoin.Protocol.alice (query 0)
      fun b => completeTreeAlice d (query ∘ Fin.succ)
        (fun bits => Q (Fin.cons b bits))

private theorem completeTreeAlice_run (d : ℕ)
    (query : Fin d → X → CoinTape nX → Bool)
    (Q : (Fin d → Bool) → PrivateCoin.Protocol nX nY X Y α)
    (x : X) (y : Y)
    (ω_x : CoinTape nX) (ω_y : CoinTape nY) :
    (completeTreeAlice d query Q).run x y ω_x ω_y =
      (Q (fun i => query i x ω_x)).run x y ω_x ω_y := by
  induction d with
  | zero =>
    simp only [completeTreeAlice]
    congr; ext i; exact i.elim0
  | succ d ih =>
    simp only [completeTreeAlice, PrivateCoin.Protocol.run]
    rw [ih]
    have : Fin.cons (query 0 x ω_x)
        (fun i => (query ∘ Fin.succ) i x ω_x) =
        fun i => query i x ω_x := by
      ext i; refine Fin.cases ?_ ?_ i
      · simp [Fin.cons]
      · intro j; simp [Fin.cons, Function.comp]
    rw [this]

private theorem completeTreeAlice_complexity (d : ℕ)
    (query : Fin d → X → CoinTape nX → Bool)
    (Q : (Fin d → Bool) → PrivateCoin.Protocol nX nY X Y α) :
    (completeTreeAlice d query Q).complexity =
      d + Finset.univ.sup
        (fun bits => (Q bits).complexity) := by
  induction d with
  | zero =>
    simp only [completeTreeAlice, Nat.zero_add]
    have huniq : ∀ (f : Fin 0 → Bool), f = Fin.elim0 := by
      intro f; funext i; exact i.elim0
    have : (Finset.univ : Finset (Fin 0 → Bool)) =
        {Fin.elim0} := by
      ext x; constructor
      · intro _; simp [huniq x]
      · intro _; exact Finset.mem_univ x
    rw [this, Finset.sup_singleton]
  | succ d ih =>
    simp only [completeTreeAlice,
      PrivateCoin.Protocol.complexity]
    rw [ih, ih, Nat.succ_add, Nat.add_max_add_left]
    have hsplit :
        Finset.univ.sup (fun bits : Fin (d + 1) → Bool =>
          (Q bits).complexity) =
        max (Finset.univ.sup (fun bits : Fin d → Bool =>
              (Q (Fin.cons false bits)).complexity))
            (Finset.univ.sup (fun bits : Fin d → Bool =>
              (Q (Fin.cons true bits)).complexity)) := by
      have hdec :
          (Finset.univ : Finset (Fin (d + 1) → Bool)) =
          (Finset.univ.image (Fin.cons false)) ∪
          (Finset.univ.image (Fin.cons true)) := by
        ext bits
        simp only [Finset.mem_univ, Finset.mem_union,
          Finset.mem_image, true_and, true_iff]
        by_cases h : bits 0 = true
        · right; exact ⟨Fin.tail bits, by
            ext i; simp only [Fin.cons]
            refine Fin.cases ?_ ?_ i <;>
              simp [Fin.tail, h]⟩
        · left; exact ⟨Fin.tail bits, by
            ext i; refine Fin.cases ?_ ?_ i <;>
              simp [Fin.cons, Fin.tail,
                Bool.eq_false_iff.mpr h]⟩
      rw [hdec, Finset.sup_union, Finset.sup_image,
        Finset.sup_image]; rfl
    linarith [hsplit]

private theorem encode_alice [Fintype β] [Nonempty β]
    (f : X → CoinTape nX → β)
    (Q : β → PrivateCoin.Protocol nX nY X Y α) :
    ∃ R : PrivateCoin.Protocol nX nY X Y α,
      (∀ x y ω_x ω_y,
        R.run x y ω_x ω_y =
          (Q (f x ω_x)).run x y ω_x ω_y) ∧
      R.complexity = Nat.clog 2 (Fintype.card β) +
        Finset.univ.sup (fun b => (Q b).complexity) := by
  have hcard : 0 < Fintype.card β := Fintype.card_pos
  let b₀ : β := (Fintype.equivFin β).symm ⟨0, hcard⟩
  let d := Nat.clog 2 (Fintype.card β)
  let encode : β → (Fin d → Bool) := fun b =>
    fun i => (Fintype.equivFin β b).val.testBit i.val
  have hencode_inj : Function.Injective encode := by
    intro a b hab
    apply (Fintype.equivFin β).injective; apply Fin.ext
    apply Nat.eq_of_testBit_eq; intro i
    by_cases hi : i < d
    · exact congr_fun hab ⟨i, hi⟩
    · have hd : Fintype.card β ≤ 2 ^ d :=
        Nat.le_pow_clog (by norm_num) _
      have hle := hd.trans
        (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hi))
      rw [Nat.testBit_eq_false_of_lt
            (lt_of_lt_of_le
              (Fintype.equivFin β a).isLt hle),
          Nat.testBit_eq_false_of_lt
            (lt_of_lt_of_le
              (Fintype.equivFin β b).isLt hle)]
  have hencode_unique :
      ∀ bits, (∃ b, encode b = bits) →
        ∃! b, encode b = bits := by
    intro bits ⟨b, hb⟩
    exact ⟨b, hb, fun c hc =>
      hencode_inj (hc.trans hb.symm)⟩
  let query : Fin d → X → CoinTape nX → Bool :=
    fun i x ω_x => encode (f x ω_x) i
  let leafQ :
      (Fin d → Bool) →
        PrivateCoin.Protocol nX nY X Y α :=
    fun bits => if h : ∃ b, encode b = bits then
      Q (Fintype.choose (fun b => encode b = bits)
        (hencode_unique bits h))
    else Q b₀
  refine ⟨completeTreeAlice d query leafQ, ?_, ?_⟩
  · intro x y ω_x ω_y
    rw [completeTreeAlice_run]
    have hquery_eq :
        (fun i => query i x ω_x) =
          encode (f x ω_x) := rfl
    rw [hquery_eq]
    have hexists :
        ∃ b, encode b = encode (f x ω_x) :=
      ⟨f x ω_x, rfl⟩
    simp only [leafQ, hexists, dite_true]
    have hch := Fintype.choose_spec
      (fun b => encode b = encode (f x ω_x))
      (hencode_unique _ hexists)
    rw [hencode_inj hch]
  · rw [completeTreeAlice_complexity]
    congr 1
    apply le_antisymm
    · apply Finset.sup_le; intro bits _
      by_cases h : ∃ b, encode b = bits
      · simp only [leafQ, h, dite_true]
        exact Finset.le_sup
          (f := fun b => (Q b).complexity)
          (Finset.mem_univ _)
      · simp only [leafQ, h, dite_false]
        exact Finset.le_sup
          (f := fun b => (Q b).complexity)
          (Finset.mem_univ _)
    · apply Finset.sup_le; intro b _
      have hleafQ : leafQ (encode b) = Q b := by
        have hexb :
            ∃ b', encode b' = encode b := ⟨b, rfl⟩
        simp only [leafQ, hexb, dite_true]
        congr 1
        have hch := Fintype.choose_spec
          (fun b' => encode b' = encode b)
          (hencode_unique _ hexb)
        exact hencode_inj hch
      calc (Q b).complexity
          = (leafQ (encode b)).complexity := by
            rw [hleafQ]
        _ ≤ Finset.univ.sup
              (fun bits => (leafQ bits).complexity) :=
            Finset.le_sup
              (f := fun bits =>
                (leafQ bits).complexity)
              (Finset.mem_univ _)

/-- Every generalized randomized protocol can be simulated by a
binary randomized protocol with the same complexity. -/
theorem toProtocol (p : Protocol nX nY X Y α) :
    ∃ (P : PrivateCoin.Protocol nX nY X Y α),
      P.run = p.run ∧ P.complexity = p.complexity := by
  induction p with
  | output a =>
    exact ⟨PrivateCoin.Protocol.output a, rfl, rfl⟩
  | @alice β _ _ f P ih =>
    choose Q hQ_run hQ_comp using ih
    obtain ⟨R, hR_run, hR_comp⟩ := encode_alice f Q
    exact ⟨R,
      funext₂ fun x y => funext₂ fun ω_x ω_y => by
        rw [hR_run, hQ_run]; rfl,
      by rw [hR_comp]
         simp [complexity, hQ_comp]⟩
  | @bob β _ _ f P ih =>
    choose Q hQ_run hQ_comp using ih
    obtain ⟨R, hR_run, hR_comp⟩ :=
      encode_alice f (fun b => (Q b).swap)
    exact ⟨R.swap,
      funext₂ fun x y => funext₂ fun ω_x ω_y => by
        simp [run, PrivateCoin.Protocol.swap_run,
          hR_run, hQ_run],
      by simp [complexity,
           PrivateCoin.Protocol.swap_complexity,
           hR_comp, hQ_comp]⟩

/-- Every binary randomized protocol can be viewed as a generalized
randomized protocol with the same run behavior and complexity. -/
theorem ofProtocol_equiv
    (p : PrivateCoin.Protocol nX nY X Y α) :
    ∃ (P : Protocol nX nY X Y α),
      P.run = p.run ∧ P.complexity = p.complexity :=
  ⟨ofProtocol p,
   funext₂ fun x y => funext₂ fun ω_x ω_y =>
     ofProtocol_run p x y ω_x ω_y,
   ofProtocol_complexity p⟩

end PrivateCoin.FiniteMessage.Protocol

end CommunicationComplexity
