import CommunicationComplexity.PublicCoin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Inv
import Mathlib.Data.Nat.Bitwise

namespace CommunicationComplexity

/-- A public-coin two-party communication protocol where at each step,
a player sends an element of an arbitrary finite type `β`.
Both players share the same `CoinTape n`.
Sending a `β`-valued message costs `⌈log₂ |β|⌉` bits. -/
inductive PublicCoin.FiniteMessage.Protocol
    (n : ℕ) (X Y α : Type*) where
  | output (a : α) :
      PublicCoin.FiniteMessage.Protocol n X Y α
  | alice {β : Type} [Fintype β] [Nonempty β]
      (f : X → CoinTape n → β)
      (P : β → PublicCoin.FiniteMessage.Protocol n X Y α) :
      PublicCoin.FiniteMessage.Protocol n X Y α
  | bob {β : Type} [Fintype β] [Nonempty β]
      (f : Y → CoinTape n → β)
      (P : β → PublicCoin.FiniteMessage.Protocol n X Y α) :
      PublicCoin.FiniteMessage.Protocol n X Y α

namespace PublicCoin.FiniteMessage.Protocol

variable {n : ℕ} {X Y α : Type*}

/-- Executes the public-coin finite-message protocol on inputs `x`, `y`
with shared coin flips `ω`. -/
def run (p : Protocol n X Y α)
    (x : X) (y : Y) (ω : CoinTape n) : α :=
  match p with
  | output a => a
  | alice f P => (P (f x ω)).run x y ω
  | bob f P => (P (f y ω)).run x y ω

/-- The communication complexity of a public-coin finite-message protocol.
Sending a `β`-valued message costs `⌈log₂ |β|⌉` bits. -/
def complexity : Protocol n X Y α → ℕ
  | output _ => 0
  | alice (β := β) _ P =>
      Nat.clog 2 (Fintype.card β) +
        Finset.univ.sup (fun i => (P i).complexity)
  | bob (β := β) _ P =>
      Nat.clog 2 (Fintype.card β) +
        Finset.univ.sup (fun i => (P i).complexity)

/-- Swaps the roles of Alice and Bob. -/
def swap : Protocol n X Y α → Protocol n Y X α
  | .output a => .output a
  | alice f P =>
      bob f (fun b => (P b).swap)
  | bob f P =>
      alice f (fun b => (P b).swap)

@[simp]
theorem swap_run (p : Protocol n X Y α) (x : X) (y : Y)
    (ω : CoinTape n) :
    p.swap.run y x ω = p.run x y ω := by
  induction p with
  | output a => simp [swap, run]
  | alice f P ih => simp only [swap, run]; exact ih _
  | bob f P ih => simp only [swap, run]; exact ih _

@[simp]
theorem swap_complexity (p : Protocol n X Y α) :
    p.swap.complexity = p.complexity := by
  induction p with
  | output a => simp [swap, complexity]
  | alice f P ih => simp only [swap, complexity, ih]
  | bob f P ih => simp only [swap, complexity, ih]

/-- Embed a binary public-coin protocol into a finite-message
public-coin protocol (with `β = Bool` at each step). -/
def ofProtocol :
    PublicCoin.Protocol n X Y α →
      Protocol n X Y α
  | PublicCoin.Protocol.output a => output a
  | PublicCoin.Protocol.alice f P =>
      alice f (fun b => ofProtocol (P b))
  | PublicCoin.Protocol.bob f P =>
      bob f (fun b => ofProtocol (P b))

theorem ofProtocol_run
    (p : PublicCoin.Protocol n X Y α)
    (x : X) (y : Y) (ω : CoinTape n) :
    (ofProtocol p).run x y ω =
      p.run x y ω := by
  induction p with
  | output a =>
    simp [ofProtocol, run, PublicCoin.Protocol.run]
  | alice f P ih =>
    simp [ofProtocol, run, PublicCoin.Protocol.run, ih]
  | bob f P ih =>
    simp [ofProtocol, run, PublicCoin.Protocol.run, ih]

theorem ofProtocol_complexity
    (p : PublicCoin.Protocol n X Y α) :
    (ofProtocol p).complexity = p.complexity := by
  induction p with
  | output a =>
    simp [ofProtocol, complexity,
      PublicCoin.Protocol.complexity]
  | alice f P ih =>
    simp only [ofProtocol, complexity,
      PublicCoin.Protocol.complexity, ih]
    have : Nat.clog 2 (Fintype.card Bool) = 1 := by decide
    rw [this]
    have : (Finset.univ : Finset Bool) = {false, true} := by
      ext b; simp
    simp [this]
  | bob f P ih =>
    simp only [ofProtocol, complexity,
      PublicCoin.Protocol.complexity, ih]
    have : Nat.clog 2 (Fintype.card Bool) = 1 := by decide
    rw [this]
    have : (Finset.univ : Finset Bool) = {false, true} := by
      ext b; simp
    simp [this]

/-- Every binary public-coin protocol can be viewed as a finite-message
public-coin protocol with the same run behavior and complexity. -/
theorem ofProtocol_equiv
    (p : PublicCoin.Protocol n X Y α) :
    ∃ (P : Protocol n X Y α),
      P.run = p.run ∧ P.complexity = p.complexity :=
  ⟨ofProtocol p,
   funext₂ fun x y => funext fun ω =>
     ofProtocol_run p x y ω,
   ofProtocol_complexity p⟩

-- Helper: build a complete binary tree of alice queries (public coin).
private def completeTreeAlice (d : ℕ)
    (query : Fin d → X → CoinTape n → Bool)
    (Q : (Fin d → Bool) → PublicCoin.Protocol n X Y α) :
    PublicCoin.Protocol n X Y α :=
  match d with
  | 0 => Q Fin.elim0
  | d + 1 => PublicCoin.Protocol.alice (query 0)
      fun b => completeTreeAlice d (query ∘ Fin.succ)
        (fun bits => Q (Fin.cons b bits))

private theorem completeTreeAlice_run (d : ℕ)
    (query : Fin d → X → CoinTape n → Bool)
    (Q : (Fin d → Bool) → PublicCoin.Protocol n X Y α)
    (x : X) (y : Y) (ω : CoinTape n) :
    (completeTreeAlice d query Q).run x y ω =
      (Q (fun i => query i x ω)).run x y ω := by
  induction d with
  | zero =>
    simp only [completeTreeAlice]
    congr; ext i; exact i.elim0
  | succ d ih =>
    simp only [completeTreeAlice, PublicCoin.Protocol.run]
    rw [ih]
    have : Fin.cons (query 0 x ω)
        (fun i => (query ∘ Fin.succ) i x ω) =
        fun i => query i x ω := by
      ext i; refine Fin.cases ?_ ?_ i
      · simp [Fin.cons]
      · intro j; simp [Fin.cons, Function.comp]
    rw [this]

private theorem completeTreeAlice_complexity (d : ℕ)
    (query : Fin d → X → CoinTape n → Bool)
    (Q : (Fin d → Bool) → PublicCoin.Protocol n X Y α) :
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
      PublicCoin.Protocol.complexity]
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
    (f : X → CoinTape n → β)
    (Q : β → PublicCoin.Protocol n X Y α) :
    ∃ R : PublicCoin.Protocol n X Y α,
      (∀ x y ω,
        R.run x y ω =
          (Q (f x ω)).run x y ω) ∧
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
  let query : Fin d → X → CoinTape n → Bool :=
    fun i x ω => encode (f x ω) i
  let leafQ :
      (Fin d → Bool) →
        PublicCoin.Protocol n X Y α :=
    fun bits => if h : ∃ b, encode b = bits then
      Q (Fintype.choose (fun b => encode b = bits)
        (hencode_unique bits h))
    else Q b₀
  refine ⟨completeTreeAlice d query leafQ, ?_, ?_⟩
  · intro x y ω
    rw [completeTreeAlice_run]
    have hquery_eq :
        (fun i => query i x ω) =
          encode (f x ω) := rfl
    rw [hquery_eq]
    have hexists :
        ∃ b, encode b = encode (f x ω) :=
      ⟨f x ω, rfl⟩
    simp only [leafQ, hexists, dite_true]
    have hch := Fintype.choose_spec
      (fun b => encode b = encode (f x ω))
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

/-- Every public-coin finite-message protocol can be simulated by a
binary public-coin protocol with the same complexity. -/
theorem toProtocol (p : Protocol n X Y α) :
    ∃ (P : PublicCoin.Protocol n X Y α),
      P.run = p.run ∧ P.complexity = p.complexity := by
  induction p with
  | output a =>
    exact ⟨PublicCoin.Protocol.output a, rfl, rfl⟩
  | alice f P ih =>
    choose Q hQ_run hQ_comp using ih
    obtain ⟨R, hR_run, hR_comp⟩ := encode_alice f Q
    exact ⟨R,
      funext₂ fun x y => funext fun ω => by
        rw [hR_run, hQ_run]; rfl,
      by rw [hR_comp]
         simp [complexity, hQ_comp]⟩
  | bob f P ih =>
    choose Q hQ_run hQ_comp using ih
    obtain ⟨R, hR_run, hR_comp⟩ :=
      encode_alice f (fun b => (Q b).swap)
    exact ⟨R.swap,
      funext₂ fun x y => funext fun ω => by
        simp [run, PublicCoin.Protocol.swap_run,
          hR_run, hQ_run],
      by simp [complexity,
           PublicCoin.Protocol.swap_complexity,
           hR_comp, hQ_comp]⟩

open MeasureTheory

/-- A public-coin finite-message protocol `ε`-satisfies a predicate `Q`
if for every input `(x, y)`, the probability that
`Q x y (p.run ...)` fails is at most `ε`. -/
def approx_satisfies
    (p : Protocol n X Y α) (Q : X → Y → α → Prop)
    (ε : ℝ) : Prop :=
  ∀ x y,
    (volume {ω : CoinTape n |
      ¬Q x y (p.run x y ω)}).toReal ≤ ε

open Classical in
/-- A public-coin finite-message protocol `ε`-computes a function `f`
if for every input `(x, y)`, the probability of producing an
incorrect answer is at most `ε`. -/
def approx_computes
    (p : Protocol n X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y,
    (volume {ω : CoinTape n |
      p.run x y ω ≠ f x y}).toReal ≤ ε

end PublicCoin.FiniteMessage.Protocol

end CommunicationComplexity
