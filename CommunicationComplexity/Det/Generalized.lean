import CommunicationComplexity.Det.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Inv
import Mathlib.Data.Nat.Bitwise

/-- A generalized deterministic two-party communication protocol where at each step,
a player sends an element of an arbitrary finite type `β` (rather than just a `Bool`).
This is equivalent to `DetProtocol` up to complexity (see `det_protocol_generalized_to_det_protocol`),
where sending a `β`-valued message costs `⌈log₂ |β|⌉` bits. -/
inductive DetProtocolGeneralized (X Y α : Type*) where
  | output (val : α) : DetProtocolGeneralized X Y α
  | alice {β : Type} [Fintype β] [Nonempty β] (f : X → β) (P : β → DetProtocolGeneralized X Y α) : DetProtocolGeneralized X Y α
  | bob {β : Type} [Fintype β] [Nonempty β] (f : Y → β) (P : β → DetProtocolGeneralized X Y α) : DetProtocolGeneralized X Y α

namespace DetProtocolGeneralized

/-- Executes the generalized protocol on inputs `x` and `y`. -/
def run (p : DetProtocolGeneralized X Y α) (x : X) (y : Y) : α :=
  match p with
  | DetProtocolGeneralized.output val => val
  | DetProtocolGeneralized.alice f P => (P (f x)).run x y
  | DetProtocolGeneralized.bob f P => (P (f y)).run x y

/-- The communication complexity of a generalized protocol. Sending a `β`-valued message
costs `⌈log₂ |β|⌉` bits, reflecting the number of bits needed to encode an element of `β`. -/
def complexity : DetProtocolGeneralized X Y α → ℕ
  | DetProtocolGeneralized.output _ => 0
  | DetProtocolGeneralized.alice (β := β) _ P => (Nat.clog 2 (Fintype.card β)) + Finset.univ.sup (fun i => (P i).complexity)
  | DetProtocolGeneralized.bob (β := β) _ P => (Nat.clog 2 (Fintype.card β)) + Finset.univ.sup (fun i => (P i).complexity)


private def completeTreeAlice (d : ℕ) (query : Fin d → X → Bool)
    (Q : (Fin d → Bool) → DetProtocol X Y α) : DetProtocol X Y α :=
  match d with
  | 0 => Q Fin.elim0
  | d + 1 => DetProtocol.alice (query 0) (fun b =>
      completeTreeAlice d (query ∘ Fin.succ) (fun bits => Q (Fin.cons b bits)))

private theorem completeTreeAlice_run (d : ℕ) (query : Fin d → X → Bool)
    (Q : (Fin d → Bool) → DetProtocol X Y α) (x : X) (y : Y) :
    (completeTreeAlice d query Q).run x y = (Q (fun i => query i x)).run x y := by
  induction d with
  | zero =>
    simp only [completeTreeAlice]
    congr; ext i; exact i.elim0
  | succ d ih =>
    simp only [completeTreeAlice, DetProtocol.run]
    rw [ih]
    -- Goal: (Q (Fin.cons (query 0 x) ...)).run x y = (Q (fun i => query i x)).run x y
    -- Suffices to show the arguments to Q are equal
    have : Fin.cons (query 0 x) (fun i => (query ∘ Fin.succ) i x) = fun i => query i x := by
      ext i; refine Fin.cases ?_ ?_ i
      · simp [Fin.cons]
      · intro j; simp [Fin.cons, Function.comp]
    rw [this]

private theorem completeTreeAlice_complexity (d : ℕ) (query : Fin d → X → Bool)
    (Q : (Fin d → Bool) → DetProtocol X Y α) :
    (completeTreeAlice d query Q).complexity =
      d + Finset.univ.sup (fun bits => (Q bits).complexity) := by
  induction d with
  | zero =>
    simp only [completeTreeAlice, Nat.zero_add]
    have huniq : ∀ (f : Fin 0 → Bool), f = Fin.elim0 := by
      intro f; funext i; exact i.elim0
    have : (Finset.univ : Finset (Fin 0 → Bool)) = {Fin.elim0} := by
      ext x; constructor
      · intro _; simp [huniq x]
      · intro _; exact Finset.mem_univ x
    rw [this, Finset.sup_singleton]
  | succ d ih =>
    -- Unfold to 1 + max (rec false).complexity (rec true).complexity
    simp only [completeTreeAlice, DetProtocol.complexity]
    rw [ih, ih, Nat.succ_add, Nat.add_max_add_left]
    -- Need: max(sup over false-cons, sup over true-cons) = sup over all Fin (d+1) → Bool
    have hsplit : Finset.univ.sup (fun bits : Fin (d + 1) → Bool => (Q bits).complexity) =
        max (Finset.univ.sup (fun bits : Fin d → Bool => (Q (Fin.cons false bits)).complexity))
            (Finset.univ.sup (fun bits : Fin d → Bool => (Q (Fin.cons true bits)).complexity)) := by
      have hdec : (Finset.univ : Finset (Fin (d + 1) → Bool)) =
          (Finset.univ.image (Fin.cons false)) ∪ (Finset.univ.image (Fin.cons true)) := by
        ext bits; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_image, true_and, true_iff]
        by_cases h : bits 0 = true
        · right; exact ⟨Fin.tail bits, by ext i; simp only [Fin.cons]; refine Fin.cases ?_ ?_ i <;> simp [Fin.tail, h]⟩
        · left; exact ⟨Fin.tail bits, by ext i; refine Fin.cases ?_ ?_ i <;> simp [Fin.cons, Fin.tail, Bool.eq_false_iff.mpr h]⟩
      rw [hdec, Finset.sup_union, Finset.sup_image, Finset.sup_image]; rfl
    linarith [hsplit]

/-- Given a function `f : X → β` and binary protocols `Q b` for each `b : β`, constructs
a single binary protocol that simulates choosing `Q (f x)` using `⌈log₂ |β|⌉` alice bits
via a complete binary tree encoding. -/
private theorem encode_alice [Fintype β] [Nonempty β] (f : X → β)
    (Q : β → DetProtocol X Y α) :
    ∃ R : DetProtocol X Y α,
      (∀ x y, R.run x y = (Q (f x)).run x y) ∧
      R.complexity = Nat.clog 2 (Fintype.card β) +
        Finset.univ.sup (fun b => (Q b).complexity) := by
  have hcard : 0 < Fintype.card β := Fintype.card_pos
  let b₀ : β := (Fintype.equivFin β).symm ⟨0, hcard⟩
  let d := Nat.clog 2 (Fintype.card β)
  -- Binary encoding: β → (Fin d → Bool) via Fintype.equivFin then testBit
  let encode : β → (Fin d → Bool) := fun b =>
    fun i => (Fintype.equivFin β b).val.testBit i.val
  have hencode_inj : Function.Injective encode := by
    intro a b hab
    apply (Fintype.equivFin β).injective; apply Fin.ext
    apply Nat.eq_of_testBit_eq; intro i
    by_cases hi : i < d
    · exact congr_fun hab ⟨i, hi⟩
    · have hd : Fintype.card β ≤ 2 ^ d := Nat.le_pow_clog (by norm_num) _
      rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (Fintype.equivFin β a).isLt (hd.trans (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hi)))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (Fintype.equivFin β b).isLt (hd.trans (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hi))))]
  -- Upgrade ∃ to ∃! using injectivity, for use with Fintype.choose
  have hencode_unique : ∀ bits, (∃ b, encode b = bits) → ∃! b, encode b = bits := by
    intro bits ⟨b, hb⟩; exact ⟨b, hb, fun c hc => hencode_inj (hc.trans hb.symm)⟩
  -- Build a complete binary tree of alice queries
  let query : Fin d → X → Bool := fun i x => encode (f x) i
  -- For each bit pattern, use Fintype.choose to find the unique β value (if any)
  let leafQ : (Fin d → Bool) → DetProtocol X Y α :=
    fun bits => if h : ∃ b, encode b = bits then
      Q (Fintype.choose (fun b => encode b = bits) (hencode_unique bits h))
    else Q b₀
  refine ⟨completeTreeAlice d query leafQ, ?_, ?_⟩
  · -- run correctness
    intro x y
    rw [completeTreeAlice_run]
    have hquery : (fun i => query i x) = encode (f x) := rfl
    rw [hquery]
    have hexists : ∃ b, encode b = encode (f x) := ⟨f x, rfl⟩
    simp only [leafQ, hexists, dite_true]
    -- Fintype.choose picks the unique b with encode b = encode (f x); by injectivity it's f x
    have hch := Fintype.choose_spec (fun b => encode b = encode (f x)) (hencode_unique _ hexists)
    rw [hencode_inj hch]
  · -- complexity
    rw [completeTreeAlice_complexity]
    congr 1
    apply le_antisymm
    · apply Finset.sup_le; intro bits _
      by_cases h : ∃ b, encode b = bits
      · simp only [leafQ, h, dite_true]
        exact Finset.le_sup (f := fun b => (Q b).complexity) (Finset.mem_univ _)
      · simp only [leafQ, h, dite_false]
        exact Finset.le_sup (f := fun b => (Q b).complexity) (Finset.mem_univ _)
    · apply Finset.sup_le; intro b _
      have hleafQ : leafQ (encode b) = Q b := by
        have hexb : ∃ b', encode b' = encode b := ⟨b, rfl⟩
        simp only [leafQ, hexb, dite_true]
        congr 1
        have hch := Fintype.choose_spec (fun b' => encode b' = encode b) (hencode_unique _ hexb)
        exact hencode_inj hch
      calc (Q b).complexity
          = (leafQ (encode b)).complexity := by rw [hleafQ]
        _ ≤ Finset.univ.sup (fun bits => (leafQ bits).complexity) :=
            Finset.le_sup (f := fun bits => (leafQ bits).complexity) (Finset.mem_univ _)

/-- Every generalized protocol can be simulated by a binary protocol with the same
complexity. The key idea is to encode each `β`-valued message as `⌈log₂ |β|⌉` bits
using a complete binary tree of depth `⌈log₂ |β|⌉`. -/
theorem det_protocol_generalized_to_det_protocol (p : DetProtocolGeneralized X Y α) : ∃ (P : DetProtocol X Y α), P.run = p.run ∧ P.complexity = p.complexity := by
  induction p with
  | output val => exact ⟨DetProtocol.output val, rfl, rfl⟩
  | @alice β _ _ f P ih =>
    -- Use encode_alice with the IH-provided binary protocols
    choose Q hQ_run hQ_comp using ih
    obtain ⟨R, hR_run, hR_comp⟩ := encode_alice f Q
    exact ⟨R,
      funext fun x => funext fun y => by rw [hR_run, hQ_run, DetProtocolGeneralized.run],
      by rw [hR_comp]; simp [DetProtocolGeneralized.complexity, hQ_comp]⟩
  | @bob β _ _ f P ih =>
    -- Reduce to the alice case: swap the IH protocols, apply encode_alice on Y X α,
    -- then swap the result back.
    choose Q hQ_run hQ_comp using ih
    obtain ⟨R, hR_run, hR_comp⟩ := encode_alice f (fun b => (Q b).swap)
    exact ⟨R.swap,
      funext fun x => funext fun y => by
        simp [DetProtocolGeneralized.run, DetProtocol.swap_run, hR_run, hQ_run],
      by simp [DetProtocolGeneralized.complexity, DetProtocol.swap_complexity, hR_comp,
               DetProtocol.swap_complexity, hQ_comp]⟩

/-- Embed a binary protocol into a generalized protocol (with `β = Bool` at each step). -/
def ofDetProtocol : DetProtocol X Y α → DetProtocolGeneralized X Y α
  | DetProtocol.output val => DetProtocolGeneralized.output val
  | DetProtocol.alice f P => DetProtocolGeneralized.alice f (fun b => ofDetProtocol (P b))
  | DetProtocol.bob f P => DetProtocolGeneralized.bob f (fun b => ofDetProtocol (P b))

theorem ofDetProtocol_run (p : DetProtocol X Y α) (x : X) (y : Y) :
    (ofDetProtocol p).run x y = p.run x y := by
  induction p with
  | output val => simp [ofDetProtocol, run, DetProtocol.run]
  | alice f P ih => simp [ofDetProtocol, run, DetProtocol.run, ih]
  | bob f P ih => simp [ofDetProtocol, run, DetProtocol.run, ih]

theorem ofDetProtocol_complexity (p : DetProtocol X Y α) :
    (ofDetProtocol p).complexity = p.complexity := by
  induction p with
  | output val => simp [ofDetProtocol, complexity, DetProtocol.complexity]
  | alice f P ih =>
    simp only [ofDetProtocol, complexity, DetProtocol.complexity, ih]
    -- clog 2 |Bool| = 1, and sup over Bool = max
    have : Nat.clog 2 (Fintype.card Bool) = 1 := by decide
    rw [this]
    -- Finset.univ for Bool is {false, true}, so sup = max
    have : (Finset.univ : Finset Bool) = {false, true} := by ext b; simp
    simp [this]
  | bob f P ih =>
    simp only [ofDetProtocol, complexity, DetProtocol.complexity, ih]
    have : Nat.clog 2 (Fintype.card Bool) = 1 := by decide
    rw [this]
    have : (Finset.univ : Finset Bool) = {false, true} := by ext b; simp
    simp [this]

/-- Every binary protocol can be viewed as a generalized protocol with the same
run behavior and complexity (using `β = Bool` at each step). -/
theorem det_protocol_to_det_protocol_generalized (p : DetProtocol X Y α) :
    ∃ (P : DetProtocolGeneralized X Y α), P.run = p.run ∧ P.complexity = p.complexity :=
  ⟨ofDetProtocol p, funext fun x => funext fun y => ofDetProtocol_run p x y, ofDetProtocol_complexity p⟩

end DetProtocolGeneralized
