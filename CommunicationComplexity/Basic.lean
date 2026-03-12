import Mathlib

open MeasureTheory ProbabilityTheory

/-- A deterministic two-party communication protocol where Alice holds input `x : X`,
Bob holds input `y : Y`, and the protocol computes a value of type `α`.
At each step, either Alice or Bob sends a single bit based on their input,
and the protocol branches accordingly. -/
inductive DetProtocol (X Y α : Type*) where
  | output (val : α) : DetProtocol X Y α
  | alice (f : X → Bool) (P0 : DetProtocol X Y α) (P1 : DetProtocol X Y α) : DetProtocol X Y α
  | bob (f : Y → Bool) (P0 : DetProtocol X Y α) (P1 : DetProtocol X Y α) : DetProtocol X Y α

namespace DetProtocol

variable {X Y α : Type*}

/-- Executes the protocol on inputs `x` and `y`, returning the output value. -/
def run (p : DetProtocol X Y α) (x : X) (y : Y) : α :=
  match p with
  | DetProtocol.output val => val
  | DetProtocol.alice f P0 P1 => if f x then P1.run x y else P0.run x y
  | DetProtocol.bob f P0 P1 => if f y then P1.run x y else P0.run x y

/-- The communication complexity of a protocol, i.e. the worst-case number of bits exchanged. -/
def complexity : DetProtocol X Y α → ℕ
  | DetProtocol.output _ => 0
  | DetProtocol.alice _ P0 P1 => 1 + max P0.complexity P1.complexity
  | DetProtocol.bob _ P0 P1 => 1 + max P0.complexity P1.complexity

/-- Two protocols are equivalent if they produce the same output on all inputs. -/
def equiv (p q : DetProtocol X Y α) : Prop :=
  ∀ x y, p.run x y = q.run x y

/-- A protocol computes a function `f` if it produces `f x y` on all inputs `(x, y)`. -/
def computes (p : DetProtocol X Y α) (f : X → Y → α) : Prop :=
  ∀ x y, p.run x y = f x y

end DetProtocol

/-- A generalized deterministic two-party communication protocol where at each step,
a player sends an element of an arbitrary finite type `β` (rather than just a `Bool`).
This is equivalent to `DetProtocol` up to complexity (see `det_protocol_gen_to_det_protocol`),
where sending a `β`-valued message costs `⌈log₂ |β|⌉` bits. -/
inductive DetProtocolGen (X Y α : Type*) where
  | output (val : α) : DetProtocolGen X Y α
  | alice {β : Type*} [Fintype β] (f : X → β) (P : β → DetProtocolGen X Y α) : DetProtocolGen X Y α
  | bob {β : Type*} [Fintype β] (f : Y → β) (P : β → DetProtocolGen X Y α) : DetProtocolGen X Y α

namespace DetProtocolGen

/-- Executes the generalized protocol on inputs `x` and `y`. -/
def run (p : DetProtocolGen X Y α) (x : X) (y : Y) : α :=
  match p with
  | DetProtocolGen.output val => val
  | DetProtocolGen.alice f P => (P (f x)).run x y
  | DetProtocolGen.bob f P => (P (f y)).run x y

/-- The communication complexity of a generalized protocol. Sending a `β`-valued message
costs `⌈log₂ |β|⌉` bits, reflecting the number of bits needed to encode an element of `β`. -/
def complexity : DetProtocolGen X Y α → ℕ
  | DetProtocolGen.output _ => 0
  | DetProtocolGen.alice (β := β) _ P => (Nat.clog 2 (Fintype.card β)) + Finset.univ.sup (fun i => (P i).complexity)
  | DetProtocolGen.bob (β := β) _ P => (Nat.clog 2 (Fintype.card β)) + Finset.univ.sup (fun i => (P i).complexity)


private def completeTreeAlice (d : ℕ) (query : Fin d → X → Bool)
    (Q : (Fin d → Bool) → DetProtocol X Y α) : DetProtocol X Y α :=
  match d with
  | 0 => Q Fin.elim0
  | d + 1 => DetProtocol.alice (query 0)
      (completeTreeAlice d (query ∘ Fin.succ) (fun bits => Q (Fin.cons false bits)))
      (completeTreeAlice d (query ∘ Fin.succ) (fun bits => Q (Fin.cons true bits)))

private theorem completeTreeAlice_run (d : ℕ) (query : Fin d → X → Bool)
    (Q : (Fin d → Bool) → DetProtocol X Y α) (x : X) (y : Y) :
    (completeTreeAlice d query Q).run x y = (Q (fun i => query i x)).run x y := by
  induction d with
  | zero =>
    simp only [completeTreeAlice]
    congr; ext i; exact i.elim0
  | succ d ih =>
    simp only [completeTreeAlice, DetProtocol.run]
    have cons_eq : ∀ b, b = query 0 x →
        Fin.cons b (fun j => query (Fin.succ j) x) = fun i => query i x := by
      intro b hb; ext i; refine Fin.cases ?_ ?_ i
      · simp [Fin.cons, hb]
      · intro j; simp [Fin.cons]
    by_cases h : query 0 x = true
    · simp only [h, ↓reduceIte, ih, Function.comp]; rw [cons_eq true h.symm]
    · push_neg at h
      simp only [Bool.eq_false_iff.mpr h, Bool.false_eq_true, ↓reduceIte, ih, Function.comp]
      rw [cons_eq false (Bool.eq_false_iff.mpr h).symm]

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

private def completeTreeBob (d : ℕ) (query : Fin d → Y → Bool)
    (Q : (Fin d → Bool) → DetProtocol X Y α) : DetProtocol X Y α :=
  match d with
  | 0 => Q Fin.elim0
  | d + 1 => DetProtocol.bob (query 0)
      (completeTreeBob d (query ∘ Fin.succ) (fun bits => Q (Fin.cons false bits)))
      (completeTreeBob d (query ∘ Fin.succ) (fun bits => Q (Fin.cons true bits)))

private theorem completeTreeBob_run (d : ℕ) (query : Fin d → Y → Bool)
    (Q : (Fin d → Bool) → DetProtocol X Y α) (x : X) (y : Y) :
    (completeTreeBob d query Q).run x y = (Q (fun i => query i y)).run x y := by
  induction d with
  | zero =>
    simp only [completeTreeBob]
    congr; ext i; exact i.elim0
  | succ d ih =>
    simp only [completeTreeBob, DetProtocol.run]
    have cons_eq : ∀ b, b = query 0 y →
        Fin.cons b (fun j => query (Fin.succ j) y) = fun i => query i y := by
      intro b hb; ext i; refine Fin.cases ?_ ?_ i
      · simp [Fin.cons, hb]
      · intro j; simp [Fin.cons]
    by_cases h : query 0 y = true
    · simp only [h, ↓reduceIte, ih, Function.comp]; rw [cons_eq true h.symm]
    · push_neg at h
      simp only [Bool.eq_false_iff.mpr h, Bool.false_eq_true, ↓reduceIte, ih, Function.comp]
      rw [cons_eq false (Bool.eq_false_iff.mpr h).symm]

private theorem completeTreeBob_complexity (d : ℕ) (query : Fin d → Y → Bool)
    (Q : (Fin d → Bool) → DetProtocol X Y α) :
    (completeTreeBob d query Q).complexity =
      d + Finset.univ.sup (fun bits => (Q bits).complexity) := by
  induction d with
  | zero =>
    simp only [completeTreeBob, Nat.zero_add]
    have huniq : ∀ (f : Fin 0 → Bool), f = Fin.elim0 := by
      intro f; funext i; exact i.elim0
    have : (Finset.univ : Finset (Fin 0 → Bool)) = {Fin.elim0} := by
      ext x; constructor
      · intro _; simp [huniq x]
      · intro _; exact Finset.mem_univ x
    rw [this, Finset.sup_singleton]
  | succ d ih =>
    simp only [completeTreeBob, DetProtocol.complexity]
    rw [ih, ih, Nat.succ_add, Nat.add_max_add_left]
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

/-- Every generalized protocol can be simulated by a binary protocol with the same
complexity. The key idea is to encode each `β`-valued message as `⌈log₂ |β|⌉` bits
using a complete binary tree of depth `⌈log₂ |β|⌉`. -/
theorem det_protocol_gen_to_det_protocol [Nonempty α] (p : DetProtocolGen X Y α) : ∃ (P : DetProtocol X Y α), P.run = p.run ∧ P.complexity = p.complexity := by
  induction p with
  | output val => exact ⟨DetProtocol.output val, rfl, rfl⟩
  | @alice β _ f P ih =>
    classical
    choose Q hQ_run hQ_comp using ih
    let d := Nat.clog 2 (Fintype.card β)
    -- We need an injection β ↪ (Fin d → Bool) since |Fin d → Bool| = 2^d ≥ |β|
    -- Use Fintype.equivFin to get β ≃ Fin |β|, then encode Fin |β| into Fin d → Bool
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
    let query : Fin d → X → Bool := fun i x => encode (f x) i
    let leafQ : (Fin d → Bool) → DetProtocol X Y α :=
      fun bits => if h : ∃ b, encode b = bits then Q (Classical.choose h)
                  else DetProtocol.output (Classical.arbitrary α)
    refine ⟨completeTreeAlice d query leafQ, ?_, ?_⟩
    · -- run correctness
      funext x y
      simp only [DetProtocolGen.run]
      rw [completeTreeAlice_run]
      -- Goal: (leafQ (fun i => query i x)).run x y = (P (f x)).run x y
      -- query i x = encode (f x) i, so fun i => query i x = encode (f x)
      have hquery : (fun i => query i x) = encode (f x) := rfl
      rw [hquery]
      -- leafQ (encode (f x)) = Q (f x) since encode (f x) is in image
      have hexists : ∃ b, encode b = encode (f x) := ⟨f x, rfl⟩
      simp only [leafQ, hexists, dite_true]
      have := Classical.choose_spec hexists
      rw [hencode_inj this, hQ_run]
    · -- complexity
      simp only [DetProtocolGen.complexity]
      rw [completeTreeAlice_complexity]
      congr 1
      -- Need: sup over (Fin d → Bool) of leafQ = sup over β of (P b).complexity
      apply le_antisymm
      · apply Finset.sup_le; intro bits _
        by_cases h : ∃ b, encode b = bits
        · simp only [leafQ, h, dite_true]
          rw [hQ_comp]; exact Finset.le_sup (f := fun b => (P b).complexity) (Finset.mem_univ _)
        · simp only [leafQ, h, dite_false, DetProtocol.complexity]
          exact Nat.zero_le _
      · apply Finset.sup_le; intro b _
        have hleafQ : leafQ (encode b) = Q b := by
          have hexb : ∃ b', encode b' = encode b := ⟨b, rfl⟩
          simp only [leafQ, hexb, dite_true]
          have hspec : encode (Classical.choose hexb) = encode b := Classical.choose_spec hexb
          congr 1; exact hencode_inj hspec
        calc (P b).complexity = (Q b).complexity := (hQ_comp b).symm
          _ = (leafQ (encode b)).complexity := by rw [hleafQ]
          _ ≤ Finset.univ.sup (fun bits => (leafQ bits).complexity) :=
              Finset.le_sup (f := fun bits => (leafQ bits).complexity) (Finset.mem_univ _)
  | @bob β _ f P ih =>
    classical
    choose Q hQ_run hQ_comp using ih
    let d := Nat.clog 2 (Fintype.card β)
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
    let query : Fin d → Y → Bool := fun i y => encode (f y) i
    let leafQ : (Fin d → Bool) → DetProtocol X Y α :=
      fun bits => if h : ∃ b, encode b = bits then Q (Classical.choose h)
                  else DetProtocol.output (Classical.arbitrary α)
    refine ⟨completeTreeBob d query leafQ, ?_, ?_⟩
    · funext x y
      simp only [DetProtocolGen.run]
      rw [completeTreeBob_run]
      have hquery : (fun i => query i y) = encode (f y) := rfl
      rw [hquery]
      have hexists : ∃ b, encode b = encode (f y) := ⟨f y, rfl⟩
      simp only [leafQ, hexists, dite_true]
      have := Classical.choose_spec hexists
      rw [hencode_inj this, hQ_run]
    · simp only [DetProtocolGen.complexity]
      rw [completeTreeBob_complexity]
      congr 1
      apply le_antisymm
      · apply Finset.sup_le; intro bits _
        by_cases h : ∃ b, encode b = bits
        · simp only [leafQ, h, dite_true]
          rw [hQ_comp]; exact Finset.le_sup (f := fun b => (P b).complexity) (Finset.mem_univ _)
        · simp only [leafQ, h, dite_false, DetProtocol.complexity]
          exact Nat.zero_le _
      · apply Finset.sup_le; intro b _
        have hleafQ : leafQ (encode b) = Q b := by
          have hexb : ∃ b', encode b' = encode b := ⟨b, rfl⟩
          simp only [leafQ, hexb, dite_true]
          have hspec : encode (Classical.choose hexb) = encode b := Classical.choose_spec hexb
          congr 1; exact hencode_inj hspec
        calc (P b).complexity = (Q b).complexity := (hQ_comp b).symm
          _ = (leafQ (encode b)).complexity := by rw [hleafQ]
          _ ≤ Finset.univ.sup (fun bits => (leafQ bits).complexity) :=
              Finset.le_sup (f := fun bits => (leafQ bits).complexity) (Finset.mem_univ _)

end DetProtocolGen

/-- A randomized two-party communication protocol. Each player has access to private
randomness (`Ω_X` for Alice, `Ω_Y` for Bob), modeled as probability spaces.
At each step, a player sends a bit that may depend on both their input and their randomness. -/
inductive RandProtocol
    (Ω_X Ω_Y : Type*)
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    [IsProbabilityMeasure (volume : Measure Ω_X)]
    [IsProbabilityMeasure (volume : Measure Ω_Y)]
    (X Y α : Type*) where
  | output (a : α) :
      RandProtocol Ω_X Ω_Y X Y α
  | alice
      (f : X → Ω_X → Bool)
      (hf : ∀ x, Measurable (f x))
      (P0 P1 : RandProtocol Ω_X Ω_Y X Y α) :
      RandProtocol Ω_X Ω_Y X Y α
  | bob
      (f : Y → Ω_Y → Bool)
      (hf : ∀ y, Measurable (f y))
      (P0 P1 : RandProtocol Ω_X Ω_Y X Y α) :
      RandProtocol Ω_X Ω_Y X Y α

namespace RandProtocol

variable {Ω_X Ω_Y X Y α : Type*}
    [MeasureSpace Ω_X] [MeasureSpace Ω_Y]
    [IsProbabilityMeasure (volume : Measure Ω_X)]
    [IsProbabilityMeasure (volume : Measure Ω_Y)]

/-- Executes the randomized protocol on inputs `x`, `y` with random coins `ω_x`, `ω_y`. -/
def run
    (p : RandProtocol Ω_X Ω_Y X Y α) (x : X) (y : Y) (ω_x : Ω_X) (ω_y : Ω_Y) :
    α :=
  match p with
  | RandProtocol.output a => a
  | RandProtocol.alice f _ P0 P1 =>
      if f x ω_x then P1.run x y ω_x ω_y else P0.run x y ω_x ω_y
  | RandProtocol.bob f _ P0 P1 =>
      if f y ω_y then P1.run x y ω_x ω_y else P0.run x y ω_x ω_y

/-- The preimage of any set under the protocol's output is measurable in the product
probability space, which is needed to make sense of error probabilities. -/
theorem measurable_preimage_run
    (p : RandProtocol Ω_X Ω_Y X Y α) (x : X) (y : Y) (s : Set α) :
    MeasurableSet ((fun (ω : Ω_X × Ω_Y) ↦ p.run x y ω.1 ω.2) ⁻¹' s) := by
  induction p with
  | output a =>
    unfold run
    unfold Set.preimage
    simp only [measurableSet_setOf, measurable_const]
  | alice f hf P0 P1 ih0 ih1 =>
    unfold run
    unfold Set.preimage
    have key : {ω : Ω_X × Ω_Y |
        (if f x ω.1 = true then P1.run x y ω.1 ω.2 else P0.run x y ω.1 ω.2) ∈ s} =
      ({ω | f x ω.1 = true} ∩ {ω | P1.run x y ω.1 ω.2 ∈ s}) ∪
      ({ω | ¬(f x ω.1 = true)} ∩ {ω | P0.run x y ω.1 ω.2 ∈ s}) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff]
      by_cases h : f x ω.1 = true <;> simp [h]
    rw [key]
    have hcond : MeasurableSet {ω : Ω_X × Ω_Y | f x ω.1 = true} := by
      have : {ω : Ω_X × Ω_Y | f x ω.1 = true} = (fun ω => f x ω.1) ⁻¹' {true} := by
        ext ω; simp [Set.mem_preimage]
      rw [this]
      exact ((hf x).comp measurable_fst) (measurableSet_singleton true)
    exact (hcond.inter ih1).union (hcond.compl.inter ih0)
  | bob f hf P0 P1 ih0 ih1 =>
    unfold run
    unfold Set.preimage
    have key : {ω : Ω_X × Ω_Y |
        (if f y ω.2 = true then P1.run x y ω.1 ω.2 else P0.run x y ω.1 ω.2) ∈ s} =
      ({ω | f y ω.2 = true} ∩ {ω | P1.run x y ω.1 ω.2 ∈ s}) ∪
      ({ω | ¬(f y ω.2 = true)} ∩ {ω | P0.run x y ω.1 ω.2 ∈ s}) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff]
      by_cases h : f y ω.2 = true <;> simp [h]
    rw [key]
    have hcond : MeasurableSet {ω : Ω_X × Ω_Y | f y ω.2 = true} := by
      have : {ω : Ω_X × Ω_Y | f y ω.2 = true} = (fun ω => f y ω.2) ⁻¹' {true} := by
        ext ω; simp [Set.mem_preimage]
      rw [this]
      exact ((hf y).comp measurable_snd) (measurableSet_singleton true)
    exact (hcond.inter ih1).union (hcond.compl.inter ih0)

/-- A randomized protocol `ε`-computes a function `f` if for every input `(x, y)`,
the probability of outputting a value other than `f x y` is at most `ε`. -/
def approx_computes
    (p : RandProtocol Ω_X Ω_Y X Y α) (f : X → Y → α) (ε : ℝ) : Prop :=
  ∀ x y, (volume {ω : Ω_X × Ω_Y | p.run x y ω.1 ω.2 ≠ f x y}).toReal ≤ ε

end RandProtocol
