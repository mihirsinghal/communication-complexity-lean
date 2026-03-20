import CommunicationComplexity.PublicCoin.Derandomization
import CommunicationComplexity.PublicCoin.Complexity
import CommunicationComplexity.PrivateCoin.Complexity
import CommunicationComplexity.PrivateCoin.FiniteMessage
import CommunicationComplexity.Comparison

/-!
# Newman's Theorem: Public Coin to Private Coin Reduction

A public-coin protocol can be simulated by a private-coin protocol
with only O(log(|X|·|Y|)) additional random bits, at the cost of
slightly increasing the error.

## Direct conversion

The simplest conversion from public-coin to private-coin: Alice
has `n` private coin bits, sends them all to Bob as a single
`CoinTape n`-valued message (costing `n` bits), then both
deterministically simulate the public-coin protocol.

## Newman's theorem

By Chernoff + union bound, only O(log(|X|·|Y|)/ε²) random seeds
are needed, giving a much cheaper conversion.
-/

open MeasureTheory ProbabilityTheory

namespace CommunicationComplexity

/-- Unit with the Dirac probability measure. -/
noncomputable instance Unit.measureSpace : MeasureSpace Unit :=
  ⟨Measure.dirac ()⟩

instance Unit.isProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure Unit) := by
  constructor
  simp [volume, Unit.measureSpace, Measure.dirac_apply_of_mem (Set.mem_univ ())]

namespace PublicCoin

/-- The number of random seeds Alice samples from in the Newman
reduction: `Fin (derandomizationSamples X Y ε c)`. -/
noncomputable abbrev newmanIndexSpace
    (X Y : Type*) [Fintype X] [Fintype Y] (ε c : ℝ) :=
  Fin (FiniteMessage.Protocol.derandomizationSamples X Y ε c)

noncomputable instance newmanIndexSpace.fintype
    (X Y : Type*) [Fintype X] [Fintype Y] (ε c : ℝ) :
    Fintype (newmanIndexSpace X Y ε c) := inferInstance

noncomputable instance newmanIndexSpace.nonempty
    (X Y : Type*) [Fintype X] [Fintype Y] (ε c : ℝ) :
    Nonempty (newmanIndexSpace X Y ε c) :=
  ⟨⟨0, by simp [FiniteMessage.Protocol.derandomizationSamples]⟩⟩

noncomputable instance newmanIndexSpace.measureSpace
    (X Y : Type*) [Fintype X] [Fintype Y] (ε c : ℝ) :
    MeasureSpace (newmanIndexSpace X Y ε c) :=
  ⟨ProbabilityTheory.uniformOn Set.univ⟩

noncomputable instance newmanIndexSpace.isProbabilityMeasure
    (X Y : Type*) [Fintype X] [Fintype Y] (ε c : ℝ) :
    IsProbabilityMeasure (volume : Measure (newmanIndexSpace X Y ε c)) := by
  change IsProbabilityMeasure (ProbabilityTheory.uniformOn Set.univ)
  infer_instance

/-- The Newman reduction: given a public-coin protocol that ε-computes f,
construct a private-coin protocol where Alice samples a random index i
from `newmanIndexSpace` and sends it to Bob. Both then simulate the
public-coin protocol with the i-th seed from a fixed table of good
randomness values (chosen via Chernoff + union bound). -/
noncomputable def FiniteMessage.Protocol.newmanProtocol
    {Ω X Y α : Type*} [Fintype Ω]
    [Fintype X] [Fintype Y]
    [MeasureSpace Ω] [DiscreteMeasurableSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    (p : FiniteMessage.Protocol Ω X Y α)
    (f : X → Y → α) (ε c : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hc : 1 < c)
    (hp : p.ApproxComputes f ε) :
    PrivateCoin.FiniteMessage.Protocol
      (newmanIndexSpace X Y ε c) Unit X Y α :=
  -- Choose good randomness values via Chernoff + union bound
  let ωs := (FiniteMessage.Protocol.exists_good_randomness
    p f ε c hε hε1 hc hp).choose
  -- Alice sends her random index i ∈ newmanIndexSpace to Bob,
  -- then both simulate with ωs(i)
  @Deterministic.FiniteMessage.Protocol.alice
    (newmanIndexSpace X Y ε c × X) (Unit × Y) α
    (newmanIndexSpace X Y ε c) inferInstance inferInstance
    Prod.fst
    (fun i => (p.toDeterministic (ωs i)).toPrivateCoin)

theorem FiniteMessage.Protocol.newmanProtocol_ApproxComputes
    {Ω X Y α : Type*} [Fintype Ω]
    [Fintype X] [Fintype Y]
    [MeasureSpace Ω] [DiscreteMeasurableSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    (p : FiniteMessage.Protocol Ω X Y α)
    (f : X → Y → α) (ε c : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hc : 1 < c)
    (hp : p.ApproxComputes f ε) :
    (p.newmanProtocol f ε c hε hε1 hc hp).ApproxComputes f (c * ε) := by
  -- ApproxComputes means: for all x y, P[rrun ≠ f x y] ≤ c * ε
  -- on the product space newmanIndexSpace × Unit
  intro x y
  -- Unfold the protocol definition to get at the run behavior
  unfold newmanProtocol
  simp only [PrivateCoin.FiniteMessage.Protocol.rrun,
    Deterministic.FiniteMessage.Protocol.run,
    Deterministic.FiniteMessage.Protocol.comap_run]
  set ωs := (exists_good_randomness p f ε c hε hε1 hc hp).choose
  have hωs := (exists_good_randomness p f ε c hε hε1 hc hp).choose_spec
  -- The error set only depends on ω.1 (the index)
  have hset : {ω : newmanIndexSpace X Y ε c × Unit |
      p.run (ωs ω.1, x) (ωs ω.1, y) ≠ f x y} =
      {i | p.run (ωs i, x) (ωs i, y) ≠ f x y} ×ˢ Set.univ := by
    ext ⟨i, u⟩; simp
  rw [hset]
  -- Product measure of S ×ˢ univ = volume(S) * volume(univ) = volume(S)
  rw [show (volume : Measure (newmanIndexSpace X Y ε c × Unit)) =
    volume.prod volume from rfl]
  rw [Measure.prod_prod, measure_univ, mul_one]
  -- volume on newmanIndexSpace = uniformOn Set.univ
  change (ProbabilityTheory.uniformOn Set.univ _).toReal ≤ _
  rw [ProbabilityTheory.uniformOn_univ, ENNReal.toReal_div]
  classical
  rw [Measure.count_apply MeasurableSet.of_discrete,
    Set.encard_eq_coe_toFinset_card]
  simp only [ENat.toENNReal_coe, ENNReal.toReal_natCast, Fintype.card_fin]
  convert hωs x y using 1
  congr 1; norm_cast
  apply Finset.card_equiv (Equiv.refl _)
  intro i; simp; rfl

theorem FiniteMessage.Protocol.newmanProtocol_complexity
    {Ω X Y α : Type*} [Fintype Ω]
    [Fintype X] [Fintype Y]
    [MeasureSpace Ω] [DiscreteMeasurableSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    (p : FiniteMessage.Protocol Ω X Y α)
    (f : X → Y → α) (ε c : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hc : 1 < c)
    (hp : p.ApproxComputes f ε) :
    (p.newmanProtocol f ε c hε hε1 hc hp).complexity =
      Nat.clog 2 (FiniteMessage.Protocol.derandomizationSamples
        X Y ε c) + p.complexity := by
  simp only [newmanProtocol,
    Deterministic.FiniteMessage.Protocol.complexity,
    Deterministic.FiniteMessage.Protocol.toPrivateCoin_complexity,
    PublicCoin.FiniteMessage.Protocol.toDeterministic_complexity]
  -- sup of constant function = constant (since newmanIndexSpace is nonempty)
  rw [Finset.sup_const
    (α := ℕ) (Finset.univ_nonempty (α := newmanIndexSpace X Y ε c)),
    show Fintype.card (newmanIndexSpace X Y ε c) =
      FiniteMessage.Protocol.derandomizationSamples X Y ε c
      from Fintype.card_fin _]

/-- Newman's theorem: for any ε' > c·ε, private-coin communication
complexity at error ε' is at most public-coin complexity at error ε
plus O(log(|X|·|Y|)/ε²) bits. -/
theorem newman
    {X Y α : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → α) (ε ε' : ℝ) (c : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hc : 1 < c)
    (hε' : c * ε < ε') :
    PrivateCoin.communicationComplexity f ε' ≤
      PublicCoin.communicationComplexity f ε +
        Nat.clog 2
          (FiniteMessage.Protocol.derandomizationSamples
            X Y ε c) := by
  -- Match on the public-coin complexity
  match h : PublicCoin.communicationComplexity f ε with
  | ⊤ => simp
  | (n : ℕ) =>
    -- There exists a public-coin protocol with complexity ≤ n
    obtain ⟨m, p, hp, hc_le⟩ :=
      (PublicCoin.communicationComplexity_le_iff f ε n).mp (le_of_eq h)
    -- Lift to FiniteMessage
    let pfm := PublicCoin.FiniteMessage.Protocol.ofProtocol p
    have hpfm_approx : pfm.ApproxComputes f ε := by
      intro x y
      simp only [pfm, PublicCoin.FiniteMessage.Protocol.rrun,
        Deterministic.FiniteMessage.Protocol.ofProtocol_run]
      exact hp x y
    -- Apply newmanProtocol: get a private-coin FM protocol that (c*ε)-computes f
    let q := pfm.newmanProtocol f ε c hε hε1 hc hpfm_approx
    have hq_approx :=
      FiniteMessage.Protocol.newmanProtocol_ApproxComputes
        pfm f ε c hε hε1 hc hpfm_approx
    -- q (c*ε)-computes f with c*ε < ε', so we can use
    -- communicationComplexity_le_of_finiteMessage
    have hbound :=
      PrivateCoin.communicationComplexity_le_of_finiteMessage
        f ε' (c * ε) hε' q hq_approx
    -- Bound q.complexity
    have hpfm_comp : pfm.complexity = p.complexity :=
      Deterministic.FiniteMessage.Protocol.ofProtocol_complexity p
    have hq_comp : q.complexity =
        Nat.clog 2 (FiniteMessage.Protocol.derandomizationSamples X Y ε c) +
          pfm.complexity :=
      FiniteMessage.Protocol.newmanProtocol_complexity pfm f ε c hε hε1 hc hpfm_approx
    set t_log := Nat.clog 2
      (FiniteMessage.Protocol.derandomizationSamples X Y ε c)
    -- Goal is: CC ≤ ↑n + ↑t_log
    calc PrivateCoin.communicationComplexity f ε'
        ≤ (q.complexity : ENat) := hbound
      _ = ↑(t_log + pfm.complexity) := by exact_mod_cast hq_comp
      _ = ↑(t_log + p.complexity) := by rw [hpfm_comp]
      _ ≤ ↑(t_log + n) := by exact_mod_cast Nat.add_le_add_left hc_le _
      _ = ↑n + ↑t_log := by push_cast; ring

end PublicCoin

end CommunicationComplexity
