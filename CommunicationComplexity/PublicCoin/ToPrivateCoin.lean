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
  Fin (GeneralFiniteMessage.Protocol.derandomizationSamples X Y ε c)

noncomputable instance newmanIndexSpace.fintype
    (X Y : Type*) [Fintype X] [Fintype Y] (ε c : ℝ) :
    Fintype (newmanIndexSpace X Y ε c) := inferInstance

noncomputable instance newmanIndexSpace.nonempty
    (X Y : Type*) [Fintype X] [Fintype Y] (ε c : ℝ) :
    Nonempty (newmanIndexSpace X Y ε c) :=
  ⟨⟨0, by simp [GeneralFiniteMessage.Protocol.derandomizationSamples]⟩⟩

noncomputable instance newmanIndexSpace.measureSpace
    (X Y : Type*) [Fintype X] [Fintype Y] (ε c : ℝ) :
    MeasureSpace (newmanIndexSpace X Y ε c) :=
  ⟨ProbabilityTheory.uniformOn Set.univ⟩

noncomputable instance newmanIndexSpace.isProbabilityMeasure
    (X Y : Type*) [Fintype X] [Fintype Y] (ε c : ℝ) :
    IsProbabilityMeasure (volume : Measure (newmanIndexSpace X Y ε c)) := by
  change IsProbabilityMeasure (ProbabilityTheory.uniformOn Set.univ)
  infer_instance

/-- Convert a public-coin protocol to a private-coin finite-message
protocol using the Newman reduction. Alice samples a random index
i from `newmanIndexSpace` and sends it to Bob. Both then simulate
the public-coin protocol with the i-th seed from a fixed table. -/
noncomputable def GeneralFiniteMessage.Protocol.toPrivateCoin
    {Ω X Y α : Type*} [Fintype Ω] [DecidableEq α]
    [Fintype X] [Fintype Y]
    [MeasureSpace Ω] [DiscreteMeasurableSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    (p : GeneralFiniteMessage.Protocol Ω X Y α)
    (f : X → Y → α) (ε c : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hc : 1 < c)
    (hp : p.ApproxComputes f ε) :
    PrivateCoin.GeneralFiniteMessage.Protocol
      (newmanIndexSpace X Y ε c) Unit X Y α :=
  -- Choose good randomness values via Chernoff + union bound
  let ωs := (GeneralFiniteMessage.Protocol.exists_good_randomness
    p f ε c hε hε1 hc hp).choose
  -- Alice sends her random index i ∈ newmanIndexSpace to Bob,
  -- then both simulate with ωs(i)
  .alice (fun _ ω_x => ω_x) (fun i =>
    (p.toDeterministic (ωs i)).toPrivateCoinOver)

theorem GeneralFiniteMessage.Protocol.toPrivateCoin_ApproxComputes
    {Ω X Y α : Type*} [Fintype Ω] [DecidableEq α]
    [Fintype X] [Fintype Y]
    [MeasureSpace Ω] [DiscreteMeasurableSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    (p : GeneralFiniteMessage.Protocol Ω X Y α)
    (f : X → Y → α) (ε c : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hc : 1 < c)
    (hp : p.ApproxComputes f ε) :
    (p.toPrivateCoin f ε c hε hε1 hc hp).ApproxComputes f (c * ε) := by
  -- The spec from exists_good_randomness
  -- ApproxComputes means: for all x y, P[run ≠ f x y] ≤ c * ε
  -- on the product space newmanIndexSpace × Unit
  intro x y
  unfold toPrivateCoin PrivateCoin.GeneralFiniteMessage.Protocol.run
  simp only [Deterministic.FiniteMessage.Protocol.toPrivateCoinOver_run, toDeterministic_run]
  set ωs := (exists_good_randomness p f ε c hε hε1 hc hp).choose
  have hωs := (exists_good_randomness p f ε c hε hε1 hc hp).choose_spec
  -- The error set only depends on ω.1
  have hset : {ω : newmanIndexSpace X Y ε c × Unit |
      p.run x y (ωs ω.1) ≠ f x y} =
      {i | p.run x y (ωs i) ≠ f x y} ×ˢ Set.univ := by
    ext ⟨i, u⟩; simp
  simp only [hset]
  -- Product measure of S ×ˢ univ = volume(S) * volume(univ) = volume(S)
  rw [show (volume : Measure (newmanIndexSpace X Y ε c × Unit)) =
    volume.prod volume from rfl]
  rw [Measure.prod_prod, measure_univ, mul_one]
  -- volume on newmanIndexSpace = uniformOn Set.univ
  change (ProbabilityTheory.uniformOn Set.univ _).toReal ≤ _
  rw [ProbabilityTheory.uniformOn_univ, ENNReal.toReal_div]
  rw [Measure.count_apply MeasurableSet.of_discrete,
    Set.encard_eq_coe_toFinset_card]
  simp only [ENat.toENNReal_coe, ENNReal.toReal_natCast, Fintype.card_fin]
  convert hωs x y using 1
  congr 1; norm_cast
  apply Finset.card_equiv (Equiv.refl _)
  intro i; simp; rfl

/-- Newman's theorem: private-coin communication complexity at error
c·ε is at most public-coin complexity at error ε plus
O(log(|X|·|Y|)/ε²) bits. -/
theorem newman
    {X Y α : Type*} [Fintype X] [Fintype Y]
    (f : X → Y → α) (ε : ℝ) (c : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hc : 1 < c) :
    PrivateCoin.communicationComplexity f (c * ε) ≤
      PublicCoin.communicationComplexity f ε +
        Nat.clog 2
          (GeneralFiniteMessage.Protocol.derandomizationSamples
            X Y ε c) := by
  sorry

end PublicCoin

end CommunicationComplexity
