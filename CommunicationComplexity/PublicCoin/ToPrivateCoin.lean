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
    {Ω X Y α : Type*} [Fintype Ω]
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
    {Ω X Y α : Type*} [Fintype Ω]
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
  classical
  rw [Measure.count_apply MeasurableSet.of_discrete,
    Set.encard_eq_coe_toFinset_card]
  simp only [ENat.toENNReal_coe, ENNReal.toReal_natCast, Fintype.card_fin]
  convert hωs x y using 1
  congr 1; norm_cast
  apply Finset.card_equiv (Equiv.refl _)
  intro i; simp; rfl

theorem GeneralFiniteMessage.Protocol.toPrivateCoin_complexity
    {Ω X Y α : Type*} [Fintype Ω]
    [Fintype X] [Fintype Y]
    [MeasureSpace Ω] [DiscreteMeasurableSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    (p : GeneralFiniteMessage.Protocol Ω X Y α)
    (f : X → Y → α) (ε c : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hc : 1 < c)
    (hp : p.ApproxComputes f ε) :
    (p.toPrivateCoin f ε c hε hε1 hc hp).complexity =
      Nat.clog 2 (GeneralFiniteMessage.Protocol.derandomizationSamples
        X Y ε c) + p.complexity := by
  simp only [toPrivateCoin,
    PrivateCoin.GeneralFiniteMessage.Protocol.complexity,
    Deterministic.FiniteMessage.Protocol.toPrivateCoinOver_complexity,
    toDeterministic_complexity]
  -- sup of constant function = constant (since newmanIndexSpace is nonempty)
  rw [Finset.sup_const
    (α := ℕ) (Finset.univ_nonempty (α := newmanIndexSpace X Y ε c)),
    show Fintype.card (newmanIndexSpace X Y ε c) =
      derandomizationSamples X Y ε c from Fintype.card_fin _]

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
          (GeneralFiniteMessage.Protocol.derandomizationSamples
            X Y ε c) := by
  -- Match on the public-coin complexity
  match h : PublicCoin.communicationComplexity f ε with
  | ⊤ => simp
  | (n : ℕ) =>
    -- There exists a public-coin protocol with complexity ≤ n
    obtain ⟨m, p, hp, hc_le⟩ :=
      (PublicCoin.communicationComplexity_le_iff f ε n).mp (le_of_eq h)
    -- Lift to GeneralFiniteMessage
    let pGFM := GeneralFiniteMessage.Protocol.ofProtocol p
    have hpGFM_approx : pGFM.ApproxComputes f ε := by
      intro x y; simp only [pGFM, ne_eq,
        GeneralFiniteMessage.Protocol.ofProtocol_run]; exact hp x y
    -- Apply toPrivateCoin: get a private-coin GFM protocol that (c*ε)-computes f
    let q := pGFM.toPrivateCoin f ε c hε hε1 hc hpGFM_approx
    have hq_approx :=
      GeneralFiniteMessage.Protocol.toPrivateCoin_ApproxComputes
        pGFM f ε c hε hε1 hc hpGFM_approx
    -- q (c*ε)-computes f with c*ε < ε', so we can use
    -- communicationComplexity_le_of_generalFiniteMessage
    have hbound :=
      PrivateCoin.communicationComplexity_le_of_generalFiniteMessage
        f ε' (c * ε) hε' q hq_approx
    -- q.complexity = ⌈log t⌉ + pGFM.complexity
    -- pGFM.complexity = p.complexity ≤ n
    -- q.complexity ≤ ⌈log t⌉ + n
    -- since q = alice(send index) then (det protocol of complexity ≤ p.complexity ≤ n)
    -- and pGFM.complexity = p.complexity
    have hpGFM_comp : pGFM.complexity = p.complexity :=
      GeneralFiniteMessage.Protocol.ofProtocol_complexity p
    -- Bound q.complexity
    have hq_comp : q.complexity =
        Nat.clog 2 (GeneralFiniteMessage.Protocol.derandomizationSamples X Y ε c) +
          pGFM.complexity :=
      GeneralFiniteMessage.Protocol.toPrivateCoin_complexity pGFM f ε c hε hε1 hc hpGFM_approx
    set t_log := Nat.clog 2
      (GeneralFiniteMessage.Protocol.derandomizationSamples X Y ε c)
    -- Goal is: CC ≤ ↑n + ↑t_log (after match rewrote PublicCoin.CC to n)
    calc PrivateCoin.communicationComplexity f ε'
        ≤ (q.complexity : ENat) := hbound
      _ = ↑(t_log + pGFM.complexity) := by exact_mod_cast hq_comp
      _ = ↑(t_log + p.complexity) := by rw [hpGFM_comp]
      _ ≤ ↑(t_log + n) := by exact_mod_cast Nat.add_le_add_left hc_le _
      _ = ↑n + ↑t_log := by push_cast; ring

end PublicCoin

end CommunicationComplexity
