import CommunicationComplexity.Basic
import CommunicationComplexity.Deterministic.Rectangle
import CommunicationComplexity.Deterministic.OneWay
import CommunicationComplexity.Deterministic.UpperBounds
import CommunicationComplexity.CoinTape
import CommunicationComplexity.Hamming
import CommunicationComplexity.Helper
import CommunicationComplexity.PublicCoin.OneWayMinimax
import Mathlib.Probability.UniformOn

/-!
# Indexing

This file contains one-way and public-coin bounds for the indexing function.

For the distributional lower-bound strategy (uniform input distribution,
answer vectors, and Hamming-ball counting), we follow the proof presentation in:

* Tim Roughgarden, *Communication Complexity* lecture notes, Section 3
  (indexing lower bound via distributional complexity / Yao's framework).
-/


namespace CommunicationComplexity

namespace Functions.Indexing

open Deterministic
open MeasureTheory ProbabilityTheory

variable (n : ℕ+)

/-- The indexing function: Bob outputs Alice's `i`-th bit. -/
def indexing (x : Fin n → Bool) (i : Fin n) : Bool :=
  x i

/-- The trivial one-way protocol for indexing: Alice sends her full string. -/
def trivialProtocol : OneWay.Protocol (Fin n → Bool) (Fin n) Bool where
  Message := Fin n → Bool
  send := id
  decode := fun x i => x i

/-- One-way upper bound for indexing: Alice can send all `n` bits. -/
theorem oneWayCommunicationComplexity_le :
    OneWay.communicationComplexity (indexing n) ≤ (n : ℕ) := by
  rw [OneWay.communicationComplexity_le_iff]
  refine ⟨trivialProtocol n, (by ext x i; rfl), ?_⟩
  · simp [trivialProtocol, OneWay.Protocol.cost,
      Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Nat.one_lt_ofNat, Nat.clog_pow]

/-- Deterministic upper bound for indexing induced by the one-way protocol. -/
theorem communicationComplexity_le :
    Deterministic.communicationComplexity (indexing n) ≤ (n : ℕ) + 1 := by
  exact OneWay.deterministic_communicationComplexity_le_of_oneWay_le_bool
    (f := indexing n) (n := n) (oneWayCommunicationComplexity_le n)

/-- One-way lower bound for indexing: any correct deterministic one-way protocol
must send at least `n` bits. -/
theorem le_oneWayCommunicationComplexity : n ≤ OneWay.communicationComplexity (indexing n) := by
  rw [OneWay.le_communicationComplexity_iff]
  intro p hp_comp
  have hinj : Function.Injective p.send := by
    intro x y heq
    ext i
    have hx := congrFun (congrFun hp_comp x) i
    have hy := congrFun (congrFun hp_comp y) i
    have hm : p.decode (p.send x) i = p.decode (p.send y) i := by
      simpa using congrArg (fun m => p.decode m i) heq
    simpa [OneWay.Protocol.Computes, OneWay.Protocol.run, indexing] using
      hx.symm.trans (hm.trans hy)
  have hcard : Fintype.card (Fin n → Bool) ≤ Fintype.card p.Message := by
    exact Fintype.card_le_of_injective p.send hinj
  have hpow_dom : 2 ^ (n : ℕ) ≤ Fintype.card p.Message := by
    simpa [Fintype.card_pi, Fintype.card_bool, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin] using hcard
  have hcost : Fintype.card p.Message ≤ 2 ^ p.cost := by
    apply Nat.le_pow_clog; linarith
  by_contra!
  have h_bad : 2 ^ p.cost < 2 ^ (n : ℕ) := by
    refine Nat.pow_lt_pow_of_lt (by linarith) this
  omega

theorem oneWayCommunicationComplexity_eq :
    OneWay.communicationComplexity (indexing n) = (n : ℕ) := by
  exact le_antisymm (oneWayCommunicationComplexity_le n) (le_oneWayCommunicationComplexity n)

/-- Coercion helper showing `(n : ℕ)` is nonzero for `n : ℕ+`. -/
instance indexNeZero : NeZero (n : ℕ) := ⟨Nat.pos_iff_ne_zero.mp n.pos⟩

/-- Uniform measure-space structure on `Fin n`. -/
noncomputable instance indexMeasureSpace :
    MeasureSpace (Fin n) :=
  ⟨ProbabilityTheory.uniformOn Set.univ⟩

/-- Uniform measure on `Fin n` is a probability measure. -/
noncomputable instance indexIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure (Fin n)) := by
  change IsProbabilityMeasure (ProbabilityTheory.uniformOn Set.univ)
  infer_instance

/-- Finite probability-space packaging for uniform `Fin n`. -/
noncomputable instance indexFiniteProbabilitySpace :
    FiniteProbabilitySpace (Fin n) :=
  FiniteProbabilitySpace.of (Fin n)

/-- Finite probability-space packaging for uniform `BoolInput n`. -/
noncomputable instance boolInputFiniteProbabilitySpace :
    FiniteProbabilitySpace (BoolInput n) := by
  change FiniteProbabilitySpace (CoinTape n)
  infer_instance

/-- Uniform distribution on indexing inputs `(x, i)`, where `x` and `i`
are chosen independently and uniformly. -/
noncomputable def indexingInputDist :
    FiniteProbabilitySpace (BoolInput n × Fin n) := by
  letI : MeasureSpace (BoolInput n × Fin n) :=
    ⟨ProbabilityTheory.uniformOn Set.univ⟩
  letI : IsProbabilityMeasure (volume : Measure (BoolInput n × Fin n)) := by
    change IsProbabilityMeasure (ProbabilityTheory.uniformOn Set.univ)
    infer_instance
  exact FiniteProbabilitySpace.of (BoolInput n × Fin n)

open Classical in
/-- Bob's full answer vector for a fixed received one-way message. -/
private def answerVector
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool)
    (m : p.Message) : BoolInput n :=
  fun i => p.decode m i

open Classical in
/-- The finite set of answer vectors realizable by protocol messages. -/
private def answerSet
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool) : Finset (BoolInput n) :=
  Finset.image (answerVector (n := n) p) Finset.univ

open Classical in
/-- Inputs `x` that are not within Hamming radius `n/4` of any realizable answer vector. -/
private def badInput
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool)
    (x : BoolInput n) : Prop :=
  ¬ ∃ a ∈ answerSet (n := n) p, (hammingDist x a : ℝ) < (n : ℝ) / 4

open Classical in
/-- Decidability of the `badInput` predicate (finite ambient types). -/
private noncomputable instance badInputDecidablePred
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool) :
    DecidablePred (badInput (n := n) p) := by
  infer_instance

open Classical in
/-- Indices where protocol `p` errs on fixed input string `x`. -/
private def mismatchSubtype
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool)
    (x : BoolInput n) : Type :=
  {i : Fin n // p.run x i ≠ indexing n x i}

open Classical in
/-- Finiteness of mismatch coordinates for fixed `x`. -/
private noncomputable instance mismatchSubtypeFintype
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool)
    (x : BoolInput n) :
    Fintype (mismatchSubtype (n := n) p x) := by
  unfold mismatchSubtype
  infer_instance

open Classical in
/-- Input pairs `(x, i)` where protocol `p` is incorrect. -/
private def badPairSubtype
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool) : Type :=
  {xi : BoolInput n × Fin n // p.run xi.1 xi.2 ≠ indexing n xi.1 xi.2}

open Classical in
/-- Finiteness of incorrect input pairs. -/
private noncomputable instance badPairSubtypeFintype
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool) :
    Fintype (badPairSubtype (n := n) p) := by
  unfold badPairSubtype
  infer_instance

open Classical in
/-- Equivalence between incorrect pairs and a sigma of per-`x` mismatch indices. -/
private def badPairEquivSigma
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool) :
    badPairSubtype (n := n) p ≃ Σ x : BoolInput n, mismatchSubtype (n := n) p x where
  toFun z := ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
  invFun z := ⟨⟨z.1, z.2.1⟩, z.2.2⟩
  left_inv z := by
    rcases z with ⟨⟨x, i⟩, hz⟩
    rfl
  right_inv z := by
    rcases z with ⟨x, ⟨i, hi⟩⟩
    rfl

/-- The mismatch count for fixed `x` is exactly a Hamming distance to the
answer vector induced by `p.send x`. -/
private lemma mismatchSubtype_card_eq_hammingDist
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool)
    (x : BoolInput n) :
    Fintype.card (mismatchSubtype (n := n) p x) =
      hammingDist x (answerVector (n := n) p (p.send x)) := by
  classical
  unfold hammingDist
  simpa [mismatchSubtype, Deterministic.OneWay.Protocol.run, indexing, answerVector, ne_comm] using
    (Fintype.card_subtype (p := fun i : Fin n => p.decode (p.send x) i ≠ x i))

/-- Total incorrect-pair count equals the sum of per-`x` mismatch counts. -/
private lemma badPairSubtype_card_eq_sum
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool) :
    Fintype.card (badPairSubtype (n := n) p) =
      ∑ x : BoolInput n, Fintype.card (mismatchSubtype (n := n) p x) := by
  calc
    Fintype.card (badPairSubtype (n := n) p) =
        Fintype.card (Σ x : BoolInput n, mismatchSubtype (n := n) p x) := by
          exact Fintype.card_congr (badPairEquivSigma (n := n) p)
    _ = ∑ x : BoolInput n, Fintype.card (mismatchSubtype (n := n) p x) := Fintype.card_sigma

/-- Number of distinct answer vectors is at most `2 ^ p.cost`. -/
private lemma answerSet_card_le_pow_cost
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool) :
    (answerSet (n := n) p).card ≤ 2 ^ p.cost := by
  calc
    (answerSet (n := n) p).card
        ≤ Fintype.card p.Message := by
          simpa [answerSet] using
            (Finset.card_image_le (f := answerVector (n := n) p)
              (s := (Finset.univ : Finset p.Message)))
    _ ≤ 2 ^ p.cost := by
      exact Nat.le_pow_clog (by decide) _

/-- A bad input has Hamming distance at least `n/4` from its own induced answer vector. -/
private lemma badInput_implies_hammingDist_ge
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool)
    {x : BoolInput n}
    (hx : badInput (n := n) p x) :
    (n : ℝ) / 4 ≤ hammingDist x (answerVector (n := n) p (p.send x)) := by
  have hmem : answerVector (n := n) p (p.send x) ∈ answerSet (n := n) p := by
    exact Finset.mem_image.mpr ⟨p.send x, Finset.mem_univ _, rfl⟩
  have hnot :
      ¬ (hammingDist x (answerVector (n := n) p (p.send x)) : ℝ) < (n : ℝ) / 4 := by
    intro hlt
    exact hx ⟨answerVector (n := n) p (p.send x), hmem, hlt⟩
  exact le_of_not_gt hnot

/-- Core counting step in the indexing distributional argument: if at least half
of Alice inputs are bad (in the answer-vector sense), then the deterministic one-way
protocol has distributional error at least `1/8` under the uniform input distribution. -/
theorem distributionalError_ge_one_eighth_of_bad_half
    (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool)
    (hbad :
      2 ^ ((n : ℕ) - 1) ≤
        (Finset.univ.filter (fun x : BoolInput n => badInput (n := n) p x)).card) :
    p.distributionalError (μ := indexingInputDist n) (indexing n) ≥ (1 / 8 : ℝ) := by
  classical
  let bad : Finset (BoolInput n) :=
    Finset.univ.filter (fun x : BoolInput n => badInput (n := n) p x)
  let g : BoolInput n → ℝ := fun x => Fintype.card (mismatchSubtype (n := n) p x)
  have hsplit :
      (∑ x : BoolInput n, g x) =
        (Finset.sum bad g) +
          (Finset.sum (Finset.univ.filter (fun x : BoolInput n => x ∉ bad)) g) := by
    simpa [bad] using
      (Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
        (p := fun x : BoolInput n => x ∈ bad) (f := g)).symm
  have hsum_ge_bad : (∑ x : BoolInput n, g x) ≥ Finset.sum bad g := by
    have hnonneg :
        0 ≤ Finset.sum (Finset.univ.filter (fun x : BoolInput n => x ∉ bad)) g := by
      positivity
    linarith
  have hbad_term : ∀ x ∈ bad, (n : ℝ) / 4 ≤ g x := by
    intro x hx
    have hx_bad : badInput (n := n) p x := (Finset.mem_filter.mp hx).2
    have hdist := badInput_implies_hammingDist_ge (n := n) p hx_bad
    simpa [g, mismatchSubtype_card_eq_hammingDist] using hdist
  have hsum_bad_ge :
      Finset.sum bad g ≥ Finset.sum bad (fun _ => (n : ℝ) / 4) := by
    refine Finset.sum_le_sum ?_
    intro x hx
    exact hbad_term x hx
  have hsum_bad_const :
      (Finset.sum bad (fun _ => (n : ℝ) / 4)) = (bad.card : ℝ) * ((n : ℝ) / 4) := by
    simp
  have hsum_ge :
      (∑ x : BoolInput n, g x) ≥ (bad.card : ℝ) * ((n : ℝ) / 4) := by
    linarith [hsum_ge_bad, hsum_bad_ge, hsum_bad_const]
  have hbad_real : ((2 ^ ((n : ℕ) - 1) : ℕ) : ℝ) ≤ (bad.card : ℝ) := by
    exact_mod_cast hbad
  have hcard_badpair :
      (Fintype.card (badPairSubtype (n := n) p) : ℝ) ≥
        ((2 ^ ((n : ℕ) - 1) : ℕ) : ℝ) * ((n : ℝ) / 4) := by
    have hsum_card :
        (Fintype.card (badPairSubtype (n := n) p) : ℝ) = ∑ x : BoolInput n, g x := by
      simp [g, badPairSubtype_card_eq_sum]
    have hmult :
        (bad.card : ℝ) * ((n : ℝ) / 4) ≥
          ((2 ^ ((n : ℕ) - 1) : ℕ) : ℝ) * ((n : ℝ) / 4) := by
      gcongr
    linarith [hsum_ge, hsum_card, hmult]
  rw [Deterministic.OneWay.Protocol.distributionalError]
  change
    (((ProbabilityTheory.uniformOn Set.univ : Measure (BoolInput n × Fin n))
      {xi : BoolInput n × Fin n | p.run xi.1 xi.2 ≠ indexing n xi.1 xi.2}).toReal) ≥
      (1 / 8 : ℝ)
  rw [uniformOn_univ_measureReal_eq_card_filter]
  let errSet : Set (BoolInput n × Fin n) :=
    {xi : BoolInput n × Fin n | p.run xi.1 xi.2 ≠ indexing n xi.1 xi.2}
  let errFinset : Finset (BoolInput n × Fin n) := {ω : BoolInput n × Fin n | ω ∈ errSet}
  have hcard_eq :
      errFinset.card =
        Fintype.card (badPairSubtype (n := n) p) := by
    simp [errFinset, errSet, badPairSubtype, Fintype.card_subtype]
  have hcard_eq_real :
      (errFinset.card : ℝ) =
        Fintype.card (badPairSubtype (n := n) p) := by
    exact_mod_cast hcard_eq
  have hcard_eq_div :
      ((errFinset.card : ℝ) /
          (Fintype.card (BoolInput n × Fin n) : ℝ)) =
        ((Fintype.card (badPairSubtype (n := n) p) : ℝ) /
          (Fintype.card (BoolInput n × Fin n) : ℝ)) := by
    exact congrArg (fun t : ℝ => t / (Fintype.card (BoolInput n × Fin n) : ℝ)) hcard_eq_real
  have hden :
      (Fintype.card (BoolInput n × Fin n) : ℝ) = (2 ^ (n : ℕ) : ℝ) * (n : ℝ) := by
    simp [BoolInput, Fintype.card_prod, Fintype.card_pi, Fintype.card_bool,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast n.pos
  have hpow_pos : (0 : ℝ) < (2 ^ (n : ℕ) : ℝ) := by positivity
  have hmain :
      (Fintype.card (badPairSubtype (n := n) p) : ℝ) /
          ((2 ^ (n : ℕ) : ℝ) * (n : ℝ))
      ≥
        (((2 ^ ((n : ℕ) - 1) : ℕ) : ℝ) * ((n : ℝ) / 4)) /
          ((2 ^ (n : ℕ) : ℝ) * (n : ℝ)) := by
    exact div_le_div_of_nonneg_right hcard_badpair (by positivity)
  have hfinal :
      (((2 ^ ((n : ℕ) - 1) : ℕ) : ℝ) * ((n : ℝ) / 4)) /
          ((2 ^ (n : ℕ) : ℝ) * (n : ℝ)) = (1 / 8 : ℝ) := by
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp n.pos) with ⟨m, hm⟩
    rw [hm, Nat.succ_sub_one, pow_succ]
    have hcast : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m := by
      exact_mod_cast (show (2 ^ m : ℕ) = 2 ^ m by rfl)
    rw [hcast]
    have hm_ne : ((m.succ : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hm_ne, pow_ne_zero]
    ring_nf
  have htarget_rhs :
      ((Fintype.card (badPairSubtype (n := n) p) : ℝ) /
          (Fintype.card (BoolInput n × Fin n) : ℝ)) ≥ (1 / 8 : ℝ) := by
    rw [hden]
    linarith [hmain, hfinal]
  have htarget_lhs :
      ((errFinset.card : ℝ) /
          (Fintype.card (BoolInput n × Fin n) : ℝ)) ≥ (1 / 8 : ℝ) := by
    calc
      ((errFinset.card : ℝ) / (Fintype.card (BoolInput n × Fin n) : ℝ))
          = ((Fintype.card (badPairSubtype (n := n) p) : ℝ) /
              (Fintype.card (BoolInput n × Fin n) : ℝ)) := hcard_eq_div
      _ ≥ (1 / 8 : ℝ) := htarget_rhs
  convert htarget_lhs using 1
  refine congrArg (fun t : Finset (BoolInput n × Fin n) =>
      (t.card : ℝ) / (Fintype.card (BoolInput n × Fin n) : ℝ)) ?_
  ext x
  simp [errFinset, errSet]

/-- Distributional one-way lower-bound hypothesis for indexing at error `ε`
and cost budget `c`. -/
def deterministicOneWayDistributionalLowerBound (ε : ℝ) (c : ℕ) : Prop :=
  ∀ (p : Deterministic.OneWay.Protocol (BoolInput n) (Fin n) Bool),
    p.cost ≤ c →
    p.distributionalError (μ := indexingInputDist n) (indexing n) > ε

/-- Setup lemma: any distributional lower bound against the uniform indexing
distribution yields a one-way public-coin lower bound via minimax. -/
theorem publicCoinOneWay_lower_bound_of_distributional
    {ε : ℝ} {c : ℕ}
    (h : deterministicOneWayDistributionalLowerBound n ε c) :
    c < PublicCoin.OneWay.communicationComplexity (indexing n) ε := by
  exact PublicCoin.OneWay.minimax_lower_bound
    (f := indexing n) (ε := ε) (n := c) (μ := indexingInputDist n) h

/-- Convenience specialization of `publicCoinOneWay_lower_bound_of_distributional`
to the common constants used in the indexing proof skeleton. -/
theorem publicCoinOneWay_linear_lower_bound
    (h : deterministicOneWayDistributionalLowerBound n (1 / 8 : ℝ) ((n : ℕ) / 10)) :
    ((((n : ℕ) / 10 : ℕ) : ENat)) <
      PublicCoin.OneWay.communicationComplexity (indexing n) (1 / 8 : ℝ) := by
  exact publicCoinOneWay_lower_bound_of_distributional (n := n) h

end Functions.Indexing

end CommunicationComplexity
