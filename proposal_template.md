# CS 294-268 Final Project Proposal

**Title:** Formalizing Communication Complexity: Foundations, Protocols, and Tight Bounds

**Group Members:** Mihir Singhal

---

## 1. Project Topic

We formalize the foundations of two-party communication complexity, covering deterministic, private-coin, and public-coin models. Starting from protocol definitions and the rectangle method, we aim to prove tight upper and lower bounds (both deterministic and randomized) for important functions including equality, inner product, disjointness, indexing, and gap-Hamming distance.

## 2. Background and Motivation

Communication complexity, introduced by Yao (1979), is a cornerstone of theoretical computer science with applications to circuit lower bounds, streaming algorithms, data structures, and property testing. The key functions we target (equality, inner product, disjointness, etc.) are among the most well-studied in the field, with tight bounds that illustrate fundamentally different proof techniques: combinatorial rectangle arguments, rank methods, corruption/information-theoretic methods, and distributional complexity. A formal library for these results would provide a verified foundation for one of TCS's most active areas.

## 3. Proof Strategy

We plan to follow the standard textbook development (primarily Kushilevitz–Nisan and Rao–Yehudayoff), proceeding through several layers:

- **Deterministic model:** Define protocols, the rectangle partition structure, and the log-rank lower bound. Prove tight bounds for equality ($D(\text{EQ}_n) = n + 1$) and the rank method.
- **Randomized models (private and public coin):** Define $\varepsilon$-error protocols, communication complexity as an infimum, and monotonicity in $\varepsilon$. Establish reductions between models (deterministic $\Rightarrow$ private-coin $\Rightarrow$ public-coin).
- **Randomized upper bounds:** For equality, the classic $O(\log n)$-bit public-coin protocol via fingerprinting. For other functions, appropriate protocol constructions.
- **Randomized lower bounds:** Distributional complexity and Yao's minimax principle. For disjointness, corruption-based or information-theoretic arguments. For inner product, reduction from or direct argument.
- **Composition:** Oblivious (product/pi) composition of protocols, used in amplification and reductions.

Key lemmas include: the rectangle partition theorem, log-rank lower bound, balanced simulation (Theorem 1.7 of Rao–Yehudayoff), single-coin approximation for reducing general probability spaces to coin flips, and protocol composition with additive complexity.

## 4. Lean Formalization Plan

We have already built substantial infrastructure, organized as follows:

**Existing definitions and theorems:**
- `Deterministic.Protocol`, `PrivateCoin.Protocol`, `PublicCoin.Protocol` — inductive protocol types for all three models
- `FiniteMessage.Protocol` and `GeneralFiniteMessage.Protocol` — generalized message-alphabet and arbitrary-probability-space variants, with verified reductions to binary protocols
- `communicationComplexity` — defined as an infimum over protocols in each model, with `_le_iff` and `le_` characterizations
- Rectangle theory: `IsRectangle`, `IsMonoPartition`, the rectangle partition theorem, and `communicationComplexity_lower_bound`
- `log_rank_lower_bound` — $D(f) \geq \lceil \log_2 \text{rank}(f) \rceil$
- `communicationComplexity_eq` for equality — $D(\text{EQ}_n) = n + 1$
- Balanced simulation (Theorem 1.7) and balanced subtree lemma (Lemma 1.8)
- `single_coin_approx` — approximation of arbitrary finite probability spaces by coin flips
- `communicationComplexity_mono` — monotonicity in error parameter
- Protocol composition (`prod`, `pi`, `comapRandomness`, `map`, `bind`)

**Planned additions:**
- *Equality:* $R^{\text{pub}}(\text{EQ}_n) = \Theta(\log n)$ — fingerprinting upper bound and distributional lower bound
- *Inner product:* $D(\text{IP}_n) = n + 1$ via rank argument; $R(\text{IP}_n) = \Omega(n)$
- *Disjointness:* $R^{\text{pub}}(\text{DISJ}_n) = \Omega(n)$ via corruption or information complexity
- *Indexing:* $D(\text{IND}_n) = \Omega(\log n)$ (and matching upper bound)
- *Gap-Hamming:* $R^{\text{pub}}(\text{GHD}_n) = \Omega(n)$
- *Yao's minimax principle* relating distributional and randomized complexity
- *Newman's theorem* reducing public-coin to private-coin with logarithmic overhead

We make heavy use of Mathlib for measure theory (`MeasureTheory`, `IsProbabilityMeasure`), finite types (`Fintype`, `Finset`), linear algebra (`Matrix.rank`), and big operators.

## 5. Potential Challenges

- **Distributional complexity and Yao's minimax:** Formalizing the minimax theorem for two-player games (von Neumann's theorem) or a communication-specific version may require nontrivial convex analysis or linear programming duality, which has limited Mathlib support.
- **Information-theoretic arguments:** Lower bounds for disjointness and gap-Hamming use entropy, mutual information, and information-theoretic inequalities (e.g., chain rule, Fano's inequality). These may need new Mathlib infrastructure or careful formalization.
- **Measure-theoretic subtleties:** Working with probability measures over finite types in Lean requires careful handling of `ENNReal`/`NNReal` coercions and `volume` on product spaces, as we have already encountered extensively.
- **Dependent types in composition:** The k-fold protocol composition (`pi`) requires structural recursion over dependent types `(i : Fin k) → Ωf i`, which interacts poorly with Lean's typeclass resolution and necessitates arrow-style definitions.

## 6. References

- Kushilevitz, E. and Nisan, N. *Communication Complexity*. Cambridge University Press, 1997.
- Rao, A. and Yehudayoff, A. *Communication Complexity and Applications*. Cambridge University Press, 2020.
- Yao, A. C.-C. Some complexity questions related to distributive computing. *STOC*, 1979.
- Newman, I. Private vs. common random bits in communication complexity. *Information Processing Letters*, 1991.
- Razborov, A. On the distributional complexity of disjointness. *Theoretical Computer Science*, 1992.
