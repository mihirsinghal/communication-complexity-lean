# CS 294-268 Final Project Proposal

**Title:** Formalizing Communication Complexity: The Log-Rank Theorem and Protocols for Equality

**Group Members:** Lucy Horowitz, Timothe Kasriel, Mihir Singhal, 

---

## 1. Project Topic

We formalize foundational results in two-party communication complexity. On the lower bound side, we prove the **log-rank theorem**: for any Boolean function $f : X \times Y \to \{0,1\}$, the deterministic communication complexity satisfies $D(f) \geq \log_2 \operatorname{rank}(M_f)$, where $M_f$ is the communication matrix of $f$ over $\mathbb{R}$. On the upper bound side, we define the equality function $\mathrm{EQ}_n$, give an explicit deterministic protocol, and formally verify its correctness and communication cost.

## 2. Background and Motivation

Communication complexity, introduced by Yao (1979), studies the minimum number of bits two parties must exchange to jointly compute a function of their inputs. It is a foundational model in theoretical computer science with deep connections to circuit complexity, data structures, proof complexity, and algorithms. The log-rank theorem is one of the most important structural lower bound techniques, relating algebraic rank to combinatorial communication cost. The log-rank *conjecture* — that $D(f) = \operatorname{poly}(\log \operatorname{rank}(M_f))$ — remains one of the major open problems in the field, making even the known lower bound direction a natural target for formalization.

## 3. Proof Strategy

**Log-rank lower bound.** We follow the standard argument (see Kushilevitz–Nisan, Chapter 1–2):
1. Associate to any deterministic protocol $P$ a partition of $X \times Y$ into at most $2^{D(P)}$ combinatorial rectangles, one per leaf.
2. Show each rectangle is monochromatic (all-0 or all-1 under $f$), hence the corresponding submatrix of $M_f$ has rank at most 1.
3. Since $M_f$ is a sum of at most $2^{D(P)}$ rank-1 matrices, $\operatorname{rank}(M_f) \leq 2^{D(P)}$, giving $D(f) \geq \log_2 \operatorname{rank}(M_f)$.

**Equality protocol.** Alice holds $x \in \{0,1\}^n$, Bob holds $y \in \{0,1\}^n$. The naive deterministic protocol has Alice send all $n$ bits; Bob replies with a single bit. We construct this as a `DetProtocol` term and prove `computes` holds. As a stretch goal, we state a randomized fingerprinting protocol for equality with $O(\log n)$ communication and error $1/3$.

**Parallel repetition (stretch goal).** We aim to state the direct-sum / direct-product framework and possibly prove a simple parallel repetition bound for deterministic protocols.

## 4. Lean Formalization Plan

The project builds on the existing `DetProtocol` and `RandProtocol` infrastructure in `CommunicationComplexity/Basic.lean`.

**Definitions to add:**
- `commMatrix (f : X → Y → Bool) : Matrix X Y ℝ` — the communication matrix of $f$
- `isRectangle (R : Set (X × Y)) : Prop` — $R$ is a combinatorial rectangle ($R = A \times B$)
- `monochromaticRectangle (f : X → Y → Bool) (R : Set (X × Y)) : Prop`
- `leafRectangles (p : DetProtocol X Y α) : List (Set (X × Y))` — rectangles induced by protocol leaves
- `D (f : X → Y → Bool) : ℕ` — deterministic communication complexity (minimum over all computing protocols)

**Theorems to prove:**
- `protocol_partitions_into_rectangles`: leaves of any protocol induce a partition of $X \times Y$ into monochromatic rectangles
- `num_leaves_le_two_pow_complexity`: a protocol of complexity $c$ has at most $2^c$ leaves
- `rank_le_num_rectangles`: $\operatorname{rank}(M_f) \leq$ number of monochromatic 1-rectangles in any partition
- `log_rank_lower_bound`: $D(f) \geq \log_2 \operatorname{rank}(M_f)$  *(main theorem)*
- `eq_protocol`: an explicit `DetProtocol` term computing $\mathrm{EQ}_n$
- `eq_protocol_correct`: `eq_protocol.computes (fun x y => x == y)`
- `eq_protocol_complexity`: `eq_protocol.complexity = n + 1`

**Mathlib dependencies anticipated:**
- `Mathlib.LinearAlgebra.Matrix.Rank` for matrix rank
- `Mathlib.Data.Fintype.Basic`, `Mathlib.Data.Matrix.Basic`
- `Mathlib.Analysis.SpecialFunctions.Log.Basic` for $\log_2$

## 5. Potential Challenges

- **Defining communication complexity $D(f)$** as an infimum over all protocols requires either working with a `Finset` of bounded-complexity protocols or arguing finiteness of the search space, which may require additional infrastructure.
- **Connecting protocol leaves to matrix rank** requires bridging combinatorial/inductive reasoning about protocol trees with Mathlib's linear algebra API for matrix rank, which may require nontrivial glue lemmas.
- **Matrix rank in Lean** is defined over a field; using $\mathbb{R}$ is natural but we must be careful with `Fintype` instances when $X$ and $Y$ are finite.
- **Equality protocol construction**: building the explicit `DetProtocol` term for $\mathrm{EQ}_n$ by induction on $n$ is straightforward but may require careful handling of index types.
- **Parallel repetition** (stretch goal) would require defining direct products of protocols and establishing a measure of "hardness," which may be out of scope depending on progress.

## 6. References

- Eyal Kushilevitz and Noam Nisan. *Communication Complexity*. Cambridge University Press, 1997. (Primary reference for all proofs.)
- Andrew Chi-Chih Yao. "Some complexity questions related to distributive computing." *STOC 1979*.
- Ran Raz. "A parallel repetition theorem." *SIAM Journal on Computing*, 1998. (For stretch goal.)
- Mathlib4 documentation: `Mathlib.LinearAlgebra.Matrix.Rank`.
