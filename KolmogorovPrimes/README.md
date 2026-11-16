# Formalization of Lower Bounds on Prime Distribution via Kolmogorov Complexity

**Assignee: Gabriel Resende Machado — INF2290 (2026.2).**

---

This repository contains a complete, mechanically verified formalization in **Lean 4** of information-theoretic lower bounds on the distribution of prime numbers $\pi(n)$ using the **Incompressibility Method** [(based on Schöning & Pruim, *Gems of Theoretical Computer Science*, Topic 9).](docs/references/Gems_of_Theoretical_Computer_Science.pdf)

Developed as the final project for ****INF2290** (Formalization in Lean)** at **PUC-Rio**, this library bridges the gap between **Complexitylib** (`Cslib.Kolmogorov`, which provides abstract Kolmogorov complexity over bit strings) and **Mathlib** (`Mathlib.NumberTheory.PrimeCounting`, which provides prime enumeration and arithmetic foundations).

---

## Key Contributions

While `Complexitylib` formalizes plain Kolmogorov complexity (`DescriptionMethod.ecomplexity`) and the existence of incompressible binary strings via the Pigeonhole Principle, applying these results to Number Theory requires an intermediate information-theoretic layer not previously available in the ecosystem:

1. **Arithmetic-Information Bridge (`Basic.lean`):** Connects canonical binary representations of natural numbers (`Nat.bits` / `bin`) to `List Bool` (`BinWord`), proving injectivity via an explicit left-inverse decoder (`decodeBin`) and establishing the exact logarithmic bit-length identity $\vert{}\text{bin}(n)\vert{} = \lfloor\log_2 n\rfloor + 1$ for $n > 0$.
2. **Constructive Hierarchy of Self-Terminating Codes (`SelfTerminatingCode.lean`):** Formalizes three prefix-free encoding schemes to concatenate pairs of integers without boundary ambiguity:
   * **Elementary Bit-Doubling Code (`bar`):** $\vert{}\overline{w}\vert{} = 2\vert{}w\vert{} + 1$.
   * **Compact Length-Prefixed Code (`code`):** $\text{code}(w) = \overline{\text{bin}(\vert{}w\vert{})}w$, with $\vert{}\text{code}(w)\vert{} \le \vert{}w\vert{} + 2\lfloor\log_2 \vert{}w\vert{}\rfloor + 3$.
   * **Iterated Length-Prefixed Code (`code2`):** $\text{code}_2(w) = \text{code}(\text{bin}(\vert{}w\vert{}))w$, reducing header overhead to $\lfloor\log_2 \vert{}w\vert{}\rfloor + 2\lfloor\log_2(\lfloor\log_2 \vert{}w\vert{}\rfloor + 1)\rfloor + 4$.
   * Includes full mechanical proofs of unique decodability (`bar_append_inj`, `code_append_inj`, `code2_append_inj`).
3. **Information-to-Density Transfer for Primes (`InfinitudePrimes.lean`, `PrimeReconstruction.lean`, `WeakPNT.lean`):** Proves that improvements in prefix-free code compactness translate directly into stronger lower bounds on the prime-counting function $\pi(n)$, progressing from qualitative infinitude to the Weak Prime Number Theorem ($p_m < 2^{c+5}(m+1)(\lfloor\log_2 m\rfloor + 2)^2$).

---

## Repository Structure & Verified Theorems

All five modules compile cleanly with **zero `sorry` axioms**:

```text
KolmogorovPrimes/
├── KolmogorovPrimes/
│   ├── Basic.lean                 # Canonical binary encoding, left-inverse decoder, Complexitylib bridge
│   ├── SelfTerminatingCode.lean   # Prefix-free codes (bar, code, code2), length bounds, and injectivity
│   ├── InfinitudePrimes.lean      # Exponent tuple encoding and Kolmogorov proof of infinite primes
│   ├── PrimeReconstruction.lean   # Bivariate reconstruction (n = p_m * k) and analytic reduction for π(n)
│   └── WeakPNT.lean               # Core Bit-Balance Inequality, Weak PNT, iterated bounds, exponential bridge
├── KolmogorovPrimes.lean          # Root library module importing all verified files
├── Main.lean                      # Verification entry point
└── lakefile.toml                  # Lake build configuration and dependencies
```

### Summary of Main Formalized Results

| Module | Theorem Identifier | Mathematical Statement Verified |
| :--- | :--- | :--- |
| `Basic.lean` | `decodeBin_bin` / `bin_injective` | $\forall n \in \mathbb{N}, \text{decodeBin}(\text{bin}(n)) = n \implies \text{Injective}(\text{bin})$ |
| `Basic.lean` | `length_bin_pos` | $n \neq 0 \implies \|\text{bin}(n)\| = \lfloor\log_2 n\rfloor + 1$ |
| `Basic.lean` | `exists_incompressible_word` | $\forall M, m, \exists w \in \{0,1\}^m, M.\text{ecomplexity}(w) \ge m$ |
| `SelfTerminatingCode.lean` | `bar_append_inj` | $\overline{w_1}v_1 = \overline{w_2}v_2 \implies w_1 = w_2 \land v_1 = v_2$ |
| `SelfTerminatingCode.lean` | `code_append_inj` / `length_code_le` | Prefix-free property of $\text{code}(w)$ and $\|\text{code}(w)\| \le \|w\| + 2\lfloor\log_2 \|w\|\rfloor + 3$ |
| `SelfTerminatingCode.lean` | `code2_append_inj` / `length_code2_le` | Prefix-free property of $\text{code}_2(w)$ and iterated double-logarithmic length bound |
| `InfinitudePrimes.lean` | `false_of_finite_prime_exponents` | Contradiction for incompressible $n$ under $k$ finite primes: $k(2\lfloor\log_2\lfloor\log_2 n\rfloor\rfloor + 3) + c < \lfloor\log_2 n\rfloor + 1 \implies \bot$ |
| `PrimeReconstruction.lean` | `reconstructFromPrime_div` | $p_m \mid n \implies p_m \cdot (n / p_m) = n$ |
| `PrimeReconstruction.lean` | `analytic_reduction_prime_bound` | $p_m \le m(\lfloor\log_2 m\rfloor)^2 \implies p_m \le \pi(p_m)(\lfloor\log_2 p_m\rfloor)^2$ |
| `WeakPNT.lean` | `log2_nthPrime_le_code_length` | **Core Bit-Balance Inequality:** $\lfloor\log_2 p_m\rfloor \le \|\text{enc\_m}\| + c$ |
| `WeakPNT.lean` | `log2_nthPrime_le_compact_code` | $\lfloor\log_2 p_m\rfloor \le \lfloor\log_2 m\rfloor + 2\lfloor\log_2(\lfloor\log_2 m\rfloor + 1)\rfloor + c + 4$ |
| `WeakPNT.lean` | `nthPrime_lt_compact_code_bound` | $p_m < 2^{c+5}(m + 1)(\lfloor\log_2 m\rfloor + 2)^2$ |
| `WeakPNT.lean` | `log2_nthPrime_le_iterated_code` | $\lfloor\log_2 p_m\rfloor \le \lfloor\log_2 m\rfloor + \lfloor\log_2(\lfloor\log_2 m\rfloor + 1)\rfloor + 2\lfloor\log_2(\lfloor\log_2(\lfloor\log_2 m\rfloor + 1)\rfloor + 1)\rfloor + c + 5$ |

---

## How to Build and Verify

### Prerequisites

* **Lean 4** and **Lake** (managed via [`elan`](https://github.com/leanprover/elan)). The exact compiler version is pinned in `lean-toolchain`.

### Build Instructions

1. Clone the repository:

```bash
git clone <YOUR_REPO_URL>
cd KolmogorovPrimes
```

2. Fetch the precompiled Mathlib / Complexitylib cache (avoids compiling Mathlib from scratch):

```bash
lake exe cache get
```

3. Build and verify all formal proofs:

```bash
lake build
```

4. Audit for completeness (verify zero sorry tokens):

```bash
grep -rn "sorry" KolmogorovPrimes/
```

## References

* U. Schöning and R. Pruim, Gems of Theoretical Computer Science, Springer, 1998 (Topic 9: "Kolmogorov Complexity and the Incompressibility Method").

* M. Li and P. Vitányi, An Introduction to Kolmogorov Complexity and Its Applications, 4th ed., Springer, 2019.

* cslib-community/complexitylib and leanprover-community/mathlib4.
