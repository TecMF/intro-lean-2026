# Formalizing the Weak Prime Number Theorem and Its Iterated Refinements via Kolmogorov Complexity

**Assignee: Gabriel Resende Machado — INF2290 (2026.2).**

---

## Main Objective

The main goal of this project is the **first complete, step-by-step, `sorry`-free formalization in Lean 4** of three things: the **Incompressibility Method**, the **Weak Prime Number Theorem**, and its **iterated logarithmic refinement**. The work follows Schöning & Pruim, [*Gems of Theoretical Computer Science*, Topic 9](docs/references/schoning_topic9_kolmogorov_complexity.pdf), Exercises 9.1–9.5:

$$
\pi(n) \ge \frac{n}{C\,(\log_2 n)^2} \quad\Longleftrightarrow\quad p_m \le C \cdot m\,(\log_2 m)^2,
\quad\text{refined to} \\
p_m = \mathcal{O}\big(m \log_2 m\,(\log_2\log_2 m)^2\big).
$$

The argument is a **"proof by decompressor"**. Factor an incompressible integer $n$ as $n = p_m \cdot k$. Then $n$ can be described by the pair $\langle m, k\rangle$ alone. If primes were scarce, $m$ would be small, so this pair would compress $n$ below its Kolmogorov complexity, which is a contradiction. The textbook presents this argument as a semi-formal sketch. It glosses over boundary ambiguity when bit strings are concatenated, and it uses real-valued identities such as $\log_2(n/p) = \log_2 n - \log_2 p$. This project checks every one of those steps mechanically.

Developed as the final project for **INF2290 (Formalization in Lean)** at **PUC-Rio**.

### Enabling Challenge: Bridging Mathlib and Complexitylib

The proof needs primitives from two libraries that are not connected to each other:

* **Mathlib** (`Mathlib.NumberTheory.PrimeCounting`) provides primes, `Nat.nth`, and `Nat.log`, but has no notion of Kolmogorov complexity.
* **Complexitylib** (`Cslib.Kolmogorov`) provides abstract Kolmogorov complexity over bit strings, but has no arithmetic encodings or self-terminating codes.

Building a `sorry`-free bridge between them required solving three problems:

* **Dynamic injectivity over binary words:** a variable-length `BinWord := List Bool` must decode uniquely through a hierarchy of self-terminating codes, without boundary errors or lookahead during structural induction.
* **Precise discrete integer estimation:** the proofs use exact inequalities over $\mathbb{N}$, such as the superadditivity $\lfloor\log_2 p\rfloor + \lfloor\log_2 k\rfloor \le \lfloor\log_2 (p\cdot k)\rfloor$, so that quotient bits cancel without real-number approximations.
* **Formal non-vacuity:** the incompressibility hypothesis (`h_incomp`) is shown to be satisfiable, so the theorems are not vacuously true.

---

## Key Contributions

1. **Complete Weak PNT Formalization (`InfinitudePrimes.lean`, `PrimeReconstruction.lean`, `WeakPNT.lean`):** A mechanical verification of the Schöning & Pruim exercises, with zero `sorry`:
   * **Exercise 9.1:** infinitude of primes via exponent-tuple compression;
   * **Exercises 9.2–9.3:** the discrete analytic reduction from upper bounds on $p_m$ to lower bounds on $\pi(n)$;
   * **Exercise 9.4:** the Core Bit-Balance Inequality $\lfloor\log_2 p_m\rfloor \le \vert\text{enc}_m\vert + c$ and the explicit Weak PNT bound $p_m < 2^{c+5}(m+1)(\lfloor\log_2 m\rfloor + 2)^2$, i.e. $\pi(n) = \Omega(n/\log_2^2 n)$;
   * **Exercise 9.5:** the iterated refinement $p_m = \mathcal{O}(m \log_2 m (\log_2\log_2 m)^2)$.
2. **Constructive Hierarchy of Self-Terminating Codes (`SelfTerminatingCode.lean`):** Three prefix-free encoding schemes that let two integers share one binary tape without boundary ambiguity:
   * **Elementary Bit-Doubling Code (`bar`):** a total, lookahead-free flag-prefixed construction with $\vert{}\overline{w}\vert{} = 2\vert{}w\vert{} + 1$;
   * **Compact Length-Prefixed Code (`code`):** $\text{code}(w) = \overline{\text{bin}(\vert{}w\vert{})}w$, with $\vert{}\text{code}(w)\vert{} \le \vert{}w\vert{} + 2\lfloor\log_2 \vert{}w\vert{}\rfloor + 3$;
   * **Iterated Length-Prefixed Code (`code2`):** $\text{code}_2(w) = \text{code}(\text{bin}(\vert{}w\vert{}))w$, which reduces the header overhead to $\lfloor\log_2 \vert{}w\vert{}\rfloor + 2\lfloor\log_2(\lfloor\log_2 \vert{}w\vert{}\rfloor + 1)\rfloor + 4$;
   * Full mechanical proofs of unique decodability (`bar_append_inj`, `code_append_inj`, `code2_append_inj`). The higher layers are proved by composition and need no extra induction.
3. **Arithmetic–Information Bridge (`Basic.lean`):** Connects canonical little-endian binary representations of natural numbers (`Nat.bits` / `bin`) to `List Bool` (`BinWord`). It proves injectivity through an explicit left-inverse decoder (`decodeBin`) and establishes the exact bit-length identity $\vert{}\text{bin}(n)\vert{} = \lfloor\log_2 n\rfloor + 1$ for $n > 0$. It also connects to Complexitylib's `ENat`-valued `DescriptionMethod.ecomplexity`.
4. **[Technical Report](docs/report/main.pdf) (ACM format):** A short paper that walks through the formalization step by step:
   * **Introduction:** the "proof by decompressor" intuition, why step-by-step formal verification is needed, the library-bridging friction points, and the module architecture;
   * **Background:** asymptotic upper and lower bounds and the $p_m \leftrightarrow \pi(n)$ duality; Classical vs. Weak PNT; Kolmogorov complexity as compression; incompressibility via the Pigeonhole Principle; the prefix-free concatenation problem; and the hierarchy of self-terminating codes;
   * **Tools & Methodology:** a module-by-module tour of the five Lean files;
   * **Verified Results:** compositional prefix-free injectivity, the Core Bit-Balance Inequality, the compact and iterated logarithmic bounds, the exponential bridge to the Weak PNT, and non-vacuity of the hypotheses. It also shows how the computability assumption is isolated in the explicit constant $c$ (`h_desc`);
   * **Final Considerations & Future Work:** Elias $\omega$-coding for $k$-th iterated bounds, a concrete Invariance Theorem in CSLib, and a reusable incompressibility framework.

---

## Why "Weak"? Encoding Overhead vs. Prime Bounds

The Weak PNT is off from the classical $\pi(n) \sim n/\ln n$ by one factor of $\log_2 n$. This gap is not a flaw in the method. It is exactly the bit cost of the **prefix-free header** needed to separate the prime index $m$ from the quotient $k = n/p_m$ on a single binary tape. Each more compact header in the code hierarchy yields a tighter bound on $p_m$. In the table below, $\ell(x) = \lfloor\log_2 x\rfloor$.

| Encoding Scheme (Lean 4) | Verified Codeword Length Bound | Implied Bound on $p_m$ |
| :--- | :--- | :--- |
| Elementary $\overline{w}$ — `bar (bin m)` | $2\ell(m) + 3$ | $\mathcal{O}(m^2)$ |
| Compact — `code (bin m)` | $\ell(m) + 2\ell(\ell(m) + 1) + 4$ | $\mathcal{O}(m \log_2^2 m)$ — **Weak PNT** |
| Iterated — `code2 (bin m)` | $\ell(m) + \ell(\ell(m)) + 2\ell(\ell(\ell(m))) + 5$ | $\mathcal{O}(m \log_2 m (\log_2\log_2 m)^2)$ |

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
├── docs/report/                   # Technical report (ACM format, LaTeX + PDF)
└── lakefile.toml                  # Lake build configuration and dependencies
```

### Summary of Main Formalized Results

| Module | Theorem Identifier | Mathematical Statement Verified |
| :--- | :--- | :--- |
| `Basic.lean` | `decodeBin_bin` / `bin_injective` | $\forall n \in \mathbb{N}, \text{decodeBin}(\text{bin}(n)) = n \implies \text{Injective}(\text{bin})$ |
| `Basic.lean` | `length_bin_pos` / `length_bin_le` | $n \neq 0 \implies \|\text{bin}(n)\| = \lfloor\log_2 n\rfloor + 1$, and $\|\text{bin}(n)\| \le \lfloor\log_2 n\rfloor + 1$ for all $n$ |
| `Basic.lean` | `exists_incompressible_word` | $\forall M, m, \exists w \in \{0,1\}^m, M.\text{ecomplexity}(w) \ge m$ |
| `SelfTerminatingCode.lean` | `length_bar` / `bar_append_inj` | $\|\overline{w}\| = 2\|w\| + 1$ and $\overline{w_1}v_1 = \overline{w_2}v_2 \implies w_1 = w_2 \land v_1 = v_2$ |
| `SelfTerminatingCode.lean` | `code_append_inj` / `length_code_le` | Prefix-free property of $\text{code}(w)$ and $\|\text{code}(w)\| \le \|w\| + 2\lfloor\log_2 \|w\|\rfloor + 3$ |
| `SelfTerminatingCode.lean` | `code2_append_inj` / `length_code2_le` | Prefix-free property of $\text{code}_2(w)$ and iterated double-logarithmic length bound |
| `InfinitudePrimes.lean` | `encodeExponents_inj_of_length_eq` | Equal-length exponent lists with equal encodings are equal: $\text{encodeExponents}(es_1) = \text{encodeExponents}(es_2) \implies es_1 = es_2$ |
| `InfinitudePrimes.lean` | `exponent_le_log2_of_pow_dvd` | $n \neq 0 \land p \ge 2 \land p^e \mid n \implies e \le \lfloor\log_2 n\rfloor$ |
| `InfinitudePrimes.lean` | `false_of_finite_prime_exponents` | Contradiction for incompressible $n$ under $k$ finite primes: $k(2\lfloor\log_2\lfloor\log_2 n\rfloor\rfloor + 3) + c < \lfloor\log_2 n\rfloor + 1 \implies \bot$ |
| `PrimeReconstruction.lean` | `reconstructFromPrime_div` | $p_m \mid n \implies p_m \cdot (n / p_m) = n$ |
| `PrimeReconstruction.lean` | `encodePairCode_inj` / `encodePairCode2_inj` | For $C \in \{\text{code}, \text{code}_2\}$: $C(\text{bin}(m_1))\,\text{bin}(k_1) = C(\text{bin}(m_2))\,\text{bin}(k_2) \implies m_1 = m_2 \land k_1 = k_2$ |
| `PrimeReconstruction.lean` | `analytic_reduction_prime_bound` | $p_m \le m(\lfloor\log_2 m\rfloor)^2 \implies p_m \le \pi(p_m)(\lfloor\log_2 p_m\rfloor)^2$ |
| `WeakPNT.lean` | `add_log2_le_log2_mul` | Superadditivity: $a, b \neq 0 \implies \lfloor\log_2 a\rfloor + \lfloor\log_2 b\rfloor \le \lfloor\log_2 (a \cdot b)\rfloor$ |
| `WeakPNT.lean` | `log2_nthPrime_le_code_length` | Core Bit-Balance Inequality: $\lfloor\log_2 p_m\rfloor \le \vert\text{enc}_m\vert + c$ |
| `WeakPNT.lean` | `log2_nthPrime_le_compact_code` | $\lfloor\log_2 p_m\rfloor \le \lfloor\log_2 m\rfloor + 2\lfloor\log_2(\lfloor\log_2 m\rfloor + 1)\rfloor + c + 4$ |
| `WeakPNT.lean` | `value_bound_of_log2_compact_bound` | Exponential bridge: $\lfloor\log_2 p\rfloor \le \lfloor\log_2 m\rfloor + 2\lfloor\log_2(\lfloor\log_2 m\rfloor + 1)\rfloor + K \implies p < 2^{K+1}(m+1)(\lfloor\log_2 m\rfloor + 2)^2$ |
| `WeakPNT.lean` | `nthPrime_lt_compact_code_bound` | **Weak PNT:** $p_m < 2^{c+5}(m + 1)(\lfloor\log_2 m\rfloor + 2)^2$ |
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

* T. M. Apostol, Introduction to Analytic Number Theory, Springer, 1976.

* T. M. Cover and J. A. Thomas, Elements of Information Theory, 2nd ed., Wiley-Interscience, 2006.

* P. Elias, "Universal Codeword Sets and Representations of the Integers," IEEE Transactions on Information Theory, 21(2):194–203, 1975.

* J. Avigad, K. Donnelly, D. Gray, and P. Raff, "A Formally Verified Proof of the Prime Number Theorem," ACM Transactions on Computational Logic, 9(1), 2007.

* L. de Moura and S. Ullrich, "The Lean 4 Theorem Prover and Programming Language," CADE 2021, Springer.

* The mathlib Community, "The Lean Mathematical Library," CPP 2020, ACM.

* cslib-community/complexitylib and leanprover-community/mathlib4.
