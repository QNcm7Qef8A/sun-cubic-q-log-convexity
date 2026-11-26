# Coefficientwise q-log-convexity of the rising binomial cubes

Let

$$
R_n(q)=\sum_{j=0}^{n}\binom{n+j}{j}^{3}q^j.
$$

For every integer $n\ge 1$ and every $d\ge 0$, the coefficient of $q^d$ in $R_{n-1}(q)R_{n+1}(q)-R_n(q)^2$ is nonnegative. This is the exponent-three case of the **second assertion** of Zhi-Wei Sun’s Conjecture 1.1(i). Sun also asks about a different cubic family in the same paragraph. [Original statement](https://arxiv.org/html/2505.02767v4)

## Proof and verification

The theorem `SunCubic.fullPolynomial` is stated over integer polynomials. The proof relates polynomial coefficients to a finite convolution. For $d\le n$ it controls moments of a symmetric binomial weight. For $n<d\le2n$ it computes the endpoint correction in the truncated convolution and bounds it using a fourth moment and polynomial inequalities. For $d>2n$ the coefficient vanishes. [Lean source](SunCubicProof.lean) · [Mathematical proof in Chinese](PROOF.zh.md)

The complete source was checked in Lean Web on 2026-11-26 with “Latest Mathlib with Lean v4.37.0-rc1”. The final command, `#print axioms SunCubic.fullPolynomial`, reported:

```text
'SunCubic.fullPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
```

To check the source in a browser, open Lean Web, choose a Mathlib project and load `SunCubicProof.lean` using **Load → Load file from disk**. Inspect the final entry in **All Messages**. [Lean Web](https://live.lean-lang.org/)

To build from this repository with Git and elan installed, run:

```sh
lake update
lake exe cache get
lake build
lake env lean SunCubicProof.lean
```

The project pins Lean to `v4.37.0-rc1` and mathlib to `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`, the commit for the corresponding mathlib release tag. The original web session reported its toolchain label only. Its exact mathlib revision is unknown. A clean build with the repository pin has not yet been independently confirmed. The SHA-256 digest of the source file exactly as checked is `e389ca5b38851f3ac1a8c590a9349b7d3f1fe246aa215f955d7174fd7d564640`. [mathlib release](https://github.com/leanprover-community/mathlib4/releases/tag/v4.37.0-rc1)

## Prior work and provenance

Sun posed this question publicly in September 2024. Qiping Zhou later gave a counterexample for the fifth power. In the sources searched through 2026-11-26 we found no earlier public proof of the coefficientwise cubic result. The search notes identify related results and gaps in citation-index coverage. [Sun’s question and Zhou’s answer](https://mathoverflow.net/questions/479301/on-the-polynomials-sum-k-0n-binomnkkm-qk) · [Literature search and limitations](PRIOR-ART.md)

AI was used to search for counterexamples and prior work, develop the mathematical proof, write the Lean formalization, and draft the accompanying notes. Lean checked the formal theorem. The literature search and explanatory text were prepared separately from that kernel check.
