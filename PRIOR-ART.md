# Prior-art search for the rising binomial cubes

**Search date: 2026-11-26.** Within the public sources inspected, we found no earlier proof or Lean formalization of the full coefficientwise result below. This is a bounded literature search. It does not establish priority.

## What would count as an earlier proof?

The target is the entire sequence $R_n(q)=\sum_{k=0}^{n}\binom{n+k}{k}^{3}q^k$. A result must establish $[q^d](R_{n-1}R_{n+1}-R_n^2)\ge0$ for every $n\ge1$ and $d\ge0$, either explicitly or as an instance of a theorem whose hypotheses apply. A row sum at $q=1$, a different power, ordinary binomial coefficients, or a finite range leaves part of the statement uncovered.

## Direct sources

| Source | Findings |
|---|---|
| [Sun’s MathOverflow question 479301](https://mathoverflow.net/questions/479301/on-the-polynomials-sum-k-0n-binomnkkm-qk) | The September 2024 question gives the exact family. Qiping Zhou’s July 2026 answer exhibits a negative quadratic coefficient for $m=5,n=7$. Sun’s follow-up comment explicitly retains $m=3$ among the cases he believes true. |
| [Sun, *A family of polynomials and related congruences and series*](https://arxiv.org/html/2505.02767v4) · [journal article](https://doi.org/10.3934/fcnt.2026009) | Conjecture 1.1(i), second assertion, specializes to the target. The first assertion uses $\binom nk^3$. The [version history](https://arxiv.org/abs/2505.02767) gives February 10, 2026 for v4. |
| [MathDB, problem 368293](https://mathdb.com/p/368293/sun-s-q-log-convexity-conjecture-for-binomial-sums-and-the-p) | A public contribution by Shivam Patel treats higher exponents and explicitly leaves the rising cubic case unresolved. The database summary is dated August 2026 and labels that contribution unverified. It is a lead, not an independent certification of the field’s current status. |

## Related results checked

| Source | What the result covers |
|---|---|
| [Chen, Tang, Wang and Yang, arXiv:0810.2247](https://arxiv.org/abs/0810.2247) | Coefficientwise log-convexity of the ordinary binomial squares $\binom nk^2$. Both the binomial argument and the exponent differ. |
| [Dou and Ren, *On the q-log-convexity conjecture of Sun*](https://arxiv.org/abs/1308.2736) | The coefficient is $\binom nk\binom{2k}{k}\binom{2(n-k)}{n-k}$. Their criterion for self-reciprocal polynomials does not directly apply here: for $n\ge1$ the constant and leading coefficients of $R_n$ are $1$ and $\binom{2n}{n}^3$. |
| [Chen, Wang and Yang, *Recurrence Relations for Strongly q-Log-Convex Polynomials*](https://doi.org/10.4153/CMB-2011-008-5) | The affine two-term triangular recurrence considered there would give an affine ratio on the diagonal. For our triangle the diagonal ratio is $(4-2/n)^3$, so the original triangle does not fit that recurrence. |
| [OEIS A112028](https://oeis.org/A112028) | Records the exact row sums $R_n(1)$. Evaluation at a single value of $q$ loses the signs of individual coefficients. |

## Search terms and limits

English and Chinese queries combined the paper title, DOI, arXiv identifier, MathOverflow question number, OEIS number, the two binomial arguments, and variants of “rising binomial cubes”, “q-log-convexity”, “coefficientwise log-convex”, “Lean”, “上升二项式”, “三次幂” and “逐系数对数凸”. Searches covered indexed research articles, arXiv full-text results, author and publisher pages, public mathematics discussions, and web-indexed formalization projects. The Formal Conjectures module index showed no match for identifiers `479301`, `112028`, `2505.02767` or the name `LogConvex`. Module names cannot rule out a differently named theorem. [Formal Conjectures index](https://google-deepmind.github.io/formal-conjectures/modules/)

The publisher displayed “Cited by(0)” on the search date. Complete forward-citation lists from Google Scholar, OpenAlex, Crossref and Semantic Scholar were not available in this search. Unindexed manuscripts, differently phrased general results and private proofs remain outside the conclusion. [Publisher’s article metrics](https://www.aimsciences.org/article/doi/10.3934/fcnt.2026009)
