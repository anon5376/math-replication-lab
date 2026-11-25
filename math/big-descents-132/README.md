# Big descents in 132-avoiding permutations

For every sufficiently large $n$, the polynomial that counts 132-avoiding permutations by big descents has exactly $\lfloor 2(n-1)/3\rfloor$ distinct roots, all strictly negative. Lean proves this for the defining permutation sum. A separate exact certificate covers every rank from 0 through 52. The eventual proof gives no explicit threshold, so these results leave a possible finite gap in the every-rank claim of Conjecture 4.4. [Elizalde, Rivera and Zhuang](https://arxiv.org/html/2408.15111v2#S4.SS2).

## What Lean counts

`B n` is the sum of `X ^ bigDescents w` over the permutations of `List.range n` that avoid 132. The theorem `mem_words` identifies a forbidden occurrence as an ordered subsequence `[a,b,c]` with `a < c` and `c < b`. The theorem `words_nodup` excludes duplicate permutations. A descent contributes exactly when adjacent entries satisfy `b + 1 < a`. Using the entries 0 through n−1 gives the same comparisons as numbering from 1.

An independent finite proof through rank 10 uses a search tree formed by inserting the next entry. As soon as a word contains a forbidden subsequence, every extension does too. Lean proves that pruning on this rule gives the defining sum. It also proves that a new minimum can be inserted exactly at gaps with an increasing suffix. At rank 10 the computation is split over the fourteen possible orders of the four largest entries. All small arithmetic certificates are checked by kernel reduction.

```lean
theorem finite52_simple_negative (n : ℕ) (hn : n ≤ 52) :
    (B n).natDegree = expectedDegree n ∧ SimpleNegative (B n)
```

Here `expectedDegree n = 2 * (n - 1) / 3` in natural-number arithmetic. `SimpleNegative p` says that `p` is nonzero, splits over ℝ, has a duplicate-free root multiset, and every member of that multiset is strictly negative. A nonzero constant satisfies the definition.

## The recurrence for actual permutations

For a nonempty permutation, `A n` sums the weights of avoiders with the maximum first and `C n` sums the remaining avoiders. Lean proves `B (m+1) = A (m+1) + C (m+1)`, with `B 0 = 1`, `A 1 = 1` and `C 1 = 0`. For every natural number `k` the kernel checks the two subtraction-free identities in the paper's Lemma 2.2. [Elizalde, Rivera and Zhuang, Lemma 2.2](https://arxiv.org/html/2408.15111v2#S2.SS1)

```lean
theorem A_recurrence (k : ℕ) : A (k+2) = A (k+1) + X * C (k+1)
theorem C_recurrence (k : ℕ) : C (k+2) =
    B (k+1) + X * ∑ i ∈ Finset.range k, B (i+1) * B (k-i)
```

The proof splits each word at its maximum. If the left block has length `i` and the right block length `j`, all right entries lie below all left entries. The standardized blocks are avoiders of lengths `i` and `j`. Adding `j` back to each left entry and inserting the maximum recovers the word uniquely. With two nonempty blocks, exactly one new big descent occurs. With the maximum first, it makes a big descent exactly when the following entry differs from the old maximum. A maximum at the end adds none.

## Large-rank results

The main declaration takes no hypotheses.

```lean
theorem BigDescents132.eventual_simple_negative :
    BigDescents132.EventualSimpleNegative
```

Unfolding `EventualSimpleNegative` gives
`∃ N : ℕ, ∀ n ≥ N, (B n).natDegree = expectedDegree n ∧ SimpleNegative (B n)`.
The theorem `degree_all` proves the degree formula separately at every rank.

For every fixed integer $K$ and every real cutoff $T$, all sufficiently large ranks have at least $K$ distinct negative roots below $T$. The necessary rank may depend on both $K$ and $T$. Lean proves this directly for the permutation sum.

```lean
theorem eventually_many_negative_roots (K : ℕ) (T : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∃ s : Finset ℝ, s.card = K ∧
      ∀ x ∈ s, x < T ∧ x < 0 ∧ (B n).IsRoot x
```

### The two endpoint limits

- `small_endpoint_limit` identifies the real pointwise limit of $B_n(u/n^3)/n$ at every fixed $u$. The coefficient of $u^k$ in that limit is $C_k/(3k+1)!$, where $C_k$ is the Catalan number. The pole of each coefficient column gives the fixed-index limit. The recurrence gives the summable bound required to pass to the limit in the entire row. Rational alternating-series bounds give signs −, +, −, + at magnitudes 74, 271, 672 and 1348. Thus `eventual_small_grid` gives four disjoint sign changes between 0 and $-1348/n^3$.
- `Series.far_endpoint_limit` identifies the limit of the normalized reversed polynomial for every real $y$. Write $n=3p+2e+1$, $d=2p+e$, $e\in\{0,1,2\}$, and $b_{n,d}=[t^d]B_n(t)$. Then $B_n^{\mathrm{rev}}(y/n^3)/b_{n,d}$ tends to $H_e(y)=\sum_{j\ge0}e!(y/2)^j/(3j+e)!$. This parametrization covers every sufficiently large rank. `Far.farLimit_witness` proves alternating signs at every indexed witness using the exponential series. Inverting the resulting intervals proves the fixed-$K$ root count below each real cutoff.

`Series.positive_coefficient_formula` proves the following exact identity. Its Lean argument $n$ is one less than the rank. Here $N$ denotes the rank itself.

$$
[t^k]B_N(t)=
\sum_{\substack{m+b=k\\2m+h+b+\ell+1=N}}
 C_m\binom{2m+h}{h}\binom{m+h}{b}\binom{k+\ell}{k}.
$$

All four summation indices are nonnegative. The proof substitutes into the Catalan generating function derived from the verified permutation recurrence. Reindexing by the defect $2(N-1)-3k$ gives an index set independent of $p$ for fixed defect. `Series.diagonal_limit` computes its limit, and `Series.coefficient_envelope` bounds the other terms uniformly as the defect varies. Together they justify the reciprocal limit. Separately, `Series.leading_coefficient_mod_one` gives the exact leading coefficient $C_m$ at rank $3m+1$.

### Cauchy coefficients and the three cuts

Fix $s=1-t>1$. The quartic has four distinguished simple roots, two real roots $1/s<r<1<R<4$, an upper-half-plane root $u$, and its conjugate. Lean proves their existence, uniqueness and continuity in $s$, and $|u|<r$. The product of the four principal radicals $\sqrt{1-z/a}$ squares to the quartic. It selects the generating-function germ at zero and defines a holomorphic rationalized branch on the slit domain. At the apparent pole $z=1/s$ its value is $s/(s-1)$.

`Slit.Points.coefficient_from_cuts` identifies $B_{n+1}(1-s)$ for every $n\ge0$ with $1/(2\pi i)$ times the sum of three absolutely convergent outward jump integrals. Each jump is the counterclockwise boundary value minus the clockwise value. The real jump is supported on $[r,R]$. Beyond $R$ both real radicals reverse sign and the jump vanishes. `Slit.Points.complex_cut` and `Slit.Points.real_cut` give the radial integrals with their explicit multipliers.

The proof applies Cauchy's theorem on rectangles in logarithmic coordinates. The branch has continuous one-sided boundary values on the closed edges, including their branch points. Adding the sector identities cancels the radial seams with their orientations. On the outer circle the branch is $O(1/|z|)$ for each fixed $s$. This bound proves both the outer limit and absolute convergence along the cuts. `Slit.Points.normalized_coefficient` then identifies the literal coefficient with the integral expression used in the cosine estimate.

### Uniform interior estimate and phase

Let $E(s)=\min((s-1)^{1/3},s^{-1/3})$. Write $W_N$ for the complex coefficient at the upper cut and $M_N=\int_0^\infty v^{1/2}(1+v)^{-N-1}\,dv$. Lean proves $2|W_N|M_N>0$ and the following estimate with **one constant for all negative parameters**.

$$
\left|\frac{B_N(1-s)}{2|W_N|M_N}-\cos(\arg W_N)\right|
\le \frac{C}{NE(s)}
\qquad(s>1,\ N\ge 8,\ NE(s)\ge 7).
$$

The theorem is `Slit.uniform_moving_interior`. Absorbing $|1-su|/|1-sr|$ into the real-cut multiplier makes the amplitude comparison uniform as $s$ approaches one. The proof verifies the scaled pole, radical and root separation estimates at both ends, then uses compactness between them. `Slit.compact_interior` gives a uniform $O(1/N)$ bound on any compact parameter subset.

`Slit.phase_continuous` gives a continuous real phase $N\arg u-\phi(s)$ with the required cosine. Its offset tends to $5\pi/6$ as $s\downarrow1$ and $2\pi/3$ as $s\to\infty$. `Slit.small_phase_match` and `Slit.far_phase_match` prove phase limits along arbitrary sequences approaching these ends with a fixed limit for the corresponding scaled coordinate. `Slit.interior_phase_sign` transfers each integer phase extremum to a strict sign of the literal polynomial whenever $NE$ exceeds a single threshold.

### Endpoint signs and assembly

Write $F$ for the near-zero limit and $D(v)=v^{-1/2}\sqrt{1-v^3}$. The Catalan moment proved in `Peak.catalan_moment` is

$$
\int_0^1 D(v)v^{3k+1}\,dv=\frac{\pi C_k}{6\cdot4^k}.
$$

Filtering the exponential series by exponents congruent to 1 modulo 3 and integrating gives `Peak.smallLimit_integral`. For $q>0$ it states

$$
F(-q^3/4)=\frac{2}{\pi q}\int_0^1 D(v)\left[2e^{qv/2}\cos(\sqrt{3}qv/2-\pi/3)-e^{-qv}\right]dv.
$$

Reflecting the oscillatory integral at $v=1$ gives a leading complex Laplace integral and an error. `Peak.ray_lap` evaluates the leading term, and `Peak.peak_approx` bounds the error by integrating separately on $(0,1/2)$, $(1/2,1)$ and $(1,\infty)$. `Peak.error_strict` proves that the error is smaller than the leading amplitude for every real $q\ge20$. Consequently, for $w_i=2(i\pi+5\pi/6)/\sqrt 3$, `Peak.witness_sign` proves $(-1)^i F(-w_i^3/4)>0$ for every $i\ge5$. The four exact rational samples supply indices 1 through 4, and $F(0)=1$ supplies index 0.

`Peak.near_grid` and `Peak.far_grid` transfer the limiting signs to finite-rank polynomials at each required sample. `Peak.phase_left_limit` and `Peak.phase_right_limit` place the grid endpoints between the correct surrounding interior phase levels in all three residue classes. `Peak.all_endpoint_grids` provides both grids for every prescribed interior error threshold and all sufficiently large ranks. `Slit.certificate_of_endpoint_grid` uses ordered intermediate-value crossings to supply the middle intervals. Together the intervals account for the full degree, which proves `eventual_simple_negative`.

## Exact arithmetic through rank 52

`replay52.py` computes coefficients twice. One method uses the first-maximum recurrence in the paper. The other inserts a new minimum. In a 132-avoider the entries after its minimum are increasing. A new minimum can be inserted in any gap of this increasing final run, starting just before the old minimum. The run length and the size class of its preceding drop determine the change in the statistic. The two resulting tables agree through rank 52. [Elizalde, Rivera and Zhuang, Lemma 2.2](https://arxiv.org/html/2408.15111v2#S2.SS1).

Across the 53 coefficient rows, the script finds 867 intervals with strictly opposite endpoint signs using integer arithmetic. `Data52.lean` records the coefficients and rational samples. Lean verifies all 51 recurrence steps against the proven polynomial identities and checks the rational signs for every row. `B_eq_row_through52` identifies each total row with the defining permutation sum. `finite52_simple_negative` then gives the exact degree and all roots for that range. With `--lean`, the script regenerates the data, compares them to the tracked file, and independently replays each row and its witnesses against `B n`.

## Reproduce

Run from this directory with Elan and Python 3.10 or later. The toolchain is Lean 4.19.0. The Lake manifest pins mathlib to `c44e0c8ee63ca166450922a373c7409c5d26b00b` and records each transitive revision.

```sh
lake exe cache get
lake clean big-descents-132
lake build
lake env lean Axioms.lean
python3 replay52.py --lean
lake env lean --run Replay.lean
```

The package-scoped clean deletes the project build products and retains dependency caches. `Axioms.lean` prints the target definition, theorem types and axiom dependencies. The root theorems use the standard `propext`, `Classical.choice` and `Quot.sound`. `Replay.lean` separately rechecks the compiled project declarations with Lean’s kernel, one module at a time over its declared imports. The replay traverses every local module reachable from the default library. The standalone `leanchecker` executable was unavailable in the pinned Linux distribution.
