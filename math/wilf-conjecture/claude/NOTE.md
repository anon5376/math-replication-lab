# Apéry factorization down-sets and Wilf's conjecture: an exact slack formula and the criteria it gives

**Result type: THEOREM (sufficient criteria, fully proved). No counterexample. Wilf's conjecture for e = 5 is not settled here.**

Notation throughout: S ≠ ℕ is a numerical semigroup with multiplicity m ≥ 2, minimal generators m < a_1 < … < a_k (so e = k + 1 ≥ 2), conductor c, genus g, n = c − g, and W = e·n − c = k·n − g.

## 0. Summary

| # | Statement | Status |
|---|---|---|
| L1 | Normal-form factorizations of the Apéry set form a down-set B ⊂ ℕ^k of size m, for any monomial tie-break | proved here; known for lex (Zhai 2011) |
| L2 | (k+1)·Σ_B a·x = Σ_{x∈B} Σ_i a·top_i(x) for every finite down-set | proved here; it is the equality hiding in Zhai's Lemma 3 |
| A | **m·W = Σ_{x∈B} Σ_{i≤k} D(top_i(x)) − (k−1)·m(m−1)/2** | proved; exact slack of Zhai's bound W ≥ −(e−2)(m−1)/2 |
| B | W = Σ δ(top) + (anti-carries) − (carries); carry-free normal forms ⟹ W ≥ 0 | proved |
| B2 | Explicit rays ⟨m, qm+r_1, …, qm+r_k⟩: W = q·σ − k·ρ ≥ 0 for all q ≥ 1 under a finite hypothesis (G) | proved; e.g. ⟨22, 22q+1, 22q+5, 22q+6, 22q+7⟩, type 9 |
| C | **W ≥ (em+e−2)/2 − (1/m)·Σ_{w∈Ap, w≥c} (ℓ(w)+e−1)(w−c+1)**, ℓ = least factorization length; only the Apéry elements in [c, c+m) enter | proved |
| C+ | m·W ≥ m·(km − N_T) + R(B) − (k−1)·m(m−1)/2, R a rearrangement sum of the shape | proved |
| G | **W ≥ ((e−2)(m+1−2d) − d(d−1))/2, where d is the number of gaps in [c−m, c)**; more generally a sum over the windows [c−(j+1)m, c−jm) | proved |
| G1 | **Wilf holds if d(d−1) ≤ (e−2)(m+1−2d)**; with Eliahou's theorem (3e ≥ m), Wilf holds whenever [c−m, c) has at most e−1 gaps | proved (second part uses Eliahou's theorem) |
| S | For k ≥ 2 and L ≥ 2 the simplex {x : x_1+…+x_k ≤ L} is not a lattice tile; a tile containing it has strictly more cells, by an explicit margin | proved |
| – | Conjecture C: the right side of Theorem C is ≥ 0 for every numerical semigroup (it is 0 on both known W = 0 families) | **conjectured**; proved without wraps (C3) and under G1's condition; true for all 1 179 596 semigroups of genus ≤ 25 and every semigroup scanned in §9 (46.5 million with e = 5, 32.5 million with e from 3 to 9) |
| – | Conjecture Φ: the right side of C+ with T replaced by all maximal cells is ≥ 0 for every Apéry down-set | **conjectured**; no counterexample in the scans of §9 |
| – | Wilf-type inequality for weighted down-set *tiles* without Apéry minimality (the closing question of Hellus–Rechenauer–Waldi) | **open**; no counterexample in §8 |

What the criteria reach (exact counts in §9): Theorem C certifies W ≥ 0 for every one of the 34 776 387 semigroups with e = 5 in the first three exhaustive scans, for 11 731 460 more on stabilized rays, and for every numerical semigroup of genus ≤ 25. Corollary G1, a closed formula in m, e and the number of gaps in the last window, certifies 34 685 075 of the 34 776 387. Of these semigroups 24 592 298 have type ≥ 5, where the classical criterion t ≤ e − 1 does not apply.

What they do not reach: these are lower bounds, not Wilf. Theorem G needs d ≲ √((e−2)m), and the semigroups with the smallest Wilf numbers have d near m/2. Theorem C would give Wilf for all semigroups if the Apéry elements in [c, c+m) could never crowd the top of that window (Conjecture C); I have no proof of that, and shape alone does not give it (§7). That is the first remaining obstacle (§12).

## 1. Conventions and edge cases

- S ≠ ℕ, so m ≥ 2 and e ≥ 2. (For S = ℕ: e = 1, c = g = n = 0, W = 0.)
- Ap = Ap(S, m) = {w_0 = 0, w_1, …, w_{m−1}}, w_r the least element of S congruent to r mod m.
- Standard facts used: c = max(Ap) − m + 1 and g = Σ_r ⌊w_r/m⌋. (In class r the members of S are w_r + mℕ; the gaps are r, r+m, …, w_r − m.) Put M = max(Ap) = c + m − 1.
- No Apéry element has a factorization using m (it would give w − m ∈ S). So each w ∈ Ap is a·x for some x ∈ ℕ^k, where a = (a_1, …, a_k).
- Each a_i is itself an Apéry element whose only factorization is the unit vector e_i.
- "Depth" q = ⌈c/m⌉ and ρ = qm − c ∈ [0, m), as in Eliahou's papers. Then M = qm + f with f = m − 1 − ρ.

## 2. The down-set of normal forms (known machinery, re-derived)

**Order and tie-breaking.** Fix a total order ≺ on ℕ^k compatible with addition (x ≺ y ⟹ x + z ≺ y + z). Four are implemented: `lex`, `revlex`, `deglex` (length |x| = Σx_i first, then lex), `minres` (Σ x_i·(a_i mod m) first, then lex). For each residue r let nf(r) be the ≺-least x ∈ ℕ^k with a·x = w_r, and B = {nf(r)}. The order only ever compares factorizations of the same integer; "weight first, ≺ second" is the underlying monomial order.

**Lemma 1.** (a) x ↦ a·x mod m is a bijection B → ℤ/m and a·x ∈ Ap for x ∈ B. (b) If x ∈ B and 0 ≤ y ≤ x coordinatewise, then y ∈ B and y = nf(a·y mod m).

*Proof.* (a) is the definition. (b) Put z = x − y. If a·y − m ∈ S then a·x − m = (a·y − m) + a·z ∈ S, impossible; so a·y ∈ Ap. Let y′ be the normal form of a·y. If y′ ≠ y then y′ ≺ y, so y′ + z ≺ y + z = x and a·(y′ + z) = a·x, contradicting the minimality of x. ∎

This is Zhai's observation (arXiv:1111.2779, proof of Theorem 1) for the lexicographic order; the argument is the same for any monomial order.

**The target identity.** Σ_B a·x = Σ_r w_r = m·g + m(m−1)/2. Hence the mean weighted degree is g + (m−1)/2, and Wilf (g ≤ (k/(k+1))·c) is

    mean_B(a·x) ≤ (k/(k+1))·c + (m−1)/2          (k = 4:  ≤ (4/5)c + (m−1)/2).

Equivalently mean_B(a·x) ≤ (k/(k+1))·M − (k−1)(m−1)/(2(k+1)). This is formula (10) of Hellus–Rechenauer–Waldi (arXiv:1804.06141).

**Chains.** For x ∈ B and a direction i, the set {x + j·e_i} ∩ B is {x − x_i e_i + j e_i : 0 ≤ j ≤ p} for some p (Lemma 1). Write top_i(x) for its top element and h_i(x) = p − x_i.

**Lemma 2 (chain reversal).** For every finite down-set B ⊂ ℕ^k and a ∈ ℝ^k:

    (k+1)·Σ_{x∈B} a·x = Σ_{x∈B} Σ_{i=1}^{k} a·top_i(x).

*Proof.* On one i-chain with p + 1 elements, Σ_j j = Σ_j (p − j), i.e. Σ_chain x_i = Σ_chain h_i(x). So Σ_B a_i x_i = Σ_B a_i h_i(x) = Σ_B (a·top_i(x) − a·x). Sum over i: Σ_B a·x = Σ_{x,i} a·top_i(x) − k·Σ_B a·x. ∎

**Generic inequality (Zhai, Lemma 3).** If a ≥ 0 then a·top_i(x) ≤ max_B a·x, so mean_B(a·x) ≤ (k/(k+1))·max_B(a·x) for every finite down-set. Zhai proves it by the same reversal and then bounds the top by the maximum; Lemma 2 keeps the top. For Apéry sets it gives Zhai's Theorem 1, W ≥ −(e−2)(m−1)/2. It is sharp for the simplex with equal weights, and it uses nothing about residues.

**The missing term.** Comparing with the target: the generic inequality is weaker than Wilf by exactly (k−1)(m−1)/(2(k+1)) in the mean, i.e. (k−1)·m(m−1)/2 after clearing denominators. Since Σ_B (a·x mod m) = m(m−1)/2, the term to be recovered is (k−1) times the sum of the residues.

## 3. Theorem A: the exact slack

For x ∈ B put D(x) = M − a·x ≥ 0, δ(x) = ⌊D(x)/m⌋ and D̄(x) = D(x) − m·δ(x). Then δ(x) = #{j ≥ 0 : a·x + jm < c}, so n = Σ_B δ(x); and D̄ is a bijection B → {0, …, m−1}.

**Theorem A.** m·W = Σ_{x∈B} Σ_{i=1}^{k} D(top_i(x)) − (k−1)·m(m−1)/2.

*Proof.* By Lemma 2, Σ_{x,i} D(top_i(x)) = kmM − (k+1)·Σ_B a·x = km(c + m − 1) − (k+1)(mg + m(m−1)/2) = m(kc − (k+1)g) + (k−1)m(m−1)/2, and kc − (k+1)g = (k+1)(c − g) − c = W. ∎

With μ(t) = #{(x,i) : top_i(x) = t} = Σ_{i : t+e_i ∉ B} (t_i + 1), so that Σ_t μ(t) = km:

    m·W = Σ_t μ(t)·D(t) − (k−1)·m(m−1)/2 = m·Σ_t μ(t)·δ(t) + Σ_t (μ(t) − (k−1))·D̄(t).        (A′)

So Wilf says: the μ-weighted mean of the deficits D over chain tops is at least (k−1)(m−1)/(2k). A uniformly random cell has mean residue deficit (m−1)/2; the chain tops are the heavy cells, and the conjecture is that they cannot all sit just below M.

Equality checks: e = 2 (B a chain, one top with D = 0) gives W = 0; ⟨m, qm+1, …, qm+m−1⟩ (B = {0, e_1, …, e_{m−1}}) gives W = 0.

The proof uses only: B a down-set of size m, and a·x mod m bijective on B. Minimality of the weights is not used.

## 4. Theorem B: carries

Let ρ_i(x) = x_i a_i mod m, carry(x) = ⌊a·x/m⌋ − Σ_i ⌊x_i a_i/m⌋ = ⌊Σ_i ρ_i(x)/m⌋ ∈ [0, max(0, |supp x| − 1)], and ε_i(x) = ⌊(D̄(top_i(x)) + ρ_i(x))/m⌋ ∈ {0, 1}.

**Theorem B.** W = Σ_{x,i} δ(top_i(x)) + Σ_{x,i} ε_i(x) − Σ_x carry(x). In particular W ≥ 0 if carry(x) = 0 for all x ∈ B, for some monomial order.

*Proof.* Reflection on the i-chain is a bijection of B, and the reflected element sits x_i steps below the top, so n = Σ_x ⌊(D(top_i(x)) + x_i a_i)/m⌋ = Σ_x (δ(top_i(x)) + ⌊x_i a_i/m⌋ + ε_i(x)). Sum over i and subtract g = Σ_x ⌊a·x/m⌋ = Σ_{x,i} ⌊x_i a_i/m⌋ + Σ_x carry(x); W = kn − g. ∎

**Corollary B1 (no wrap).** Write a_i = q_i m + r_i, 1 ≤ r_i ≤ m − 1, and λ(t) = Σ_i q_i t_i. If every Apéry element has a factorization x with Σ x_i r_i ≤ m − 1, then W = Σ_{x,i} (q − λ(top_i(x))) − kρ ≥ 0, with q the depth and ρ = qm − c.

*Proof.* All factorizations x of an Apéry element w have r·x ≡ w mod m, so one with r·x ≤ m − 1 has the least possible r·x, and the `minres` normal form has r·x = (w mod m). Hence there are no carries and ⌊a·x/m⌋ = λ(x) on B. Lemma 2 for the weight vector (q_i) gives (k+1)g = Σ_{x,i} λ(top_i(x)), and W = k(qm − ρ) − (k+1)g. Non-negativity is Theorem B. (Directly: the ρ cells with residue above f = m − 1 − ρ have all k of their tops again of residue above f, hence of level ≤ q − 1; that is the kρ.) ∎

**Corollary B2 (uniform rays).** Let 1 = r_1 < … < r_k ≤ m − 1. Let N(v) be the least number of r_i's summing to v, and N_cyc(v) the least number summing to v modulo m. Assume

    (G)   N_cyc(v) = N(v) for all 0 ≤ v < m.

Put L = max N, f = max{v : N(v) = L}, ρ = m − 1 − f, σ = kLm − (k+1)·Σ_{v<m} N(v), and τ = #{v : for every i, v + r_i ≥ m or N(v + r_i) ≤ N(v)}. Then for every q ≥ 1 the semigroup S_q = ⟨m, qm + r_1, …, qm + r_k⟩ has:

1. Ap(S_q) = {qm·N(v) + v : 0 ≤ v < m};
2. embedding dimension k + 1;
3. c = qmL − ρ, g = q·ΣN(v), W = qσ − kρ, and σ ≥ kρ, so W ≥ (q − 1)σ ≥ 0;
4. type τ for q ≥ 2.

*Proof.* (1) If r·x = v + jm with 0 ≤ v < m, j ≥ 0, then a·x = m(q|x| + j) + v ≥ mq·N_cyc(v) + v = mq·N(v) + v, with equality for a shortest exact representation of v. (2) Each qm + r_i is the Apéry element of residue r_i. Every element of S_q not divisible by m is ≥ qm + 1, so a sum of two nonzero elements with residue r_i is ≥ (q+1)m + 1 > qm + r_i. (3) By (1) the largest Apéry element is qmL + f, so c = qmL − ρ and g = q·ΣN(v); then W = kc − (k+1)g = qσ − kρ. The shortest exact representations do not wrap, so B1 gives W ≥ 0 for every q; at q = 1 this is σ ≥ kρ. (4) An Apéry element w is maximal in the order "w ≤ w′ iff w′ − w ∈ S" iff no w + a_i is an Apéry element (summands of Apéry elements are Apéry elements). Here w_v + a_i = qm(N(v) + 1) + v + r_i. If v + r_i < m this is Apéry iff N(v + r_i) = N(v) + 1. If v + r_i ≥ m it would need q(N(v) + 1) + 1 = q·N(v + r_i − m), impossible mod q for q ≥ 2. ∎

Explicit instance (hypothesis (G) checked by two independent routines in `uniform_rays.py`): m = 22, r = (1, 5, 6, 7). Here N = 0,1,2,3,4,1,1,1,2,3,2,2,2,2,2,3,3,3,3,3,3,3 for v = 0..21, L = 4, f = 4, ρ = 17, ΣN = 49, σ = 107, τ = 9. So for every q ≥ 1:

    S_q = ⟨22, 22q+1, 22q+5, 22q+6, 22q+7⟩:   e = 5,  c = 88q − 17,  g = 49q,  n = 39q − 17,  W = 107q − 68,  type 9 (q ≥ 2).

For q ≥ 3 these lie outside every solved range listed in §10 (m = 22, 3e < m, c > 4m, m ∤ c, g = 49q > 100, type 9 > e − 1, n > 12, and 2g ≠ F + t so not almost symmetric). They are an infinite family in the carry-free class, but their Wilf numbers are also immediate from (1), so they illustrate the class and do not need the theorem. `uniform_rays.py scan 20 30` lists how many (m; r) satisfy (G) with τ ≥ 5.

## 5. Theorems C and G: few heavy chain tops, few gaps in the last windows

Let T = {t ∈ B : a·t ≥ c} = {t : δ(t) = 0}. Each t ∈ T is a maximal cell of B, because a·(t + e_i) ≥ c + m + 1 > M; hence μ(t) = |t| + k. As integers, T is Ap ∩ [c, c + m) = {h + m : h a gap, h ≥ c − m}. Every gap h ≥ c − m is pseudo-Frobenius (h + s ≥ c for s ∈ S∖{0}), so |T| is both the number of gaps in [c − m, c) and the number of pseudo-Frobenius numbers there. Put N_T = Σ_{t∈T} (|t| + k).

**Theorem C.** Let ℓ(w) be the least number of minimal generators in a factorization of w. Then

    W ≥ (em + e − 2)/2 − (1/m)·Σ_{w ∈ Ap, w ≥ c} (ℓ(w) + e − 1)·(w − c + 1).

Each Apéry element of the threshold interval [c, c + m) is weighted by its position w − c + 1 ∈ [1, m]. In terms of gaps: the sum runs over the gaps h ≥ c − m, with w = h + m and (w − c + 1)/m = 1 − (F − h)/m.

*Proof.* By Theorem A, m·W = Σ_t μ(t)D(t) − (k−1)m(m−1)/2. For t ∉ T, D(t) ≥ m. For t ∈ T, μ(t) = |t| + k and m − D(t) = a·t − c + 1. So Σ_t μ(t)D(t) ≥ km² − Σ_{t∈T} (|t| + k)(a·t − c + 1). With the `deglex` order |t| = ℓ(a·t). ∎

Weaker forms, with d = |T| the number of gaps in [c − m, c):

- *(C1)* The positions a·t − c + 1 are d distinct integers in [1, m] and |t| + k ≥ e, so Σ_T (|t| + k)(a·t − c + 1) ≤ m·N_T − e·d(d−1)/2, and W ≥ (em + e − 2)/2 − N_T + e·d(d−1)/(2m).
- *(C2)* If every ℓ(w) ≤ λ, then W ≥ (em + e − 2)/2 − (λ + e − 1)·d·(1 − (d−1)/(2m)). One may take λ = min(m − 1, ⌊(c + m − 1)/a_1⌋) ≤ q, with a_1 the least generator above m: the box [0, x] ⊂ B has at least |x| + 1 cells, and a_1|x| ≤ a·x ≤ c + m − 1.

Equality: Theorem C is an equality for e = 2 and for ⟨m, qm+1, …, qm+m−1⟩.

**Conjecture C.** For every numerical semigroup, Σ_{w ∈ Ap, w ≥ c} (ℓ(w) + e − 1)(w − c + 1) ≤ m(em + e − 2)/2. By Theorem C this implies Wilf's conjecture. It only involves the Apéry elements in [c, c + m) and their shortest factorizations. Equivalently: the μ-weighted mean over T of the deficit D(t) = c + m − 1 − a·t is at least m − m(em + e − 2)/(2N_T). Since N_T ≤ km, this can fail only if more than (k+1)/(2k) of all chain tops lie in the window (N_T > ((k+1)m + k − 1)/2) and, in addition, those Apéry elements crowd the top of the window (mean deficit below (k−1)(m−1)/(2k)). In [25, 36, 42, 43, 44], N_T = 84 of 100 and the mean deficit is 10.6 against a threshold of 5.95. Evidence in §9; I have no proof. The mechanism that seems to prevent crowding: for many chain tops to lie in the window the generators must be nearly equal, and then distinct cells of the same length have weights that differ by small integer combinations, which either coincide (a tie, removing cells from B) or spread over a range much longer than d.

**Proposition C3 (Conjecture C holds without wraps).** Under the hypothesis of Corollary B1 (every Apéry element has a factorization x with Σ x_i r_i ≤ m − 1) the bound of Theorem C is ≥ 0.

*Proof.* Use the `minres` normal forms; their lengths are at least the minimal ones, so it suffices to show m((k+1)m + k − 1)/2 ≥ Σ_{t∈T} μ(t)(a·t − c + 1) for this B. Here a·x = mλ(x) + r·x with r·x ≤ m − 1 the residue. Write M = mq + f and ρ = m − 1 − f. Then T = T_q ∪ T_{q−1}, where T_q is the set of cells of level q (all have r·t ≤ f) and T_{q−1} the set of cells of level q − 1 with r·t ≥ f + 1; the position a·t − c + 1 is m − f + r·t on T_q and r·t − f on T_{q−1}. Lemma 2 for the weight vector r gives Σ_t μ(t)·r·t = (k+1)m(m−1)/2, and Σ_t μ(t) = km. Substituting,

    m((k+1)m + k − 1)/2 − Σ_{t∈T} μ(t)(a·t − c + 1) = Σ_{t∉T} μ(t)(1 + r·t) − ρ·μ(T_q) + (f + 1)·μ(T_{q−1}).

Let R be the ρ cells with r·x ≥ f + 1. For x ∈ R every top_i(x) has r-value ≥ r·x, so it lies in R: it is in T_{q−1} or outside T, never in T_q. These kρ pairs contribute at least kρ(f + 1) to the first and third terms, and they show μ(T_q) ≤ km − kρ. So the right side is at least kρ(f + 1) − ρk(m − ρ) = 0. ∎

So Conjecture C is proved in two ranges: without wraps (C3), and when d(d−1) ≤ (e−2)(m + 1 − 2d) (below). The identity in the proof was checked on 4 578 random no-wrap semigroups (`nowrap_check.py`).

**Theorem C+ (rearrangement).** Let μ_0 ≥ μ_1 ≥ … ≥ μ_{m−1} be the decreasing rearrangement of (μ(t))_{t∈B} and R(B) = Σ_j j·μ_j. Then

    m·W ≥ m·(km − N_T) + R(B) − (k−1)·m(m−1)/2.

*Proof.* In (A′), δ(t) ≥ 1 for t ∉ T, and Σ_{t∉T} μ(t) = km − N_T. D̄ is a bijection onto {0, …, m−1}, so Σ_t μ(t)D̄(t) ≥ Σ_j j·μ_j by the rearrangement inequality. ∎

Neither of C and C+ implies the other; C+ is also an equality on the two families above.

**Lemma 3 (chain tops cannot share many cells).** For every U ⊆ B, the number of pairs (x, i) with top_i(x) ∈ U satisfies

    μ(U) = Σ_{t∈U} μ(t) ≤ m + (k−1)·|U| + |U|(|U|−1)/2.

*Proof.* Let I(x) = {i : top_i(x) ∈ U}, so μ(U) = Σ_x |I(x)|. For x ∈ U use |I(x)| ≤ 1 + (k−1). For x ∉ U with I(x) ≠ ∅ use r ≤ 1 + r(r−1)/2 for integers r ≥ 1. So μ(U) ≤ m + (k−1)|U| + Σ_{x∉U} C(|I(x)|, 2). If x ∉ U and i ≠ j lie in I(x), then t = top_i(x) = x + s·e_i and t′ = top_j(x) = x + s′·e_j with s, s′ ≥ 1, so t ≠ t′ and t − t′ = s·e_i − s′·e_j. The pair {t, t′} determines i, s and hence x = t − s·e_i. So distinct (x, {i, j}) give distinct 2-subsets of U, and the last sum is at most C(|U|, 2). ∎

**Theorem G (gaps in the last windows).** For j ≥ 0 let D_j be the number of integers in [c − (j+1)m, c − jm) that are not in S (negative integers count as non-members), and d = D_0 the number of gaps in [c − m, c). Then, for any set J of indices j ≥ 0,

    W ≥ Σ_{j∈J} [ (e−2)(m − D_j) − D_j(D_j − 1)/2 ] − (e−2)(m−1)/2,

and in particular

    W ≥ ( (e−2)(m + 1 − 2d) − d(d−1) ) / 2.

*Proof.* By (A′), m·W ≥ m·Σ_t μ(t)δ(t) − (k−1)m(m−1)/2, because Σ_t μ(t)D̄(t) ≥ 0 and Σ_t D̄(t) = m(m−1)/2. Let U_j = {t ∈ B : δ(t) ≤ j}. Then Σ_t μ(t)δ(t) = Σ_{j≥0} μ({t : δ(t) > j}) = Σ_{j≥0} (km − μ(U_j)), every term is ≥ 0, and by Lemma 3 the j-th term is at least (k−1)(m − |U_j|) − C(|U_j|, 2). Finally |U_j| = D_j: δ(t) ≤ j means a·t + jm ≥ c, i.e. the one integer v of the class of a·t in [c − (j+1)m, c − jm) satisfies v < a·t, i.e. v ∉ S. ∎

**Corollary G1.** Wilf's inequality holds whenever d(d−1) ≤ (e−2)(m + 1 − 2d). This is the case if d ≤ e − 1 and m ≥ 3e − 4. Since Eliahou proved Wilf for 3e ≥ m, it follows that **every numerical semigroup with at most e − 1 gaps in [c − m, c) satisfies Wilf's conjecture**. Every gap h ≥ c − m is pseudo-Frobenius, so d ≤ t, and the hypothesis d ≤ e − 1 is weaker than the classical t ≤ e − 1.

For fixed e the first condition allows d up to about √((e−2)m). The explicit ray S_q of §4 has d = 1 and type 9. The bound of Theorem C is at least the one-window bound of Theorem G (insert Lemma 3 for U = T into Theorem C), so Conjecture C is a theorem whenever d(d−1) ≤ (e−2)(m + 1 − 2d). Using (C1) with Lemma 3 instead of the proof above improves the one-window bound slightly, to W ≥ ((e−2)(m + 1 − 2d) − d(d−1)(1 − e/m))/2. Theorem G also holds with any minimal generator n in place of m (windows of length n): §§2–3 and Lemma 3 never use that m is the least generator. On the 93 141 semigroups of genus ≤ 20 this certifies only 6 more (`census_extras.py`).

The proof of Theorem G uses neither the residues nor the positions in the window. What it leaves is the range d ≳ √((e−2)m), where many cells have two or more of their chain tops in the last window; there one needs Theorem C itself, i.e. the positions.

## 6. Reflection in boxes (Hellus–Rechenauer–Waldi) and where matchings stop

For an interval [u, v] ⊂ B, y ↦ u + v − y is a bijection and D(u + v − y) = D(v) + a·(y − u). So Σ_{[u,v]} δ(y) = Σ_{[u,v]} ⌊(D(v) + a·(y − u))/m⌋ ≥ Σ_{[u,v]} ⌊a·(y − u)/m⌋.

- u = 0, v a maximal cell: summing over the maximal cells gives g ≤ t_B·n, t_B = number of maximal cells of B. This is Proposition 3.2 of Hellus–Rechenauer–Waldi, the down-set form of the Fröberg–Gottlieb–Häggkvist bound g ≤ t·n. It gives Wilf when t_B ≤ k and needs no residue condition.
- One-dimensional intervals (chains): Theorem B. It pays ⌊x_i a_i/m⌋ per direction and loses exactly the carries.

**Why no gap-to-left-element matching goes further than FGH.** Suppose φ maps gaps to L = S ∩ [0, c) with h + φ(h) ∉ S (the FGH relation). Every pseudo-Frobenius f has f + s ∈ S for all s ∈ S∖{0}, so φ(f) = 0: the fibre over 0 has at least t elements. Such a map proves g ≤ κ·n only for κ ≥ t. Chain reversal is a different relation (a gap in the class of x is paired with left elements in the class of the reflection of x), which is why it reaches semigroups of large type.

## 7. Natural lemmas that fail (exact examples)

1. *Direction by direction.* Σ_x D(top_i(x)) ≥ ((k−1)/k)·m(m−1)/2 for each i is false. ⟨3, 4, 5⟩, B = {0, e_1, e_2}, M = 5, D = (5, 1, 0): direction 2 gives 0 + 1 + 0 = 1 < 3/2. (Total 3 = (k−1)·3, W = 0.)
2. *Cell by cell.* carry(x) ≤ Σ_i (δ(top_i(x)) + ε_i(x)) is false. ⟨4, 6, 7⟩, Ap = {0, 13, 6, 7}, B = {0, e_1, e_2, e_1+e_2}: at x = e_1 + e_2 the carry is 3 − 1 − 1 = 1 and x is its own top in both directions with D = 0. (W = 5.) The maximal element never pays for its own carries.
3. *Shape alone.* The right side of C+ with T = all maximal cells is negative for the triangle {x ∈ ℕ² : x_1 + x_2 ≤ 2}: m = 6, μ = (4,4,4,0,0,0), N = 12 = km, R = 12, value 0 + 12 − 15 = −3. This triangle is not a lattice tile (Lemma S).
4. *Weights without distinct residues.* On the same triangle with a = (9, 10), m = 6 (the example closing Hellus–Rechenauer–Waldi, γ = (3/2, 5/3)): Σ⌊a·x/6⌋ = 11, Σ⌊(20 − a·x)/6⌋ = 5, and 2·5 < 11. The residues are 0,3,4,0,1,2: a collision of residues (0 and 2e_1), not an equality of weights. So a down-set with weights above m can violate the Wilf-type inequality; every such example I know has a residue collision.

Ties versus collisions at the boundary. If t + e_i ∉ B because a·t + a_i equals another Apéry element (equal weights, a tie), then D(t) ≥ a_i > m and that top contributes δ ≥ 1. Only genuine residue collisions with a weight drop (a·t + a_i − m ∈ S) let a top sit in the last window. The cells of T have collisions in all k directions.

## 8. Realizability

**Lemma S (difference packing).** Let P, Q ⊂ ℕ^k with P + Q ⊆ B. Then the differences x − y (x ∈ P, y ∈ Q) are pairwise incongruent modulo the lattice Λ = {z : a·z ≡ 0 mod m}, so |P − Q| ≤ m. Consequently, for k ≥ 2 and L ≥ 2 the simplex Δ_L = {x ∈ ℕ^k : |x| ≤ L} is not the Apéry down-set of any numerical semigroup, and more precisely

    Δ_h ⊆ B  ⟹  m ≥ N(k; ⌈h/2⌉, ⌊h/2⌋),   N(k; p, n) = Σ_{j=0}^{k} C(k,j)·C(n,j)·C(p+k−j, k−j) > C(p+n+k, k) = |Δ_{p+n}|   (k ≥ 2, p, n ≥ 1).

*Proof.* If x − y ≡ x′ − y′ then x + y′ ≡ x′ + y, both in B, so x + y′ = x′ + y. For P = Δ_p, Q = Δ_n: P + Q = Δ_{p+n} and P − Q = {z ∈ ℤ^k : |z⁺| ≤ p, |z⁻| ≤ n}. Counting by the j coordinates that are negative gives N(k; p, n). By Vandermonde, C(p+n+k, k) = Σ_j C(n,j)·C(p+k, k−j). The ratio of the j-th terms is ρ_j = C(k,j)·C(p+k−j, k−j)/C(p+k, k−j) = Π_{i=1}^{j} f_i with f_i = (k−i+1)(p+i)/(i(p+k−i+1)). Here f_i − 1 has the sign of p(k+1−2i) and f_i·f_{k+1−i} = 1, so ρ_j = ρ_{k−j} ≥ 1 for all j, and ρ_1 = k(p+1)/(p+k) > 1. The j = 1 term is present because n ≥ 1. ∎

The same argument works for any lattice tile, with any quotient group. For k = 4: a tile containing Δ_2, Δ_3, Δ_4, Δ_5 has m ≥ 21, 55, 131, 255, while |Δ_h| = 15, 35, 70, 126. In particular no down-set tile lies between Δ_4 and Δ_5, and none between Δ_{L−1} and Δ_L for any L ≥ 5 (k = 4): for h = L − 1 from 4 to 14 by evaluating N, and for h ≥ 15 because the j = 2 term alone, 6·C(⌊h/2⌋, 2)·C(⌈h/2⌉ + 2, 2), exceeds C(h+5, 4). (`simplex_tile.py` re-checks three small cases by brute force.)

Consequence. For unit weights the slack in Lemma 2 is σ(B) = Σ_{x,i} (L − |top_i(x)|), L the largest length in B, and σ(B) = 0 iff B = Δ_L. (If every chain top has length L, then walking from 0 along the support of any x with |x| = L stays in B.) So for k ≥ 2 every lattice-tile down-set other than Δ_0, Δ_1 has σ ≥ 1; in B2 this is why W grows linearly along a ray.

**Tiles without minimality.** A weighted tile is (B, a): B a down-set of size m, a ∈ ℤ^k, a·x mod m bijective on B (so B tiles ℤ^k by a lattice with cyclic quotient). Theorems A, B, C, C+ hold for weighted tiles with all a_i > m, with c and g replaced by max_B a·x − m + 1 and Σ_B ⌊a·x/m⌋. Hellus–Rechenauer–Waldi ask whether k·Σ_B ⌊(max − a·x)/m⌋ ≥ Σ_B ⌊a·x/m⌋ holds whenever B tiles ℤ^k by a lattice and all a_i ≥ m. Exhaustive tests over tiles with cyclic quotient, exact arithmetic (`pseudo_tiles.py`, `hrw_question.py`), all with zero violations:

- k = 2, m = 3..14 and k = 3, m = 4..11, a_i = q_i m + r_i with q_i ∈ {1, 2}: 3 194 + 35 715 tiles whose weights are Apéry-minimal and 8 118 + 251 037 that are not. The least value among non-minimal tiles is larger than among minimal ones for every m.
- Tiles with more than k maximal cells (the others are covered by §6), q_i allowed down to 0: k = 3, m = 8..11, q ≤ 4: 261 000; k = 3, m = 12..14, q ≤ 3: 547 584; k = 4, m = 8..10, q ≤ 2: 944 784.
- Weights not tied to the tiling lattice, a ∈ [m, 3m]^3, k = 3, m = 8..12, tiles with more than 3 maximal cells: 468 tiles, 25 344 compatible and 5 871 306 incompatible weight vectors. For k = 4, a ∈ [m, 2m]^4, m = 8, 9: 90 tiles, 5 616 compatible and 873 750 incompatible weight vectors.

So in these ranges weight-minimality is not what makes the inequality true; the tiling is. This is evidence about an open question, not a theorem.

**Conjecture Φ.** For a down-set B put N_max = Σ over maximal cells of μ, and Φ(B) = m(km − N_max) + R(B) − (k−1)m(m−1)/2. Since T ⊂ maximal cells, C+ gives m·W ≥ Φ(B). Conjecture: Φ(B) ≥ 0 for every Apéry normal-form down-set (`deglex`). This is a statement about the shape of a lattice tile with no weights in it, and it implies Wilf. It is an equality on both known equality families and fails for non-tiles (§7.3). Evidence: §9 (every scanned semigroup); the 16 down-sets with Φ < 0 of size ≤ 16 (k = 2) or ≤ 12 (k = 3) admit no bijective residue vector; and the graded tiles of ℤ/m for all generator triples with m ≤ 70 (854 694 tiles) and quadruples with m ≤ 34 (271 580 tiles) have Φ > 0 (`shape_tiles.py`). Heuristic limit: a tile sandwiched between Δ_{L−1} and Δ_L with L large would have Φ < 0, so the conjecture needs such near-perfect tiles not to exist. Lemma S shows they do not exist for L ≥ 5 when k = 4; it says nothing yet about tiles that are close to a weighted simplex with unequal weights.

## 9. Bounded computations

All exact integer arithmetic. Counts are of semigroups with embedding dimension exactly 5 (redundant lists are discarded). "type ≥ 5" means the FGH criterion does not apply. "G holds" means d(d−1) ≤ 3(m+1−2d), the one-window condition of Corollary G1 for e = 5. "C < 0" counts semigroups where the bound of Theorem C is negative (a failure of Conjecture C); "C+ < 0" and "Φ < 0" likewise for Theorem C+ and Conjecture Φ. Minimal lengths (`deglex`) throughout.

| Exhaustive scan (`scan_criteria.c`) | semigroups | type ≥ 5 | G holds | G holds, type ≥ 5 | C < 0 | C+ < 0 | Φ < 0 | least W | least Theorem C bound |
|---|---|---|---|---|---|---|---|---|---|
| m = 6..19, every 4-subset of (m, 4m] without multiples of m, any conductor | 715 736 | 297 147 | 700 991 | 283 249 | 0 | 0 | 0 | 3 at [6, 7, 15, 16, 17] | 0.50 at [6, 11, 19, 20, 21] |
| m = 20..26, every 4-subset of (m, 5m] without multiples of m, c > 4m | 10 814 803 | 6 025 009 | 10 787 079 | 5 997 285 | 0 | 0 | 0 | 37 at [25, 36, 42, 43, 44] | 5.76 at [25, 51, 54, 57, 58] |
| m = 20..80, every 4-subset of (m, 2m), c > 4m | 23 293 614 | 18 291 278 | 23 243 588 | 18 241 252 | 0 | 0 | 0 | 37 at [25, 36, 42, 43, 44] | 10.68 at [22, 31, 40, 41, 43] |
| m = 20..70, every 4-subset of (12m, 13m) (stabilized rays), c > 4m | 11 731 460 | 9 860 132 | 11 715 018 | 9 843 690 | 0 | 0 | 0 | 240 at [25, 301, 304, 307, 308] | 5.76 at [25, 301, 304, 307, 308] |

The third scan for m ≤ 26 (47 766 semigroups) is contained in the second. The first three scans cover 34 776 387 distinct semigroups, 24 592 298 of type ≥ 5. On every one of them the bound of Theorem C is positive, so Theorem C alone certifies W ≥ 0; the closed formula of Corollary G1 certifies 34 685 075 of them (24 501 833 of type ≥ 5). No negative Wilf number occurs. A seeded pseudo-random sample (m = 100..130, 50 000 lists per m with a_i ∈ (m, 3m), c > 4m: 1 393 214 lists with e = 5, 1 234 743 of type ≥ 5) shows the same: G holds for all but 26, C, C+ and Φ are never negative, and the least W is 3.97m. It is a sample, not a scan, and random lists are far from extremal.

The fourth scan is aimed at Conjecture C. Along a ray ⟨m, qm + b_1, …, qm + b_4⟩ the Apéry down-set and the top window stop changing once q exceeds the longest factorization, so the bound of Theorem C is constant in q while W grows linearly; the bound is therefore smallest relative to W there. Its least value per multiplicity has local minima 5.76 at m = 25, 14.05 at m = 41 and 26.23 at m = 61, and does not approach 0 in this range. These three belong to one family, m = 2s² − 2s + 1 with residues (1, s, 2s − 1, 2s): for s = 3..12 (m up to 265, computed with `apery_downset.py`, not proved in general) it satisfies (G) with L = s − 1, ρ = 0, d = 4(s − 1), σ = (2/3)(s − 2)(s − 1)(2s − 3), so W = qσ, and the Theorem C bound grows from 1.23 (s = 3, the semigroup [13, 14, 16, 18, 19] at q = 1) to 182.6 (s = 12). The least Wilf numbers at m = 13 in the first scan and at m = 61 in the third are attained by its members with q = 1 ([13, 14, 16, 18, 19] and [61, 62, 67, 72, 73]).

**Other embedding dimensions (an attempt to break Conjecture C).** `scan_general.c` evaluates Theorem C for any number of generators; it reproduces the five-generator scanner exactly on rays (m = 20..24). Every k-subset b of [1, m − 1] was taken as the residues of a ray ⟨m, Qm + b_1, …, Qm + b_k⟩, with Q = 40 (stabilized) and for some k also Q = 1:

| e | multiplicities | Q | semigroups | G1 holds | Theorem C bound < 0 | W < 0 |
|---|---|---|---|---|---|---|
| 3 | 3..200 | 40 | 1 098 601 | 1 098 600 | 0 | 0 |
| 4 | 4..120 | 40 | 7 627 637 | 7 626 797 | 0 | 0 |
| 4 | 4..120 | 1 | 7 627 637 | 7 626 167 | 0 | 0 |
| 6 | 6..40 | 40 | 3 797 877 | 3 741 793 | 0 | 0 |
| 6 | 6..40 | 1 | 3 797 877 | 3 624 457 | 0 | 0 |
| 7 | 7..32 | 40 | 3 354 296 | 3 119 653 | 0 | 0 |
| 8 | 8..28 | 40 | 3 105 093 | 3 025 391 | 0 | 0 |
| 9 | 9..25 | 40 | 2 042 755 | 1 536 497 | 0 | 0 |

That is 32 451 773 further semigroups. In every file the bound of Theorem C reaches 0 only on the equality family m = e. Conjecture C survives; these are rays only, and bounded in m.

These scans are bounded and say nothing beyond their ranges. With c > 4m and generators in (m, 2m) the least Wilf number for each m lies between 1.48m and 2.64m, always at depth 5 or 6, and the minimizers have Apéry down-sets that are truncated simplices, e.g. [25, 36, 42, 43, 44]: W = 37, 25 of the 35 cells of Δ_3, twelve maximal cells all ≥ c (so d = 12, where Corollary G1 needs d ≤ 6), Theorem C bound 15.56, Theorem C+ bound 8.24. The least value of Φ/m² per multiplicity is 0.33 at m = 25 and between 0.41 and 0.86 for the other m in 20..80.

At m = 20 in the second box (`coverage_exhaustive.py`): 737 442 semigroups, 334 408 of type ≥ 5. Corollary G1 holds for 731 325 (328 291 of type ≥ 5); 55 503 are carry-free under one of the four orders (24 758 of type ≥ 5); 5 703 satisfy neither; Theorem C certifies all 737 442.

Other checks:

- Lemma 2, Lemma 3, Theorems A, B, G and the bounds C, C+ are asserted inside `apery_downset.stats` on every call; `scan_criteria.c` asserts Theorem A and the bounds of Theorems C, C+ and G (one window) on every semigroup it counts. The invariants (m, e, c, g, n, W) agree with `../wilf.py` on 17 589 random semigroups with e from 2 to 7 under two tie-breaks (`test_claude.py`).
- Repository baseline family (`baseline_family.py` reproduces its counts: 54 099 lists, 41 799 beyond its filters): Theorem C certifies all 41 799; the closed formula of Corollary G1 certifies 41 796 of them; 26 717 have type ≥ 5 (26 714 of these satisfy G1); 14 010 are carry-free under one of the four orders (10 134 of type ≥ 5). The control [23, 47, 51, 78, 80] has type 10, no carries, and W = 86 + 9 − 0 = 95 by Theorem B.
- `tree_check.py`, independent of everything else here: on all 1 179 596 numerical semigroups of genus ≤ 25 (any e; the per-genus counts 1, 2, 4, 7, 12, 23, …, 467 224 match the known sequence), with every quantity computed from the definitions, the bounds of Theorems C and G hold, **the bound of Theorem C is ≥ 0 for every one**, and Theorem G certifies W ≥ 0 for 798 606 with one window and 802 402 with all windows. 1 145 086 of them have at most e − 1 gaps in [c − m, c).
- `check_independent.py`: direct membership DP and an independent certificate checker agree with `../wilf.py verify` and with `apery_downset.py` on the control (m, e, c, g, n, W) = (23, 5, 170, 117, 53, 95) and on 18 further semigroups.

## 10. Prior work and the scope of the exclusion filters

Accessed 2026-11-27 through fetch agents (arXiv HTML) and the PDF text they saved; what was read is stated per item. Statements below are from the parts read.

- Zhai, arXiv:1111.2779 (HTML read via a fetch agent): lex-minimal Apéry factorizations form a down-set; Lemma 3 is the generic inequality, proved by the same chain reversal; Theorem 1 is W ≥ −(e−2)(m−1)/2; "weaker than the Wilf conjecture".
- Hellus–Rechenauer–Waldi, arXiv:1804.06141 (PDF text; §1, §2.5–2.6 and §3 read directly): formula (10) is the target identity; Prop. 3.2 is the box bound of §6; Cor. 3.3 settles k = 2 tiles; the example of §7.4 and the tile question of §8 are theirs.
- Eliahou, arXiv:1909.03699 (PDF text, §§1–2 read): 3e ≥ m; W = |P|τ(X) − |X∩D|q + ρ; "downset" there means closed under summands in S, a different structure from B.
- Delgado–Eliahou–Fromentin, arXiv:2310.07742 (HTML read in full by a fetch agent): g ≤ 100; g ≤ 120 only when m divides c. Their list of known cases has m ≤ 19 (Kliem–Stump), so the m ≤ 18 filter is conservative, and it has e ≤ 3 and c ≤ 3m only.
- Bruns–García-Sánchez–O'Neill–Wilburne, arXiv:1903.04342 (abstract and §§1–4 start read by a fetch agent): m ≤ 18; uses e > t ⟹ Wilf.
- conjectures.io source23 (c ≤ 4m): page says "Approved 12 Oct 2026", Lean verification "Passed"; the Lean source and review were not read, and the page cites arXiv:1703.01761, which is the c ≤ 3m paper. source22 (e = 4): "Solved elsewhere", "Withdrawn"; no citation for the prior proof on the page, and none of the papers above lists e = 4 as known. Both are treated as reported, not verified.
- Dhayni, arXiv:1610.08726 (HTML §§1–4 read by a fetch agent): sufficient conditions of the form w_{m−1} ≥ w_1 + w_α with (2 + (α−3)/q)e ≥ m, m − e ≤ 5, (2 + 1/q)e ≥ m; the index α is free and no condition counts Apéry elements above the conductor.
- Marashdeh, arXiv:2608.12531 (first third read): W = (e − t − 1)n + σ + Θ; no theorem with hypothesis t ≥ e other than a reduction to a conjecture.
- Filters missing from the README list that matter for a hunt: type t ≤ e − 1 (FGH); n ≤ 12 (Eliahou–Marín-Aragón); m | c with 4e ≥ m (Eliahou, cited by Delgado–Eliahou–Fromentin and by Marashdeh); almost symmetric semigroups. By G1, add: d(d−1) ≤ (e−2)(m+1−2d) with d the number of gaps in [c − m, c); in particular d ≤ e − 1. By C, add: Σ_{w∈Ap, w≥c} (ℓ(w) + e − 1)(w − c + 1) ≤ m(em + e − 2)/2, which no semigroup in §9 violates.

Novelty. Lemma 1, Lemma 2 as an inequality, the target identity and the box bound are known. I did not find Theorem A as an equality, Theorems B, C, C+, G, Corollaries B2, G1 or Lemma 3 in the sources above or in seven targeted web searches; that is a negative search, not a proof of novelty. They are short consequences of Zhai's reversal once the top is kept. Lemma S is a standard packing argument (the difference set of a set that embeds in a group must embed too); I did not look for its first appearance.

## 11. Attempt log

1. *Generic down-set inequality as a route to Wilf.* True (Zhai), sharp, residue-blind; short by (k−1)m(m−1)/2. Dead as stated.
2. *Bound each direction separately.* False (§7.1).
3. *Pay for each cell's carries at that cell.* False (§7.2).
4. *Gap ↦ left element with h + s ∉ S.* Cannot beat the type (§6).
5. *k interval partitions with one covering box per partition.* Recovers FGH for B only, since each maximal cell needs its own box.
6. *Distinct residues of the chain tops alone (rearrangement over T).* Not enough for shapes near a simplex (§7.3); gives C+ and (C1), (C2) when combined with δ ≥ 1 off T.
7. *Generators just below multiples of m, a_i = Q_i m − b_i.* If Σ b_i x_i ≤ m − 1 on B then W = Σ_{x,i} (Q* − Σ_j Q_j top_i(x)_j) + (m − 1) − kβ*, with Q* = max_B Σ Q_j x_j and β* the least Σ b_j t_j among cells attaining Q* (checked on 411 random semigroups in `test_claude.py`). Carries are maximal here, and I could not prove non-negativity from this formula.
8. *Drop minimality and look for a negative weighted tile.* None found (§8).
9. *Hill-climbing on residue quadruples for a tile with Φ < 0, m up to 210.* Uninformative: it finds values far above the exhaustive minima.
10. *Scan a_i = 2m − b_i separately.* It is the same family as a_i = m + b_i; removed.
11. *One box per heavy top plus chains elsewhere (FGH inside chain reversal), aiming at "d ≤ e − 1 ⟹ Wilf".* The cells directly above a box in the direction assigned to it lose an unbounded amount, so the interval partitions do not close. The counting Lemma 3 gives the result instead, for m ≥ 3e − 4.
12. *Sharper constant for few gaps.* On all 90 515 semigroups of genus ≤ 20 with d ≤ e − 1, W ≥ (e − 1 − d)·m (`census_extras.py`; the least values are (e−1−d)·e, attained at m = e). Theorem G gives about half of that for d = 1 and I have no proof of the sharper form.
13. *A bound that needs no tile.* Since D(top_i(x)) ≥ D(x) mod a_i, Theorem A gives m·W ≥ Σ_{w∈Ap} Σ_{i≥1} ((F + m − w) mod a_i) − (e−2)m(m−1)/2, in terms of the Apéry set and the generators only. It is an equality on both W = 0 families, but its right side is negative for 178 of the 93 141 semigroups of genus ≤ 20, the smallest being ⟨5, 6, 7⟩ (`census_extras.py`). Chains that stop early (ties) make it lose too much; it cannot replace Theorem C.

## 12. Open points

1. First obstacle: Conjecture C. Equivalently, show that Σ_{t∈T} (|t| + k)(a·t − c + 1) ≤ m((k+1)m + k − 1)/2, i.e. that the Apéry elements of [c, c + m) cannot both carry most of the chain tops and crowd the top of that window. What is proved: the no-wrap case (C3), the case d(d−1) ≤ (e−2)(m + 1 − 2d) (Lemma 3), the bounds (C1), (C2) from distinct positions, and the non-existence of unit-weight near-simplices (Lemma S). What is missing is a weighted version of Lemma S: a quantitative statement that many nearly-equal-weight cells cannot have pairwise distinct residues packed into a short interval.
2. Whether W ≥ (e − 1 − d)·m for d ≤ e − 1 (attempt 12).
3. Conjecture Φ (the weight-free variant) and the Hellus–Rechenauer–Waldi tile question, with the data of §8.
4. Whether Theorems A–G are in the literature in another form.
5. No Lean formalization was attempted: no Lean toolchain is installed in this container.

## 13. Reproduce

From `math/wilf-conjecture/claude/` (Python 3.10+ standard library; gcc for the scanner):

```sh
python3 -B -m unittest -v test_claude               # random comparison with ../wilf.py, the examples of §7, the ray, the equality families
python3 -B tree_check.py 25                          # Theorems C and G on every semigroup of genus <= 25, from the definitions (about 3 minutes)
python3 -B census_extras.py 20                       # attempt 12 and Theorem G with other bases, genus <= 20
python3 -B apery_downset.py 23 47 51 78 80          # invariants and every term of Theorems A, B, C+
python3 -B check_independent.py                      # two independent checkers vs ../wilf.py
python3 -B uniform_rays.py check 22 5 6 7 8          # Corollary B2 on the explicit ray, q = 1..8
python3 -B uniform_rays.py scan 20 30
python3 -B nowrap_check.py                           # Proposition C3 on random no-wrap semigroups
python3 -B simplex_tile.py                           # Lemma S, brute-force re-check of three small cases
python3 -B pseudo_tiles.py classify 3 4 11 2         # tiles with and without Apéry minimality
python3 -B pseudo_tiles.py extended 4 8 10 0 2
python3 -B hrw_question.py 3 8 12 3
python3 -B shape_tiles.py exhaustive 3 4 12 ; python3 -B shape_tiles.py graded 4 8 34
python3 -B baseline_family.py                        # the repository family through Theorems B, C, C+ and Corollary G1
python3 -B coverage_exhaustive.py 20 5
gcc -O2 -o scan_criteria scan_criteria.c
./scan_criteria box 6 19 4 0 ; ./scan_criteria box 20 26 5 4 ; ./scan_criteria pos 20 80 1 4
./scan_criteria pos 20 70 12 4                       # stabilized rays
./scan_criteria rnd 100 130 50000 4                  # seeded sample, not exhaustive
gcc -O2 -o scan_general scan_general.c
./scan_general ray 3 4 120 40 ; ./scan_general ray 6 7 32 40    # Theorem C for other embedding dimensions (see results/COMMANDS.txt)
```

Outputs are in `results/`; `results/COMMANDS.txt` maps each file to the command that wrote it. Nothing was submitted or posted anywhere.
