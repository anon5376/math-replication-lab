# Apéry factorization down-sets and Wilf's conjecture: an exact slack formula and two criteria

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
| C | W ≥ (em+e−2)/2 − Σ_{w∈Ap, w≥c} (ℓ(w)+e−1), ℓ = least factorization length | proved |
| C2 | **Wilf holds if the window [c−m, c) contains at most (e−1)/2 gaps and m ≥ (e−2)²; always if F is its only gap** | proved |
| C+ | m·W ≥ m·(km − N_T) + R(B) − (k−1)·m(m−1)/2, R a rearrangement sum of the shape | proved |
| S | The simplex {x : x_1+…+x_k ≤ L} is not a lattice tile for L ≥ k ≥ 2, nor for (k,L) = (3,2), (4,2), (4,3) | proved (first part), exhaustive computation (three cases) |
| – | Conjecture Φ: the right side of C+ with T replaced by all maximal cells is ≥ 0 for every Apéry down-set | **conjectured**; no counterexample in the scans of §9 |
| – | Wilf-type inequality for weighted down-set *tiles* without Apéry minimality (the closing question of Hellus–Rechenauer–Waldi) | **open**; no counterexample in §8 |

What the criteria reach (exact counts in §9): on all 34 776 387 semigroups with e = 5 in the exhaustive scans, the right side of C+ is non-negative, so Wilf follows from C+ alone on each of them; 24 592 298 of those have type ≥ 5, where the classical criterion t ≤ e − 1 does not apply.

What they do not reach: C+ is a lower bound, not Wilf. Its right side is negative for some down-sets that are not tiles (§7), so a proof along this route must use the tiling arithmetic of the whole Apéry set, not only its shape. That is the first remaining obstacle (§12).

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

## 5. Theorem C: few heavy chain tops

Let T = {t ∈ B : a·t ≥ c} = {t : δ(t) = 0}. Each t ∈ T is a maximal cell of B, because a·(t + e_i) ≥ c + m + 1 > M; hence μ(t) = |t| + k. As integers, T is Ap ∩ [c, c + m) = {h + m : h a gap, h ≥ c − m}. Every gap h ≥ c − m is pseudo-Frobenius (h + s ≥ c for s ∈ S∖{0}), so |T| is both the number of gaps in [c − m, c) and the number of pseudo-Frobenius numbers there. Put N_T = Σ_{t∈T} (|t| + k).

**Theorem C+.** Let μ_0 ≥ μ_1 ≥ … ≥ μ_{m−1} be the decreasing rearrangement of (μ(t))_{t∈B} and R(B) = Σ_j j·μ_j. Then

    m·W ≥ m·(km − N_T) + R(B) − (k−1)·m(m−1)/2.

*Proof.* In (A′), δ(t) ≥ 1 for t ∉ T, and Σ_{t∉T} μ(t) = km − N_T. D̄ is a bijection onto {0, …, m−1}, so Σ_t μ(t)D̄(t) ≥ Σ_j j·μ_j by the rearrangement inequality. ∎

**Theorem C.** Dropping R ≥ 0: W ≥ (em + e − 2)/2 − N_T. With the `deglex` order |nf(w)| is the least factorization length ℓ(w), so

    W ≥ (em + e − 2)/2 − Σ_{w ∈ Ap, w ≥ c} (ℓ(w) + e − 1).

**Corollary C2.** Let t_top ≥ 1 be the number of gaps of S in [c − m, c), a_1 the least generator above m, and λ* = min(m − 1, ⌊(c + m − 1)/a_1⌋). Then W ≥ (em + e − 2)/2 − t_top·(λ* + e − 1). Hence Wilf's inequality holds if

- t_top = 1 (then W ≥ (e−2)(m−1)/2), or
- 2·t_top ≤ e − 1 and m ≥ (e−2)², or
- t_top·(q + e − 1) ≤ (em + e − 2)/2.

*Proof.* For x ∈ B the box [0, x] ⊂ B has Π(x_i + 1) ≥ |x| + 1 cells, so |x| ≤ m − 1; also a_1·|x| ≤ a·x ≤ c + m − 1, and (m+1)|x| ≤ (q+1)m − 1 gives |x| ≤ q. The three cases are arithmetic: (e−1)(m + e − 2) ≤ em + e − 2 iff m ≥ (e−2)². ∎

The type t counts all pseudo-Frobenius numbers; t_top only those in the last window. FGH needs t ≤ e − 1; C2 needs t_top ≤ (e−1)/2 and puts no condition on t. Neither implies the other. S_q above has t = 9, t_top = 1.

Equality: C+ is an equality for e = 2 and for ⟨m, qm+1, …, qm+m−1⟩.

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

**Lemma S.** For L ≥ k ≥ 2 there is no homomorphism φ from ℤ^k to a group of order |Δ_L| that is injective on Δ_L = {x ∈ ℕ^k : |x| ≤ L}.

*Proof.* Suppose φ is bijective on Δ_L. Let |y| = L + 1 with all y_i ≥ 1, and let x ∈ Δ_L with φ(x) = φ(y). If x_i ≥ 1 then φ(x − e_i) = φ(y − e_i) with both in Δ_L, so x = y, impossible. Hence x = 0 and φ(y) = 0. For L ≥ k both (L−k+2, 1, 1, …, 1) and (L−k+1, 2, 1, …, 1) are such y, so φ(e_1 − e_2) = 0, contradicting injectivity on {e_1, e_2}. ∎

For (k, L) = (3,2), (4,2), (4,3) the order 10, 15, 35 is squarefree, so the group is cyclic; `simplex_tile.py` tests all 1000, 50 625 and 1 500 625 residue vectors and finds none injective (controls L = 1 give k! as expected). So for 2 ≤ k ≤ 4 the simplex Δ_L, L ≥ 2, is never an Apéry down-set.

Consequence. For unit weights the slack in Lemma 2 is σ(B) = Σ_{x,i} (L − |top_i(x)|), L the largest length in B, and σ(B) = 0 iff B = Δ_L. (If every chain top has length L, then walking from 0 along the support of any x with |x| = L stays in B.) So for 2 ≤ k ≤ 4 every lattice-tile down-set other than Δ_0, Δ_1 has σ ≥ 1; in B2 this is why W grows linearly along a ray.

**Tiles without minimality.** A weighted tile is (B, a): B a down-set of size m, a ∈ ℤ^k, a·x mod m bijective on B (so B tiles ℤ^k by a lattice with cyclic quotient). Theorems A, B, C, C+ hold for weighted tiles with all a_i > m, with c and g replaced by max_B a·x − m + 1 and Σ_B ⌊a·x/m⌋. Hellus–Rechenauer–Waldi ask whether k·Σ_B ⌊(max − a·x)/m⌋ ≥ Σ_B ⌊a·x/m⌋ holds whenever B tiles ℤ^k by a lattice and all a_i ≥ m. Exhaustive tests over tiles with cyclic quotient, exact arithmetic (`pseudo_tiles.py`, `hrw_question.py`), all with zero violations:

- k = 2, m = 3..14 and k = 3, m = 4..11, a_i = q_i m + r_i with q_i ∈ {1, 2}: 3 194 + 35 715 tiles whose weights are Apéry-minimal and 8 118 + 251 037 that are not. The least value among non-minimal tiles is larger than among minimal ones for every m.
- Tiles with more than k maximal cells (the others are covered by §6), q_i allowed down to 0: k = 3, m = 8..11, q ≤ 4: 261 000; k = 3, m = 12..14, q ≤ 3: 547 584; k = 4, m = 8..10, q ≤ 2: 944 784.
- Weights not tied to the tiling lattice, a ∈ [m, 3m]^3, k = 3, m = 8..12, tiles with more than 3 maximal cells: 468 tiles, 25 344 compatible and 5 871 306 incompatible weight vectors. For k = 4, a ∈ [m, 2m]^4, m = 8, 9: 90 tiles, 5 616 compatible and 873 750 incompatible weight vectors.

So in these ranges weight-minimality is not what makes the inequality true; the tiling is. This is evidence about an open question, not a theorem.

**Conjecture Φ.** For a down-set B put N_max = Σ over maximal cells of μ, and Φ(B) = m(km − N_max) + R(B) − (k−1)m(m−1)/2. Since T ⊂ maximal cells, C+ gives m·W ≥ Φ(B). Conjecture: Φ(B) ≥ 0 for every Apéry normal-form down-set (`deglex`). This is a statement about the shape of a lattice tile with no weights in it, and it implies Wilf. It is an equality on both known equality families and fails for non-tiles (§7.3). Evidence: §9 (every scanned semigroup); the 16 down-sets with Φ < 0 of size ≤ 16 (k = 2) or ≤ 12 (k = 3) admit no bijective residue vector; and the graded tiles of ℤ/m for all generator triples with m ≤ 70 (854 694 tiles) and quadruples with m ≤ 34 (271 580 tiles) have Φ > 0 (`shape_tiles.py`). Heuristic limit: a tile sandwiched between Δ_{L−1} and Δ_L with L large would have Φ < 0, so the conjecture needs such near-perfect tiles not to exist; for k = 2 they do not (tiles are L-shapes), for k ≥ 3 this is a degree–diameter question for Cayley digraphs of ℤ/m that I did not resolve.

## 9. Bounded computations

All exact integer arithmetic. "type ≥ 5" means the FGH criterion does not apply. C, C+ use minimal lengths. P means at most two gaps in [c − m, c), the hypothesis of C2 for e = 5 apart from m ≥ 9. Φ is the conjectured shape bound. Counts are of semigroups with embedding dimension exactly 5 (redundant lists are discarded).

| Exhaustive scan (`scan_criteria.c`) | semigroups | type ≥ 5 | P | P and type ≥ 5 | C fails, type ≥ 5 | C+ fails | Φ < 0 | least W |
|---|---|---|---|---|---|---|---|---|
| m = 6..19, every 4-subset of (m, 4m] without multiples of m, any conductor | 715 736 | 297 147 | 439 479 | 127 531 | 2 256 | 0 | 0 | 3 at [6, 7, 15, 16, 17] |
| m = 20..26, every 4-subset of (m, 5m] without multiples of m, c > 4m | 10 814 803 | 6 025 009 | 7 589 044 | 3 641 876 | 2 192 | 0 | 0 | 37 at [25, 36, 42, 43, 44] |
| m = 20..80, every 4-subset of (m, 2m), c > 4m | 23 293 614 | 18 291 278 | 7 740 376 | 4 433 630 | 412 | 0 | 0 | 37 at [25, 36, 42, 43, 44] |

The third scan for m ≤ 26 (47 766 semigroups) is contained in the second. In total 34 776 387 distinct semigroups with e = 5, of which 24 592 298 have type ≥ 5; Theorem C+ certifies W ≥ 0 for every one of them, and Φ ≥ 0 on every one. No negative Wilf number occurs. A seeded pseudo-random sample (m = 100..130, 50 000 lists per m with a_i ∈ (m, 3m), c > 4m: 1 393 214 lists with e = 5, 1 234 743 of type ≥ 5) shows the same: C, C+ and Φ never fail and the least W is 3.97m. It is a sample, not a scan, and random lists are far from extremal.

At m = 20 in the second box (`coverage_exhaustive.py`, `hard_core.py`): 737 442 semigroups, 334 408 of type ≥ 5; 55 503 are carry-free under one of the four orders (24 758 of type ≥ 5); 72 are covered by none of FGH, B, C. Those 72 are listed in `results/hard_core_m20_K5.json` (depth 5 to 14, genus 55 to 188, W from 38 to 148), and C+ covers all of them.

These scans are bounded and say nothing beyond their ranges. With c > 4m the least Wilf number for each m lies between 1.48m and 2.64m, always at depth 5 or 6, and the minimizers have Apéry down-sets that are truncated simplices, e.g. [25, 36, 42, 43, 44]: W = 37, 25 of the 35 cells of Δ_3, twelve maximal cells all ≥ c, C+ bound 8.24. The least value of Φ/m² per multiplicity is 0.33 at m = 25 and between 0.41 and 0.86 for the other m in 20..80; it does not decay in this range.

Other checks:

- Lemma 2, Theorems A and B and the bounds C, C+, C2 are asserted inside `apery_downset.stats` on every call; `scan_criteria.c` asserts Theorem A, the bound C+ and Corollary C2 on every semigroup it counts. The invariants (m, e, c, g, n, W) agree with `../wilf.py` on 17 589 random semigroups with e from 2 to 7 under two tie-breaks (`test_claude.py`).
- Repository baseline family (`baseline_family.py` reproduces its counts: 54 099 lists, 41 799 beyond its filters): all 41 799 satisfy the hypothesis of Theorem C; 26 717 of them have type ≥ 5; 14 010 are carry-free under one of the four orders (10 134 of type ≥ 5). The control [23, 47, 51, 78, 80] has type 10, no carries, and W = 86 + 9 − 0 = 95 by Theorem B.
- `tree_check.py`, independent of everything else here: on all 258 581 numerical semigroups of genus ≤ 22 (any e; the per-genus counts 1, 2, 4, 7, 12, 23, …, 103 246 match the known sequence), the bounds of Theorem C and Corollary C2 hold, with every quantity computed from the definitions. The hypothesis of C2 (first two cases) holds for 15 485 of them.
- `check_independent.py`: direct membership DP and an independent certificate checker agree with `../wilf.py verify` and with `apery_downset.py` on the control (m, e, c, g, n, W) = (23, 5, 170, 117, 53, 95) and on 18 further semigroups.

## 10. Prior work and the scope of the exclusion filters

Accessed 2026-11-27 through fetch agents (arXiv HTML) and the PDF text they saved; what was read is stated per item. Statements below are from the parts read.

- Zhai, arXiv:1111.2779 (HTML read via a fetch agent): lex-minimal Apéry factorizations form a down-set; Lemma 3 is the generic inequality, proved by the same chain reversal; Theorem 1 is W ≥ −(e−2)(m−1)/2; "weaker than the Wilf conjecture".
- Hellus–Rechenauer–Waldi, arXiv:1804.06141 (PDF text; §1, §2.5–2.6 and §3 read directly): formula (10) is the target identity; Prop. 3.2 is the box bound of §6; Cor. 3.3 settles k = 2 tiles; the example of §7.4 and the tile question of §8 are theirs.
- Eliahou, arXiv:1909.03699 (PDF text, §§1–2 read): 3e ≥ m; W = |P|τ(X) − |X∩D|q + ρ; "downset" there means closed under summands in S, a different structure from B.
- Delgado–Eliahou–Fromentin, arXiv:2310.07742 (HTML read in full by a fetch agent): g ≤ 100; g ≤ 120 only when m divides c. Their list of known cases has m ≤ 19 (Kliem–Stump), so the m ≤ 18 filter is conservative, and it has e ≤ 3 and c ≤ 3m only.
- Bruns–García-Sánchez–O'Neill–Wilburne, arXiv:1903.04342 (abstract and §§1–4 start read by a fetch agent): m ≤ 18; uses e > t ⟹ Wilf.
- conjectures.io source23 (c ≤ 4m): page says "Approved 12 Oct 2026", Lean verification "Passed"; the Lean source and review were not read, and the page cites arXiv:1703.01761, which is the c ≤ 3m paper. source22 (e = 4): "Solved elsewhere", "Withdrawn"; no citation for the prior proof on the page, and none of the papers above lists e = 4 as known. Both are treated as reported, not verified.
- Marashdeh, arXiv:2608.12531 (first third read): W = (e − t − 1)n + σ + Θ; no theorem with hypothesis t ≥ e other than a reduction to a conjecture.
- Filters missing from the README list that matter for a hunt: type t ≤ e − 1 (FGH); n ≤ 12 (Eliahou–Marín-Aragón); m | c with 4e ≥ m (Eliahou, cited by Delgado–Eliahou–Fromentin and by Marashdeh); almost symmetric semigroups. By C2, add: at most (e−1)/2 gaps in [c − m, c). By C, add: Σ_{w∈Ap, w≥c} (ℓ(w) + e − 1) ≤ (em + e − 2)/2.

Novelty. Lemma 1, Lemma 2 as an inequality, the target identity and the box bound are known. I did not find Theorem A as an equality, Theorems B, C, C+, Corollaries B2, C2 or Lemma S in the sources above or in five targeted web searches; that is a negative search, not a proof of novelty. They are short consequences of Zhai's reversal once the top is kept and the residue bijection is used.

## 11. Attempt log

1. *Generic down-set inequality as a route to Wilf.* True (Zhai), sharp, residue-blind; short by (k−1)m(m−1)/2. Dead as stated.
2. *Bound each direction separately.* False (§7.1).
3. *Pay for each cell's carries at that cell.* False (§7.2).
4. *Gap ↦ left element with h + s ∉ S.* Cannot beat the type (§6).
5. *k interval partitions with one covering box per partition.* Recovers FGH for B only, since each maximal cell needs its own box.
6. *Distinct residues of the chain tops alone (rearrangement over T).* Not enough for shapes near a simplex (§7.3); gives C+ when combined with δ ≥ 1 off T.
7. *Generators just below multiples of m, a_i = Q_i m − b_i.* If Σ b_i x_i ≤ m − 1 on B then W = Σ_{x,i} (Q* − Σ_j Q_j top_i(x)_j) + (m − 1) − kβ*, with Q* = max_B Σ Q_j x_j and β* the least Σ b_j t_j among cells attaining Q* (checked on 411 semigroups). Carries are maximal here, and I could not prove non-negativity from this formula.
8. *Drop minimality and look for a negative weighted tile.* None found (§8).
9. *Hill-climbing on residue quadruples for a tile with Φ < 0, m up to 210.* Uninformative: it finds values far above the exhaustive minima.
10. *Scan a_i = 2m − b_i separately.* It is the same family as a_i = m + b_i; removed.

## 12. Open points

1. First obstacle: prove Σ_t μ(t)D(t) ≥ (k−1)m(m−1)/2 when most of the μ-mass lies on T. C+ handles every semigroup scanned but is false for general shapes; the missing input is a quantitative statement that lattice tiles are far from simplices (Conjecture Φ or a weaker form).
2. The Hellus–Rechenauer–Waldi tile question, now with the data of §8.
3. Lemma S for k ≥ 5 and 2 ≤ L < k (not needed here).
4. Whether Theorems A–C+ are in the literature in another form.
5. No Lean formalization was attempted: no Lean toolchain is installed in this container.

## 13. Reproduce

From `math/wilf-conjecture/claude/` (Python 3.10+ standard library; gcc for the scanner):

```sh
python3 -B -m unittest -v test_claude               # random comparison with ../wilf.py, the examples of §7, the ray, the equality families
python3 -B tree_check.py 22                          # Theorem C and Corollary C2 on every semigroup of genus <= 22, from the definitions
python3 -B apery_downset.py 23 47 51 78 80          # invariants and every term of Theorems A, B, C+
python3 -B check_independent.py                      # two independent checkers vs ../wilf.py
python3 -B uniform_rays.py check 22 5 6 7 8          # Corollary B2 on the explicit ray, q = 1..8
python3 -B uniform_rays.py scan 20 30
python3 -B simplex_tile.py                           # Lemma S, finite part
python3 -B pseudo_tiles.py classify 3 4 11 2         # tiles with and without Apéry minimality
python3 -B pseudo_tiles.py extended 4 8 10 0 2
python3 -B hrw_question.py 3 8 12 3
python3 -B shape_tiles.py exhaustive 3 4 12 ; python3 -B shape_tiles.py graded 4 8 34
python3 -B baseline_family.py                        # the repository family through Theorems B, C, C+
python3 -B coverage_exhaustive.py 20 5 ; python3 -B hard_core.py 20 5
gcc -O2 -o scan_criteria scan_criteria.c
./scan_criteria box 6 19 4 0 ; ./scan_criteria box 20 26 5 4 ; ./scan_criteria pos 20 80 1 4
./scan_criteria rnd 100 130 50000 4                  # seeded sample, not exhaustive
```

Outputs are in `results/`; `results/COMMANDS.txt` maps each file to the command that wrote it. Nothing was submitted or posted anywhere.
