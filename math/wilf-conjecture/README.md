# Wilf's conjecture: find a numerical semigroup with negative Wilf margin

**Status: open research target. No counterexample or general proof.**

Give me a handful of coin values with gcd 1. Every sufficiently large integer is a nonnegative sum of those values. Can the representable integers below that threshold be so sparse that their density is less than one over the number of indispensable coin values? Wilf asked this in 1978. [Exact FrontierMath target and certificate format](https://epoch.ai/frontiermath/open-problems/numerical-semigroups).

For the generated semigroup S:

- **m** is the smallest positive member.
- **e** is the number of minimal generators, not the length of the submitted list.
- **c** is the conductor: the least integer from which every integer belongs to S.
- **g** counts the gaps; **n = c − g** counts members below c, including 0.

Wilf's conjecture is **e · n ≥ c**. The project's decisive target is one exact example with **W = e · n − c < 0**. A new theorem about a genuinely unresolved family is a separate success, not a counterexample.

## Do not spend the search budget on solved territory

- [Delgado, Eliahou and Fromentin](https://arxiv.org/abs/2310.07742) verified all genera through 100, and through 120 when m divides c.
- [Bruns, García-Sánchez, O'Neill and Wilburne](https://arxiv.org/abs/1903.04342) proved the conjecture through multiplicity 18. [Eliahou](https://arxiv.org/abs/1909.03699) proved it when 3e ≥ m.
- The formal-results registry reports an [accepted proof for conductor at most 4m](https://conjectures.io/problems/math30catalog-source23) and records [public proof evidence for embedding dimension four](https://conjectures.io/problems/math30catalog-source22). Treat both as exclusion filters; neither settles the full conjecture.
- [An August 2026 preprint](https://arxiv.org/abs/2608.12531) gives a separate type-based reduction. Read it before claiming novelty for a similar bound.

## Reproduce the baseline

Python 3.10+, standard library only. From this folder:

```sh
python3 -B -m unittest -v
python3 wilf.py inspect 5 7 9
python3 wilf.py inspect 5 7 9 --certificate > /tmp/wilf-example.json
python3 wilf.py verify /tmp/wilf-example.json
python3 wilf.py verify control.json
python3 wilf.py sweep > /tmp/wilf-sweep.json
cmp baseline.json /tmp/wilf-sweep.json
```

The sweep fixes m in 19–55, q in {1,2,3}, and four increasing offsets a,b,c,d in 1–12. It inspects lists [m, qm+a, qm+b, (q+1)m+c, (q+1)m+d] with gcd 1. Of **54,099 lists**, **41,799** passed the stated filters (actual e = 5, 3e < m, conductor above 4m, and beyond the applicable genus cutoff). No negative margins were found. This count is of generator lists, not distinct semigroups. The lowest margin among filtered inputs was **+95**, at [23, 47, 51, 78, 80]. [Exact run data](baseline.json) · [Replayable control](control.json). The test suite also compares the residue method to direct membership enumeration on every gcd-one subset of sizes 1–4 from {1,…,14}.

### Why a certificate is enough

The Apéry entry w[r] is the least member in residue r modulo m. Addition of a generator gives a weighted edge between residues. A descending predecessor chain shows that each claimed w[r] is attainable. Checking the triangle inequality for every generator edge shows that no walk from 0 to r can have smaller total weight. No search assumption is needed after the certificate is supplied.

In residue r, exactly floor(w[r]/m) nonnegative integers are missing. The largest gap is max(w) − m, with the usual value −1 for S = ℕ. Therefore the certificate determines g, c, and n exactly. Every primitive besides m is a nonzero Apéry entry; such an entry is decomposable exactly when it is a sum of two positive Apéry entries. The verifier uses that fact to remove redundant input generators.

## Next attack: solve for the gaps, not the coins

Start with actual embedding dimension five, where this project's baseline has not found anything. Fix m and write w[r] = m x[r] + r. For each pair of residues i,j, closure is the integer inequality

```text
x[(i+j) % m] <= x[i] + x[j] + floor((i+j)/m)
```

Here x[0] = 0 and all other coordinates are positive. A nonzero residue is primitive exactly when no sum of two nonzero residues attains equality at that residue. For a branch fixing the maximal Apéry residue f and the primitive pattern, g is the sum of the coordinates, c = m x[f] + f − m + 1, and W is linear. This is the entry point to the published fixed-multiplicity method, not a new reduction.

1. Reproduce a known small-multiplicity result or at least known feasible and infeasible faces as controls.
2. Target e = 5, m > 18, and conductor above 4m. Try to minimize W by exploring primitive patterns with a sparse first layer rather than raising the maximum generator in a blind sweep. Record ranges and exact constraints.
3. Reconstruct any proposed negative solution as a generator list and verify its Apéry certificate independently. A solver timeout or an infeasible branch is not a theorem.
4. If the hunt fails, pursue a proved inequality for a precisely defined infinite family outside the published cases. Do not treat a wider finite scan as the result.

Only the verifier and bounded baseline are implemented here. Nothing was submitted to Epoch.
