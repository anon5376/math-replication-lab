# Math Replication Lab

## 001 · Caiolo–Ferroni–Hoster, Conjecture 7.3

**Status: exact arithmetic reproduced for one witness.** This is not a new disproof, a Lean replay, or a claim of priority. The matroid construction is credited to [Cinna Davis and GPT-6.2 Astra](https://github.com/1337isnot1337/solved-conjectures/pull/326), adapting [Bérczi, Coron, Eur and Li](https://arxiv.org/html/2610.17135v1). The statement and flag-to-polynomial formula are from [Caiolo, Ferroni and Hoster, Conjecture 7.3 and Theorem 4.9](https://arxiv.org/html/2605.28474v1).

```sh
node --test cfh.test.mjs
```

No packages or floating-point arithmetic. To inspect the numbers:

```sh
node --input-type=module -e 'import {result} from "./cfh.mjs"; console.log(result(17n))'
```

At q=17, the gamma quadratics have discriminants
`-11062769241414341239970603495681493737981374532130995` (dual Chow) and
`-11061733404916469626152098526056073213151599377977031` (dual right augmented).
Both numbers and all six gamma coefficients match the reported witness.

### What was computed

The code counts chains in the product of the subspace lattice and the lattice of subsets of the auxiliary points. It builds each chain from the bottom up: an increment of u dimensions above a chosen p-space in dimension d has a Gaussian-binomial number of choices in the (d-p)-dimensional quotient. An increment in auxiliary points uses an ordinary binomial. For chains ending in rank four, each coalescence adds the new block's lower-chain counts and subtracts those under the old hyperplanes it replaces. Boolean Möbius inversion turns the resulting flag counts into flag h-numbers, and Theorem 4.9 gives the gamma coefficients.

This independently implements the arithmetic from the published construction's structural counts. It does not materialize the enormous ground set, certify matroid axioms by machine, recheck the full range q ≥ 17, or reproduce the original Lean build.

### Why one witness suffices

Write the degree-four polynomial as `(1+x)^4 G(x/(1+x)^2)`, with G the quadratic with the reported gamma coefficients. A negative discriminant excludes every real root of G; x=-1 is separately excluded because the top gamma coefficient is nonzero. The degree-five case works the same way after removing its factor 1+x. A single valid matroid therefore suffices to contradict the universal statement.

For every prime power below 17, both gamma quadratics instead have positive coefficients and positive discriminant. Their two zeros are negative. Each negative value of z has two negative preimages under z=x/(1+x)^2 (one in each of (-∞,-1) and (-1,0)), so these smaller parameters do not give a counterexample in this particular family. This is **not** a bound on the smallest matroid across all constructions.

### Next research question (not a result)

Can one find a much smaller rank-five counterexample, with a lattice that can be enumerated and cross-checked directly? Compare against other published constructions before asserting novelty.

For the **ordinary dual Chow polynomial** (not the augmented version), rank five is the first possible rank for a failure. Indeed, the original paper proves gamma-positivity for geometric lattices. For a loopless matroid of rank 1–4, its polynomial has the form `(1+x)^d a` for d=0 or 1, or `(1+x)^(d-2) [a(1+x)^2 + b x]` for d=2 or 3, with a>0 and b≥0. The quadratic has discriminant b(4a+b)≥0, product of roots 1, and negative sum of roots. All roots are therefore real and negative. Loops can be removed without changing the lattice of flats. This is a direct consequence of the original theorem, not a priority claim.
