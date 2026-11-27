"""Apéry normal forms, the down-set they form, and the chain-top identities of NOTE.md.

Standard library only.  Everything is exact integer arithmetic.

Setting: S = <m, a_1, ..., a_k>, m the multiplicity, gcd = 1.  For a residue r
let w[r] be the least element of S congruent to r mod m.  Each w[r] is a
nonnegative combination of a_1..a_k alone.  Among the exponent vectors x in N^k
with a.x = w[r] we take the smallest in a fixed tie-break monomial order
(default: lexicographic with x_1 most significant; 'revlex' compares x_k
first; 'minres' compares sum x_i (a_i mod m) first and then lex; 'deglex'
compares the length sum x_i first and then lex).  All four are total orders
compatible with addition.  The set B of these m vectors is a down-set (Lemma 1 of NOTE.md);
`check_downset` re-verifies that for every instance rather than trusting it.
"""
import heapq
from math import gcd


def apery_table(m, a):
    """Dijkstra on residues mod m with edges +a_i.  Returns the list w."""
    w = [None] * m
    w[0] = 0
    queue = [(0, 0)]
    while queue:
        d, r = heapq.heappop(queue)
        if d != w[r]:
            continue
        for x in a:
            s = (r + x) % m
            if w[s] is None or d + x < w[s]:
                w[s] = d + x
                heapq.heappush(queue, (w[s], s))
    return w


def normal_forms(m, a, tiebreak="lex"):
    """Return (w, nf): nf[r] is the tie-break-least x in N^k with a.x = w[r].

    If x is the least factorization of w[r] and x_i > 0 then x - e_i is the
    least factorization of w[r] - a_i (else a smaller one plus e_i would beat
    x).  So the least factorization is the least of the candidates
    nf[r - a_i] + e_i over all i with w[r - a_i] + a_i = w[r].
    """
    k = len(a)
    w = apery_table(m, a)
    if tiebreak == "lex":
        key = lambda v: v
    elif tiebreak == "revlex":
        key = lambda v: v[::-1]
    elif tiebreak == "minres":        # least sum x_i (a_i mod m) first, then lex
        key = lambda v: (sum(vi * (ai % m) for vi, ai in zip(v, a)), v)
    elif tiebreak == "deglex":        # fewest generators first, then lex
        key = lambda v: (sum(v), v)
    else:
        raise ValueError(tiebreak)
    nf = [None] * m
    nf[0] = (0,) * k
    for r in sorted(range(1, m), key=lambda r: w[r]):
        best = None
        for i, ai in enumerate(a):
            s = (r - ai) % m
            if w[s] + ai == w[r]:
                cand = nf[s][:i] + (nf[s][i] + 1,) + nf[s][i+1:]
                if best is None or key(cand) < key(best):
                    best = cand
        assert best is not None, "Apéry element with no generator predecessor"
        nf[r] = best
    return w, nf


def check_downset(m, a, w, nf):
    B = set(nf)
    assert len(B) == m
    for r, x in enumerate(nf):
        assert sum(ai * xi for ai, xi in zip(a, x)) == w[r] and w[r] % m == r
        for i, xi in enumerate(x):
            if xi:
                assert x[:i] + (xi - 1,) + x[i+1:] in B, (m, a, x)
    return B


def primitives(m, a, w):
    """Minimal generators: m and the Apéry elements that are not a sum of two
    positive Apéry elements."""
    pos = set(w) - {0}
    return [m] + sorted(x for x in pos if not any(x - y in pos for y in pos))


def stats(m, a, tiebreak="lex"):
    """Wilf invariants plus every term of the chain-top identities.

    Requires m < min(a) and gcd(m, *a) = 1; `a` must list exactly the minimal
    generators other than m (checked), so k = e - 1.
    """
    a = tuple(a)
    k = len(a)
    assert gcd(m, *a) == 1 and m < min(a)
    w, nf = normal_forms(m, a, tiebreak)
    B = check_downset(m, a, w, nf)
    prim = primitives(m, a, w)
    assert prim == [m] + sorted(a), ("generator list is not minimal", prim)
    M = max(w)
    c = M - m + 1
    g = sum(v // m for v in w)
    n = c - g
    W = (k + 1) * n - c
    wt = {x: w[r] for r, x in enumerate(nf)}
    D = {x: M - wt[x] for x in B}                 # deficit below the maximum
    delta = {x: D[x] // m for x in B}             # elements of S below c in the class
    assert sum(delta.values()) == n
    assert sorted(d % m for d in D.values()) == list(range(m))

    def top(x, i):
        y = x
        while True:
            z = y[:i] + (y[i] + 1,) + y[i+1:]
            if z not in B:
                return y
            y = z

    sumDtop = sum_delta_top = anti = 0
    mu = dict.fromkeys(B, 0)                      # mu[t] = number of pairs (x, i) with top_i(x) = t
    for x in B:
        for i in range(k):
            t = top(x, i)
            mu[t] += 1
            sumDtop += D[t]
            sum_delta_top += delta[t]
            anti += ((D[t] % m) + (x[i] * a[i]) % m) >= m
    assert sum(mu.values()) == k * m
    # D mod m is a bijection B -> {0..m-1}; pairing large mu with small values bounds sum mu*Dbar below.
    rearr = sum(j * v for j, v in enumerate(sorted(mu.values(), reverse=True)))
    assert sum(mu[t] * (D[t] % m) for t in B) >= rearr
    carries = sum(wt[x] // m - sum((xi * ai) // m for xi, ai in zip(x, a)) for x in B)
    # Lemma 2: (k+1) * sum_B a.x = sum_{x,i} a.top_i(x)
    assert (k + 1) * sum(wt.values()) == sum(M - D[top(x, i)] for x in B for i in range(k))
    # Theorem A: m * W = sum_{x,i} D(top_i x) - (k-1) m (m-1) / 2
    assert 2 * m * W == 2 * sumDtop - (k - 1) * m * (m - 1)
    # Theorem B: W = sum delta(top) + anticarries - carries
    assert W == sum_delta_top + anti - carries
    T = [x for x in B if D[x] < m]                # Apéry elements >= c
    assert all(mu[t] == sum(t) + k for t in T)    # each is maximal in B
    # Corollary C2 (NOTE.md): every normal form has length <= min(m-1, floor(M / min a)).
    lam = min(m - 1, M // min(a))
    assert all(sum(x) <= lam for x in B)
    assert 2 * W >= (k + 1) * m + k - 1 - 2 * len(T) * (lam + k)
    # Theorem C and its refinement C+ (both proved in NOTE.md), checked on every instance:
    assert 2 * m * W >= 2 * m * (k * m - sum(mu[t] for t in T)) - (k - 1) * m * (m - 1) + 2 * rearr
    return dict(m=m, e=k + 1, c=c, g=g, n=n, W=W, q=-(-c // m), rho=(-c) % m,
                sum_delta_top=sum_delta_top, anticarries=anti, carries=carries,
                topwindow=len(T), N0=sum(sum(t) + k for t in T), rearrangement=rearr,
                maximal=sum(all(x[:i] + (x[i] + 1,) + x[i+1:] not in B for i in range(k)) for x in B),
                generators=[m] + list(a))


if __name__ == "__main__":
    import json, sys
    gens = sorted(int(v) for v in sys.argv[1:])
    print(json.dumps(stats(gens[0], gens[1:]), indent=1))
