"""Does Wilf's inequality survive when Apéry minimality is dropped?

A *weighted tile* is (B, m, a): B a finite down-set in N^k, m = |B|, a in Z^k
with every a_i > m, such that x -> a.x mod m is a bijection B -> Z/m.
Its formal Wilf number is
    W'(B, a) = k * (M - m + 1) - (k + 1) * sum_{x in B} floor(a.x / m),   M = max_B a.x.
When B is the set of Apéry normal forms of <m, a_1..a_k> and the a_i are the
minimal generators other than m, W' is the Wilf number of that semigroup.

This script enumerates, for fixed k and m, every down-set of size m in N^k,
every residue vector r in [1, m-1]^k that is bijective on B, and every
quotient vector q in [1, qmax]^k (a_i = q_i m + r_i), and reports the minimum
of W' separately over
  * 'apery'  tiles: {a.x} equals the Apéry set of <m, a> (ties allowed), and
  * 'pseudo' tiles: some a.x is not the least element of its class.
Exact integer arithmetic; exhaustive within the stated bounds.
"""
import itertools
import json
import sys

from apery_downset import apery_table


def downsets(k, m):
    """All down-sets of size m in N^k, as frozensets, by adding one cell at a time."""
    level = {frozenset([(0,) * k])}
    for _ in range(m - 1):
        nxt = set()
        for B in level:
            for x in B:
                for i in range(k):
                    y = x[:i] + (x[i] + 1,) + x[i+1:]
                    if y in B:
                        continue
                    if all(y[j] == 0 or y[:j] + (y[j] - 1,) + y[j+1:] in B for j in range(k)):
                        nxt.add(B | {y})
        level = nxt
    return level


def scan(k, m, qmax):
    best = {"apery": None, "pseudo": None}
    counts = dict(downsets=0, bijective=0, apery=0, pseudo=0, negative_apery=0, negative_pseudo=0)
    for B in downsets(k, m):
        counts["downsets"] += 1
        cells = sorted(B)
        for r in itertools.product(range(1, m), repeat=k):
            res = [sum(ri * xi for ri, xi in zip(r, x)) % m for x in cells]
            if len(set(res)) != m:
                continue
            counts["bijective"] += 1
            for q in itertools.product(range(1, qmax + 1), repeat=k):
                a = tuple(qi * m + ri for qi, ri in zip(q, r))
                wts = [sum(ai * xi for ai, xi in zip(a, x)) for x in cells]
                M = max(wts)
                W = k * (M - m + 1) - (k + 1) * sum(w // m for w in wts)
                true = apery_table(m, a)
                kind = "apery" if all(true[w % m] == w for w in wts) else "pseudo"
                counts[kind] += 1
                if W < 0:
                    counts["negative_" + kind] += 1
                if best[kind] is None or W < best[kind][0]:
                    best[kind] = (W, a, cells)
    out = dict(k=k, m=m, qmax=qmax, counts=counts)
    for kind, b in best.items():
        if b:
            out["min_" + kind] = dict(W=b[0], a=list(b[1]), B=[list(x) for x in b[2]])
    return out


def extended(k, m, qlo, qhi):
    """Tiles with more than k maximal cells only (for at most k maximal cells
    W' >= 0 is Proposition D of NOTE.md); quotients q_i in [qlo, qhi], and
    qlo = 0 allows weights below m.  No Apéry/pseudo classification."""
    best = None
    cnt = neg = 0
    for B in downsets(k, m):
        cells = sorted(B)
        nmax = sum(all(x[:i] + (x[i] + 1,) + x[i+1:] not in B for i in range(k)) for x in cells)
        if nmax <= k:
            continue
        for r in itertools.product(range(1, m), repeat=k):
            res = [sum(ri * xi for ri, xi in zip(r, x)) % m for x in cells]
            if len(set(res)) != m:
                continue
            for q in itertools.product(range(qlo, qhi + 1), repeat=k):
                a = tuple(qi * m + ri for qi, ri in zip(q, r))
                wts = [sum(ai * xi for ai, xi in zip(a, x)) for x in cells]
                W = k * (max(wts) - m + 1) - (k + 1) * sum(w // m for w in wts)
                cnt += 1
                neg += W < 0
                if best is None or W < best[0]:
                    best = (W, a, cells)
    return dict(k=k, m=m, q=[qlo, qhi], tiles_with_more_than_k_maximal_cells=cnt, negative=neg,
                min_W=best[0] if best else None, a=list(best[1]) if best else None,
                B=[list(x) for x in best[2]] if best else None)


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "classify":            # classify k m0 m1 qmax
        k, m0, m1, qmax = map(int, sys.argv[2:6])
        for m in range(m0, m1 + 1):
            print(json.dumps(scan(k, m, qmax)), flush=True)
    elif mode == "extended":          # extended k m0 m1 qlo qhi
        k, m0, m1, qlo, qhi = map(int, sys.argv[2:7])
        for m in range(m0, m1 + 1):
            print(json.dumps(extended(k, m, qlo, qhi)), flush=True)
    else:
        raise SystemExit("usage: pseudo_tiles.py classify k m0 m1 qmax | extended k m0 m1 qlo qhi")
