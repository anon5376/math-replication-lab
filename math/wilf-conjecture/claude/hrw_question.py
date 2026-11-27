"""The closing question of Hellus-Rechenauer-Waldi (arXiv:1804.06141), tested on small tiles.

Question (their last paragraph): if a finite down-set B in N^{e-1} tiles
Z^{e-1} by a lattice, is  w(gamma, B) >= 1/(e-1)  for every weight vector gamma
with all gamma_i >= 1, "at least if #B is a common denominator" of the gamma_i?
With gamma = a/m, m = #B, k = e-1 and a in Z^k, a_i >= m, this reads
    k * sum_B floor((max_B a.x - a.x)/m)  >=  sum_B floor(a.x/m).            (*)
The question does not ask the weights to be compatible with the tiling lattice.
This script enumerates every down-set B of size m in N^k with more than k
maximal cells that is a tile for some cyclic residue map, and every integer
weight vector a in [m, A*m]^k, and reports violations of (*) separately for
  compatible   weights (x -> a.x mod m is a bijection on B), and
  incompatible weights.
Exact integers, exhaustive within the stated bounds.
"""
import itertools
import sys

from pseudo_tiles import downsets


def run(k, m, A):
    stats = dict(tiles=0, compatible=0, incompatible=0, bad_compatible=0, bad_incompatible=0)
    first = None
    for B in downsets(k, m):
        cells = sorted(B)
        if sum(all(x[:i] + (x[i] + 1,) + x[i+1:] not in B for i in range(k)) for x in cells) <= k:
            continue
        if not any(len({sum(ri * xi for ri, xi in zip(r, x)) % m for x in cells}) == m
                   for r in itertools.product(range(1, m), repeat=k)):
            continue
        stats["tiles"] += 1
        for a in itertools.product(range(m, A * m + 1), repeat=k):
            wts = [sum(ai * xi for ai, xi in zip(a, x)) for x in cells]
            M = max(wts)
            u = sum((M - w) // m for w in wts)
            d = sum(w // m for w in wts)
            comp = len({w % m for w in wts}) == m
            stats["compatible" if comp else "incompatible"] += 1
            if k * u < d:
                stats["bad_compatible" if comp else "bad_incompatible"] += 1
                if first is None or (u * first[3] < first[2] * d):      # smaller ratio u/d
                    first = (a, cells, u, d, comp)
    return stats, first


if __name__ == "__main__":
    k, m0, m1, A = map(int, sys.argv[1:5])
    for m in range(m0, m1 + 1):
        s, first = run(k, m, A)
        print(f"k={k} m={m} weights in [m,{A}m]^k:", s,
              "worst violation (a, B, u, d, compatible):" if first else "", first if first else "", flush=True)
