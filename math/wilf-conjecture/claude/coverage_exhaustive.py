"""Which e = 5 semigroups are covered by which criterion?  (bounded, exhaustive)

For a multiplicity m this enumerates every 4-subset {a1<a2<a3<a4} of
(m, K*m] with no a_i divisible by m, keeps those for which <m,a1..a4> has
embedding dimension exactly 5 and conductor c > 4m, and classifies each by

  FGH   : type t <= e - 1 = 4           (Fröberg-Gottlieb-Häggkvist; known)
  B     : carry-free normal forms       (Theorem B of NOTE.md; any of the four tie-breaks)
  C     : 2*N0 <= 5m + 3                (Theorem C of NOTE.md with k = 4, minimal lengths)

and reports counts plus the least Wilf number in each cell.  Every identity
and bound of NOTE.md is asserted inside apery_downset.stats on each instance.
"""
import json
import sys
from collections import Counter
from itertools import combinations
from multiprocessing import Pool

from apery_downset import apery_table, primitives, stats


def apery_type(m, w):
    return sum(not any(u > v and (u - v) >= w[(u - v) % m] for u in w) for v in w)


def work(args):
    m, K, a1 = args
    tot = Counter()
    least = {}
    pool = [x for x in range(a1 + 1, K * m + 1) if x % m]
    for rest in combinations(pool, 3):
        a = (a1,) + rest
        w = apery_table(m, a)
        if None in w or primitives(m, a, w) != [m] + list(a):
            continue
        s = stats(m, a, "deglex")
        if s["c"] <= 4 * m:
            continue
        W = s["W"]
        fgh = apery_type(m, w) <= 4
        cf = s["carries"] == 0 or any(stats(m, a, o)["carries"] == 0 for o in ("lex", "revlex", "minres"))
        topc = 2 * s["N0"] <= 5 * m + 3
        key = ("FGH" if fgh else "-") + ("B" if cf else "-") + ("C" if topc else "-")
        tot[key] += 1
        if key not in least or W < least[key][0]:
            least[key] = (W, [m] + list(a))
    return tot, least


if __name__ == "__main__":
    m, K = int(sys.argv[1]), int(sys.argv[2])
    tot = Counter()
    least = {}
    with Pool(4) as p:
        for t, l in p.imap_unordered(work, [(m, K, a1) for a1 in range(m + 1, K * m + 1) if a1 % m], chunksize=1):
            tot.update(t)
            for key, v in l.items():
                if key not in least or v[0] < least[key][0]:
                    least[key] = v
    print(json.dumps(dict(m=m, K=K, semigroups=sum(tot.values()), classes=dict(sorted(tot.items())),
                          least_W={k: dict(W=v[0], generators=v[1]) for k, v in sorted(least.items())}), indent=1))
