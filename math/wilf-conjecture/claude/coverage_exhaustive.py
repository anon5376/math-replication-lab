"""Which e = 5 semigroups are covered by which criterion?  (bounded, exhaustive)

For a multiplicity m this enumerates every 4-subset {a1<a2<a3<a4} of
(m, K*m] with no a_i divisible by m, keeps those for which <m,a1..a4> has
embedding dimension exactly 5 and conductor c > 4m, and counts

  type>=5 : type t >= 5, so the Fröberg-Gottlieb-Häggkvist criterion t <= e-1 does not apply
  B       : carry-free normal forms under one of the four tie-breaks   (Theorem B)
  G       : d(d-1) <= 3(m+1-2d), d = number of gaps in [c-m, c)         (Corollary G1, one window)
  C       : the bound of Theorem C is >= 0

Every identity and bound of NOTE.md is asserted inside apery_downset.stats on each instance.
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
    pool = [x for x in range(a1 + 1, K * m + 1) if x % m]
    for rest in combinations(pool, 3):
        a = (a1,) + rest
        w = apery_table(m, a)
        if None in w or primitives(m, a, w) != [m] + list(a):
            continue
        s = stats(m, a, "deglex")
        if s["c"] <= 4 * m:
            continue
        big = apery_type(m, w) >= 5
        d = s["window_gaps"][0]
        flags = dict(
            B=s["carries"] == 0 or any(stats(m, a, o)["carries"] == 0 for o in ("lex", "revlex", "minres")),
            G=d * (d - 1) <= 3 * (m + 1 - 2 * d),
            C=s["sharpC_times_2m"] >= 0,
        )
        tot["semigroups"] += 1
        tot["type>=5"] += big
        for name, ok in flags.items():
            tot[name] += ok
            tot[name + " and type>=5"] += ok and big
        tot["neither B nor G"] += not (flags["B"] or flags["G"])
        tot["negative W"] += s["W"] < 0
    return tot


if __name__ == "__main__":
    m, K = int(sys.argv[1]), int(sys.argv[2])
    tot = Counter()
    with Pool(4) as p:
        for t in p.imap_unordered(work, [(m, K, a1) for a1 in range(m + 1, K * m + 1) if a1 % m], chunksize=1):
            tot.update(t)
    print(json.dumps(dict(m=m, K=K, **dict(sorted(tot.items()))), indent=1))
