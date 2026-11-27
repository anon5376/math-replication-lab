"""List the e = 5 semigroups in a box that none of FGH / Theorem B / Theorem C covers.

Box: multiplicity m, generators {a1<a2<a3<a4} in (m, K*m], none divisible by m,
embedding dimension exactly 5, conductor c > 4m.  Theorem C is applied with
minimal factorization lengths (graded tie-break), Theorem B with each of the
four tie-breaks of apery_downset.py.  For every listed semigroup the Wilf
number is positive (asserted) and its decomposition is recorded.
"""
import json
import sys
from itertools import combinations
from multiprocessing import Pool

from apery_downset import apery_table, primitives, stats

ORDERS = ("deglex", "lex", "revlex", "minres")


def apery_type(m, w):
    return sum(not any(u > v and (u - v) >= w[(u - v) % m] for u in w) for v in w)


def work(args):
    m, K, a1 = args
    out, seen, typed = [], 0, 0
    pool = [x for x in range(a1 + 1, K * m + 1) if x % m]
    for rest in combinations(pool, 3):
        a = (a1,) + rest
        w = apery_table(m, a)
        if None in w or primitives(m, a, w) != [m] + list(a):
            continue
        s = stats(m, a, "deglex")
        if s["c"] <= 4 * m:
            continue
        seen += 1
        if 2 * s["N0"] <= 5 * m + 3:
            continue                                   # Theorem C
        t = apery_type(m, w)
        if t <= 4:
            continue                                   # FGH
        typed += 1
        carries = {o: (s if o == "deglex" else stats(m, a, o))["carries"] for o in ORDERS}
        if min(carries.values()) == 0:
            continue                                   # Theorem B
        assert s["W"] > 0
        out.append(dict(generators=[m] + list(a), c=s["c"], g=s["g"], n=s["n"], W=s["W"], type=t,
                        depth=s["q"], N0=s["N0"], top_window=s["topwindow"],
                        sum_delta_top=s["sum_delta_top"], anticarries=s["anticarries"],
                        carries=s["carries"], least_carries_over_orders=min(carries.values())))
    return seen, typed, out


if __name__ == "__main__":
    m, K = int(sys.argv[1]), int(sys.argv[2])
    seen = typed = 0
    core = []
    with Pool(4) as p:
        for s, t, o in p.imap_unordered(work, [(m, K, a1) for a1 in range(m + 1, K * m + 1) if a1 % m]):
            seen += s
            typed += t
            core += o
    core.sort(key=lambda d: (d["W"], d["generators"]))
    print(json.dumps(dict(m=m, K=K, semigroups=seen, not_C_and_type_at_least_5=typed, uncovered=len(core),
                          depth_histogram={str(q): sum(d["depth"] == q for d in core) for q in sorted({d["depth"] for d in core})},
                          genus_range=[min(d["g"] for d in core), max(d["g"] for d in core)] if core else None,
                          least_W=core[0] if core else None, core=core)))
