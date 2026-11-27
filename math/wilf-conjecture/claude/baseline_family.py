"""The repository's baseline family, re-read through the criteria of NOTE.md.

Same lists as `../wilf.py sweep`: m in 19..55, q in {1,2,3}, offsets a<b<c<d in
1..12, generators [m, qm+a, qm+b, (q+1)m+c, (q+1)m+d] with gcd 1; the same
frontier filter (e = 5, 3e < m, g > 100, c > 4m, and g > 120 if m | c).
For every frontier list: type, Theorem B (carry-free under one of four
tie-breaks), Corollary G1, Theorem C and Theorem C+.
"""
import json
import os
import sys
from collections import Counter
from itertools import combinations
from math import gcd

from apery_downset import apery_table, primitives, stats


def apery_type(m, w):
    return sum(not any(u > v and (u - v) >= w[(u - v) % m] for u in w) for v in w)


if __name__ == "__main__":
    tot = Counter()
    for m in range(19, 56):
        for q in (1, 2, 3):
            for a, b, c, d in combinations(range(1, 13), 4):
                gens = (m, q*m + a, q*m + b, (q+1)*m + c, (q+1)*m + d)
                if gcd(*gens) != 1:
                    continue
                tot["lists"] += 1
                w = apery_table(m, gens[1:])
                prim = primitives(m, gens[1:], w)
                if len(prim) != 5:
                    continue
                s = stats(m, prim[1:], "deglex")
                if not (3 * 5 < m and s["g"] > 100 and s["c"] > 4 * m and (s["c"] % m != 0 or s["g"] > 120)):
                    continue
                tot["frontier"] += 1
                big = apery_type(m, w) >= 5
                cf = s["carries"] == 0 or any(stats(m, prim[1:], o)["carries"] == 0 for o in ("lex", "revlex", "minres"))
                d = s["window_gaps"][0]
                G = d * (d - 1) <= 3 * (m + 1 - 2 * d)
                C = s["sharpC_times_2m"] >= 0
                Cp = 2 * m * (4 * m - s["N0"]) - 3 * m * (m - 1) + 2 * s["rearrangement"] >= 0
                tot["type>=5"] += big
                tot["carry-free"] += cf
                tot["carry-free and type>=5"] += cf and big
                tot["Corollary G1 (one window) applies"] += G
                tot["Corollary G1 (one window) applies and type>=5"] += G and big
                tot["Theorem C applies"] += C
                tot["Theorem C applies and type>=5"] += C and big
                tot["Theorem C+ applies"] += Cp
                tot["negative W"] += s["W"] < 0
    print(json.dumps(tot, indent=1))
