"""Theorem C and Corollary C2 of NOTE.md on EVERY numerical semigroup of genus <= G.

Independent of the rest of this folder and of ../wilf.py: the semigroup tree is
walked by removing minimal generators above the Frobenius number, and every
quantity (minimal generators, conductor, gaps in [c-m, c), least factorization
lengths of the Apéry elements >= c) is computed from the definitions.

    python3 -B tree_check.py 22

The number of semigroups found per genus is printed; it must read
1, 2, 4, 7, 12, 23, 39, 67, 118, 204, 343, 592, 1001, 1693, 2857, 4806, ...
"""
import sys
G = int(sys.argv[1])

def children(gaps, F):
    # semigroup = N \ gaps ; its minimal generators larger than F can be removed
    gapset = set(gaps)
    m = next(x for x in range(1, F + 3) if x not in gapset)
    out = []
    for x in range(F + 1, F + m + 1):
        # x is in S; it is a minimal generator iff no y in S, 0<y<x, with x-y in S
        if not any((y not in gapset) and ((x - y) not in gapset) for y in range(1, x)):
            out.append((tuple(sorted(gaps + (x,))), x))
    return out

def analyse(gaps, F):
    gapset = set(gaps)
    c = F + 1
    g = len(gaps)
    m = next(x for x in range(1, c + 2) if x not in gapset)
    inS = lambda s: s >= 0 and s not in gapset
    top = c + m
    gens = [x for x in range(1, top + 1) if inS(x) and not any(inS(y) and inS(x - y) for y in range(1, x))]
    e = len(gens)
    n = c - g
    W = e * n - c
    # minimal factorization length of every element up to c+m-1
    INF = 10**9
    ln = [INF] * (top + 1); ln[0] = 0
    for s in range(1, top + 1):
        if inS(s):
            ln[s] = 1 + min(ln[s - a] for a in gens if a <= s and inS(s - a))
    ap_top = [w for w in range(c, c + m) if inS(w) and not inS(w - m)]
    ttop = sum(1 for h in range(max(c - m, 0), c) if h in gapset)
    assert ttop == len(ap_top)
    lhs = 2 * W
    assert lhs >= e * m + e - 2 - 2 * sum(ln[w] + e - 1 for w in ap_top), ("Theorem C", gens)
    a1 = min(a for a in gens if a > m)
    lam = min(m - 1, (c + m - 1) // a1)
    assert lhs >= e * m + e - 2 - 2 * ttop * (lam + e - 1), ("Corollary C2", gens)
    hyp = ttop == 1 or (2 * ttop <= e - 1 and m >= (e - 2) ** 2)
    if hyp:
        assert W >= 0
    return hyp, W, e, ttop

count = hyp_count = 0; minW = None
level = [((1,), 1)]        # genus 1: gaps {1}
count_by_g = {}
stack = [((1,), 1)]
while stack:
    gaps, F = stack.pop()
    hyp, W, e, ttop = analyse(gaps, F)
    count += 1; hyp_count += hyp
    count_by_g[len(gaps)] = count_by_g.get(len(gaps), 0) + 1
    if minW is None or W < minW: minW = W
    if len(gaps) < G:
        stack.extend(children(gaps, F))
print("genus 1..%d: semigroups %d (by genus %s)" % (G, count, [count_by_g[i] for i in sorted(count_by_g)]))
print("Theorem C and Corollary C2 bounds hold on all; hypothesis of C2 (bullets 1-2) holds on", hyp_count, "; least W", minW)
