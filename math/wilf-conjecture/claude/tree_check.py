"""Theorems C and G of NOTE.md (and their corollaries) on EVERY numerical semigroup of genus <= G.

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
    # Theorem C: 2mW >= m(em + e - 2) - 2 * sum over Apéry w >= c of (l(w) + e - 1)(w - c + 1)
    sharp = m * (e * m + e - 2) - 2 * sum((ln[w] + e - 1) * (w - c + 1) for w in ap_top)
    assert m * lhs >= sharp, ("Theorem C", gens)
    # its weakenings: drop the factor (w - c + 1)/m; or use l(w) <= lmax and distinct positions (bound H)
    assert sharp >= m * (e * m + e - 2 - 2 * sum(ln[w] + e - 1 for w in ap_top))
    lmax = max(ln[w] for w in ap_top)
    assert sharp >= m * (e * m + e - 2) - (lmax + e - 1) * ttop * (2 * m - ttop + 1), ("bound H", gens)
    a1 = min(a for a in gens if a > m)
    lam = min(m - 1, (c + m - 1) // a1)
    assert lhs >= e * m + e - 2 - 2 * ttop * (lam + e - 1), ("length bound", gens)
    # Theorem G: with D_j = number of integers in [c-(j+1)m, c-jm) that are not in S (negatives count),
    #   2W >= sum_j max(0, 2(e-2)(m - D_j) - D_j(D_j - 1)) - (e-2)(m-1)   >=   (e-2)(m+1-2d) - d(d-1).
    k = e - 1
    bound = -(k - 1) * (m - 1)
    j = 0
    while c - j * m > 0:
        Dj = sum(1 for v in range(c - (j + 1) * m, c - j * m) if not inS(v))
        bound += max(0, 2 * (k - 1) * (m - Dj) - Dj * (Dj - 1))
        j += 1
    single = (k - 1) * (m + 1 - 2 * ttop) - ttop * (ttop - 1)
    assert lhs >= bound >= single, ("Theorem G", gens)
    return single >= 0, bound >= 0, W, e, ttop, sharp

count = one_window = all_windows = few = few_ok = sharp_ok = 0; minW = None; least_sharp = None
count_by_g = {}
stack = [((1,), 1)]        # genus 1: gaps {1}
while stack:
    gaps, F = stack.pop()
    g1, gall, W, e, ttop, sharp = analyse(gaps, F)
    count += 1; one_window += g1; all_windows += gall; sharp_ok += sharp >= 0
    if least_sharp is None or sharp < least_sharp[0]: least_sharp = (sharp, gaps)
    if ttop <= e - 1:
        few += 1; few_ok += W >= 0
    count_by_g[len(gaps)] = count_by_g.get(len(gaps), 0) + 1
    if minW is None or W < minW: minW = W
    if len(gaps) < G:
        stack.extend(children(gaps, F))
print("genus 1..%d: semigroups %d (by genus %s)" % (G, count, [count_by_g[i] for i in sorted(count_by_g)]))
print("bounds of Theorem C (with its weakenings) and Theorem G hold on all; least W", minW)
print("Theorem C certifies W >= 0 on", sharp_ok, "; least value of 2m*(Theorem C bound):", least_sharp[0], "for the gap set", least_sharp[1])
print("Theorem G certifies W >= 0: one window on", one_window, "; all windows on", all_windows)
print("semigroups with at most e-1 gaps in [c-m, c):", few, "; of these with W >= 0:", few_ok)
