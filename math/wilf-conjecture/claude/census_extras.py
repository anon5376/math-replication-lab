"""Two side observations of NOTE.md on every numerical semigroup of genus <= G, from the definitions.

  1. (attempt 12, a conjecture)  W >= (e - 1 - d) * m  whenever d <= e - 1,
     d = number of gaps in [c - m, c).
  2. Theorem G with any minimal generator n as base:
         2W >= sum_j max(0, 2(e-2)(n - D_j) - D_j(D_j - 1)) - (e-2)(n-1),
     D_j = number of non-members of S in [c - (j+1)n, c - jn).  The bound is asserted for
     every minimal generator; the script counts how often a base other than m certifies
     W >= 0 when m does not.

    python3 -B census_extras.py 20
"""
import sys

G = int(sys.argv[1])


def children(gaps, F):
    gapset = set(gaps)
    m = next(x for x in range(1, F + 3) if x not in gapset)
    out = []
    for x in range(F + 1, F + m + 1):
        if not any((y not in gapset) and ((x - y) not in gapset) for y in range(1, x)):
            out.append((tuple(sorted(gaps + (x,))), x))
    return out


count = few = bad_m = bad_e = cert_m = cert_any = 0
stack = [((1,), 1)]
while stack:
    gaps, F = stack.pop()
    gapset = set(gaps)
    c, g = F + 1, len(gaps)
    m = next(x for x in range(1, c + 2) if x not in gapset)
    inS = lambda s: s >= 0 and s not in gapset
    gens = [x for x in range(1, c + m + 1) if inS(x) and not any(inS(y) and inS(x - y) for y in range(1, x))]
    e = len(gens)
    W = e * (c - g) - c
    d = sum(1 for h in range(max(c - m, 0), c) if h in gapset)
    count += 1
    if d <= e - 1:
        few += 1
        bad_m += W < (e - 1 - d) * m
        bad_e += W < (e - 1 - d) * e
    best = None
    for n in gens:
        b2 = -(e - 2) * (n - 1)
        j = 0
        while c - j * n > 0:
            Dj = sum(1 for v in range(c - (j + 1) * n, c - j * n) if not inS(v))
            b2 += max(0, 2 * (e - 2) * (n - Dj) - Dj * (Dj - 1))
            j += 1
        assert 2 * W >= b2, (gens, n)
        if n == m:
            bm = b2
        best = b2 if best is None else max(best, b2)
    cert_m += bm >= 0
    cert_any += best >= 0
    if len(gaps) < G:
        stack.extend(children(gaps, F))

print("genus 1..%d: %d semigroups" % (G, count))
print("with d <= e-1: %d ; violations of W >= (e-1-d)m: %d ; of W >= (e-1-d)e: %d" % (few, bad_m, bad_e))
print("Theorem G holds for every minimal generator as base; certified with base m: %d ; with the best base: %d"
      % (cert_m, cert_any))
