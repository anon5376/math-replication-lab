"""Two checkers that share no code with ../wilf.py or apery_downset.py.

1. `direct(gens)`: membership by dynamic programming over the integers.
   If t, t+1, ..., t+m-1 all lie in S (m the least generator) then every
   u >= t lies in S, because u = (t + j) + i*m with 0 <= j < m, i >= 0 and S is
   closed under adding m.  So once m consecutive members have been seen and
   every generator has been passed, the last gap seen is the Frobenius number.

2. `certified(gens, w, pred)`: an Apéry table w[0..m-1] with predecessors is
   accepted only if
     (a) w[0] = 0 and w[r] = r (mod m);
     (b) following predecessors from any r strictly decreases w and reaches
         residue 0, each step subtracting a listed generator  (so w[r] is in S);
     (c) w[(r + x) mod m] <= w[r] + x for every residue r and generator x.
   From (c), by induction on the length of a factorization of s in S,
   w[s mod m] <= s; with (b) this makes w[r] the least member of its class.
   Then g = sum floor(w[r]/m), c = max(w) - m + 1.  A generator x is minimal
   iff there is no 0 < y < x with y in S and x - y in S, where membership is
   read off w:  s in S  iff  s >= w[s mod m].

`python3 check_independent.py` runs both on the control, the extremal
examples of the note and the explicit family of Corollary B2, and compares
with ../wilf.py and apery_downset.py.
"""
import heapq
import json
import os
import sys


def direct(gens):
    gens = sorted(set(gens))
    m = gens[0]
    member = [True]
    run, last_gap, gaps, t = 1, -1, 0, 0
    while run < m or t < gens[-1]:
        t += 1
        inside = any(t >= x and member[t - x] for x in gens)
        member.append(inside)
        if inside:
            run += 1
        else:
            run, last_gap, gaps = 0, t, gaps + 1
    c = last_gap + 1
    minimal = [x for x in gens if not any(member[y] and member[x - y] for y in range(1, x))]
    e = len(minimal)
    n = c - gaps
    return dict(m=m, e=e, c=c, g=gaps, n=n, W=e * n - c, minimal_generators=minimal)


def certified(gens, w, pred):
    gens = sorted(set(gens))
    m = gens[0]
    if len(w) != m or len(pred) != m or w[0] != 0 or pred[0] is not None:
        raise ValueError("malformed table")
    for r in range(m):
        if w[r] % m != r or w[r] < 0:
            raise ValueError("wrong residue")
        seen, s = 0, r                       # (b): strictly descending chain to residue 0
        while s != 0:
            p, x = pred[s]
            if x not in gens or w[p] + x != w[s] or (p + x) % m != s or x <= 0:
                raise ValueError("bad predecessor")
            s, seen = p, seen + 1
            if seen > m:
                raise ValueError("predecessor cycle")
        for x in gens:                       # (c)
            if w[(r + x) % m] > w[r] + x:
                raise ValueError("edge inequality violated")
    inside = lambda s: s >= 0 and s >= w[s % m]
    minimal = [x for x in gens if not any(inside(y) and inside(x - y) for y in range(1, x))]
    c = max(w) - m + 1
    g = sum(v // m for v in w)
    e, n = len(minimal), c - g
    return dict(m=m, e=e, c=c, g=g, n=n, W=e * n - c, minimal_generators=minimal)


def make_certificate(gens):
    """A plain Dijkstra producing (w, pred); its output is only ever trusted
    after `certified` accepts it."""
    gens = sorted(set(gens))
    m = gens[0]
    w, pred = [None] * m, [None] * m
    w[0] = 0
    heap = [(0, 0)]
    while heap:
        d, r = heapq.heappop(heap)
        if d != w[r]:
            continue
        for x in gens[1:]:
            s = (r + x) % m
            if w[s] is None or d + x < w[s]:
                w[s], pred[s] = d + x, [r, x]
                heapq.heappush(heap, (d + x, s))
    return w, pred


if __name__ == "__main__":
    here = os.path.dirname(os.path.abspath(__file__))
    sys.path.insert(0, os.path.dirname(here))
    sys.path.insert(0, here)
    from wilf import compute, verify            # the repository's verifier
    from apery_downset import stats

    with open(os.path.join(os.path.dirname(here), "control.json")) as f:
        control = json.load(f)
    c1 = certified(control["generators"], control["apery"], control["apery_predecessors"])
    assert c1 == verify(control) == direct(control["generators"])
    assert (c1["m"], c1["e"], c1["c"], c1["g"], c1["n"], c1["W"]) == (23, 5, 170, 117, 53, 95)
    print("control", c1)

    cases = [[20, 32, 33, 37, 75], [22, 35, 37, 38, 40], [23, 36, 40, 41, 42],
             [25, 36, 42, 43, 44], [26, 27, 37, 73, 76], [13, 14, 16, 18, 19]]
    cases += [[22] + [22 * q + r for r in (1, 5, 6, 7)] for q in range(1, 9)]
    cases += [[25] + [25 * q + r for r in (1, 4, 7, 8)] for q in range(1, 5)]
    for gens in cases:
        w, pred = make_certificate(gens)
        a = certified(gens, w, pred)
        b = direct(gens)
        r = verify(dict(generators=gens, apery=w, apery_predecessors=pred))
        s = stats(gens[0], gens[1:])
        assert a == b == r, gens
        assert all(a[key] == s[key] for key in "mecgnW"), gens
        print(gens, {key: a[key] for key in "mecgnW"})
    print("all four computations agree on", 1 + len(cases), "semigroups")
