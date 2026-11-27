"""Corollary B2 of NOTE.md: uniform rays S_q = <m, q*m + r_1, ..., q*m + r_k>.

Hypothesis (G) for (m; r), 1 = r_1 < ... < r_k <= m-1:
    N_cyc(v) = N(v) for all 0 <= v < m,
where N(v) is the least number of coins r_i summing to v exactly and N_cyc(v)
the least number summing to v modulo m.  Under (G) the note proves, for every
q >= 1:  Ap(S_q) = {q*m*N(v) + v},  e(S_q) = k+1,  W(S_q) = q*sigma - k*rho >= 0,
and for q >= 2 the type equals tau(m; r) (independent of q).

This script (exact integers, standard library):
  scan  m0 m1    count 4-subsets r of [1, m-1] containing 1 with (G), and those with tau >= 5
  check m r2 r3 r4 Q   re-verify every claim for q = 1..Q with apery_downset.stats
"""
import json
import sys
from collections import deque
from itertools import combinations

from apery_downset import apery_table, stats


def coin_counts(m, r):
    """N(v) for 0 <= v < m (exact representations; r contains 1)."""
    N = [0] * m
    for v in range(1, m):
        N[v] = 1 + min(N[v - ri] for ri in r if ri <= v)
    return N


def cyclic_counts(m, r):
    """Breadth-first distances from 0 in the Cayley digraph of Z/m with steps r."""
    dist = [None] * m
    dist[0] = 0
    todo = deque([0])
    while todo:
        v = todo.popleft()
        for ri in r:
            u = (v + ri) % m
            if dist[u] is None:
                dist[u] = dist[v] + 1
                todo.append(u)
    return dist


def tau(m, r, N):
    return sum(all(v + ri >= m or N[v + ri] <= N[v] for ri in r) for v in range(m))


def apery_type(m, w):
    return sum(not any(u > v and (u - v) >= w[(u - v) % m] for u in w) for v in w)


def sigma_rho(m, r, N):
    """sigma = k*L*m - (k+1)*sum N, rho = m - 1 - max{v : N(v) = L}."""
    k, L = len(r), max(N)
    f = max(v for v in range(m) if N[v] == L)
    return k * L * m - (k + 1) * sum(N), m - 1 - f, L, f


def scan(m0, m1):
    for m in range(m0, m1 + 1):
        good = big = 0
        first = None
        for rest in combinations(range(2, m), 3):
            r = (1,) + rest
            N = coin_counts(m, r)
            if N != cyclic_counts(m, r):
                continue
            good += 1
            t = tau(m, r, N)
            if t >= 5:
                big += 1
                sg, rho, L, f = sigma_rho(m, r, N)
                cand = (sg - 4 * rho, r, t, L)
                if first is None or cand < first:
                    first = cand
        print(json.dumps(dict(m=m, subsets_with_G=good, with_tau_at_least_5=big,
                              least_sigma_minus_k_rho=first)), flush=True)


def check(m, r, Q):
    N = coin_counts(m, r)
    assert N == cyclic_counts(m, r), "hypothesis (G) fails"
    sg, rho, L, f = sigma_rho(m, r, N)
    t = tau(m, r, N)
    k = len(r)
    rows = []
    for q in range(1, Q + 1):
        a = tuple(q * m + ri for ri in r)
        w = apery_table(m, a)
        assert w == [q * m * N[v] + v for v in range(m)]
        s = stats(m, a, "minres")            # also asserts that a is the minimal generating set
        assert s["carries"] == 0 and s["W"] == q * sg - k * rho and s["W"] >= 0
        ty = apery_type(m, w)
        assert q == 1 or ty == t
        rows.append(dict(q=q, c=s["c"], g=s["g"], n=s["n"], W=s["W"], type=ty))
    print(json.dumps(dict(m=m, r=list(r), L=L, f=f, sigma=sg, rho=rho, tau=t, rows=rows), indent=1))


if __name__ == "__main__":
    if sys.argv[1] == "scan":
        scan(int(sys.argv[2]), int(sys.argv[3]))
    else:
        m = int(sys.argv[2])
        check(m, (1,) + tuple(int(v) for v in sys.argv[3:6]), int(sys.argv[6]))
