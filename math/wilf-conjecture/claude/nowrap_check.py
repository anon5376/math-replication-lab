"""Proposition C3 of NOTE.md, checked numerically on random no-wrap semigroups.

For S = <m, a_1..a_k> whose `minres` normal forms all satisfy sum x_i (a_i mod m) <= m - 1,
the proof of C3 rests on the identity

    m((k+1)m + k - 1)/2 - sum_{t in T} mu(t)(a.t - c + 1)
        = sum_{t not in T} mu(t)(1 + r.t) - rho * mu(T_q) + (f + 1) * mu(T_{q-1}),

where M = mq + f, rho = m - 1 - f, T_q / T_{q-1} are the cells of T of level q / q - 1.
This script asserts the identity and the non-negativity of its right side.
Seeded; standard library only.
"""
import random
from math import gcd

from apery_downset import apery_table, normal_forms, primitives


def check(m, a):
    k = len(a)
    r = [x % m for x in a]
    w, nf = normal_forms(m, a, "minres")
    B = set(nf)
    rv = lambda t: sum(ri * xi for ri, xi in zip(r, t))
    if any(rv(x) > m - 1 for x in B):
        return None                                  # not a no-wrap semigroup
    wt = {x: w[i] for i, x in enumerate(nf)}
    M = max(w)
    c, q, f = M - m + 1, M // m, M % m
    rho = m - 1 - f

    def top(x, i):
        y = x
        while True:
            z = y[:i] + (y[i] + 1,) + y[i+1:]
            if z not in B:
                return y
            y = z

    mu = dict.fromkeys(B, 0)
    for x in B:
        for i in range(k):
            mu[top(x, i)] += 1
    T = [t for t in B if wt[t] >= c]
    Tq = [t for t in T if wt[t] // m == q]
    Tq1 = [t for t in T if wt[t] // m == q - 1]
    assert len(Tq) + len(Tq1) == len(T)
    assert all(rv(t) <= f for t in Tq) and all(rv(t) >= f + 1 for t in Tq1)
    left2 = m * ((k + 1) * m + k - 1) - 2 * sum(mu[t] * (wt[t] - c + 1) for t in T)
    right = (sum(mu[t] * (1 + rv(t)) for t in B if t not in T)
             - rho * sum(mu[t] for t in Tq) + (f + 1) * sum(mu[t] for t in Tq1))
    assert left2 == 2 * right and right >= 0, (m, a)
    return right


if __name__ == "__main__":
    random.seed(8)
    n = zero = 0
    for _ in range(60000):
        m = random.randint(4, 40)
        k = random.randint(2, 5)
        r = sorted(random.sample(range(1, m), min(k, m - 1)))
        a = tuple(sorted(random.randint(1, 3) * m + x for x in r))
        if gcd(m, *a) != 1:
            continue
        w = apery_table(m, a)
        if primitives(m, a, w) != [m] + list(a):
            continue
        v = check(m, a)
        if v is not None:
            n += 1
            zero += v == 0
    print("no-wrap semigroups checked:", n, "; identity and non-negativity hold on all; right side = 0 on", zero)
    print("control [23, 47, 51, 78, 80]: m * (Theorem C bound with minres lengths) =", check(23, (47, 51, 78, 80)))
