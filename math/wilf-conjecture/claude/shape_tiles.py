"""The shape-only form of Theorem C+ (NOTE.md, section 7), evaluated on lattice tiles.

For a finite down-set B in N^k with |B| = m put
    mu(t)   = sum over i with t + e_i not in B of (t_i + 1)        (sum of mu = k m)
    Nmax(B) = sum of mu(t) over the maximal cells t of B
    R(B)    = sum_j j * mu_j,  mu_0 >= mu_1 >= ... the decreasing rearrangement of mu
    Phi(B)  = m (k m - Nmax) + R - (k-1) m (m-1) / 2.
Theorem C+ gives  m * W(S) >= Phi(B)  whenever B is an Apéry normal-form
down-set of S.  Phi(B) < 0 does happen for down-sets that are not tiles (the
simplex of degree 2 in N^2 has Phi = -3).  This script looks for a *tile* with
Phi < 0 in two bounded families:

  exhaustive k m0 m1   every down-set of size m in N^k; those with Phi < 0 are
                       tested for a bijective residue vector r in [1,m-1]^k
  graded k m0 m1       for every r_1 < ... < r_k in [1, m-1] generating Z/m, the
                       tile of graded-lex-least representatives of the classes
"""
import itertools
import sys

from pseudo_tiles import downsets


def phi(B, k):
    m = len(B)
    mu = dict.fromkeys(B, 0)
    for x in B:
        for i in range(k):
            y = x
            while True:
                z = y[:i] + (y[i] + 1,) + y[i+1:]
                if z not in B:
                    break
                y = z
            mu[y] += 1
    nmax = sum(v for t, v in mu.items() if v == sum(t) + k)
    rearr = sum(j * v for j, v in enumerate(sorted(mu.values(), reverse=True)))
    return 2 * m * (k * m - nmax) + 2 * rearr - (k - 1) * m * (m - 1)      # = 2 * Phi(B)


def bijective_vector(B, k):
    m = len(B)
    cells = sorted(B)
    for r in itertools.product(range(1, m), repeat=k):
        if len({sum(ri * xi for ri, xi in zip(r, x)) % m for x in cells}) == m:
            return r
    return None


def graded_tile(m, r):
    """Breadth-first by length; within a length the lex-least representative."""
    k = len(r)
    nf = {0: (0,) * k}
    frontier = [0]
    while frontier:
        cand = {}
        for v in frontier:
            x = nf[v]
            for i in range(k):
                u = (v + r[i]) % m
                if u in nf:
                    continue
                y = x[:i] + (x[i] + 1,) + x[i+1:]
                if u not in cand or y < cand[u]:
                    cand[u] = y
        nf.update(cand)
        frontier = list(cand)
    return set(nf.values()) if len(nf) == m else None


if __name__ == "__main__":
    mode, k, m0, m1 = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    for m in range(m0, m1 + 1):
        if mode == "exhaustive":
            shapes = negative = tiles = 0
            for B in downsets(k, m):
                shapes += 1
                if phi(B, k) < 0:
                    negative += 1
                    tiles += bijective_vector(B, k) is not None
            print(f"k={k} m={m} downsets={shapes} with_Phi<0={negative} of_which_cyclic_tiles={tiles}", flush=True)
        else:
            cnt = neg = 0
            least = None
            for r in itertools.combinations(range(1, m), k):
                B = graded_tile(m, r)
                if B is None:
                    continue
                assert all(x[i] == 0 or x[:i] + (x[i] - 1,) + x[i+1:] in B for x in B for i in range(k))
                v = phi(B, k)
                cnt += 1
                neg += v < 0
                if least is None or v < least[0]:
                    least = (v, r)
            print(f"k={k} m={m} graded_tiles={cnt} with_Phi<0={neg} least_2Phi={least}", flush=True)
