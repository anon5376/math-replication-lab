"""Lemma S of NOTE.md, brute-force re-check of three small cases.

The note proves that the simplex {x in N^k : |x| <= L} is not a lattice tile for
any k >= 2, L >= 2.  Here the cases (k, L) = (3, 2), (4, 2), (4, 3) are confirmed
independently: |simplex| = 10, 15, 35 is squarefree, so every abelian group of
that order is cyclic, and every r in (Z/m)^k is tested for injectivity of
x -> r.x mod m on the simplex.  The L = 1 rows are positive controls (k! maps).
"""
import itertools


def simplex(k, L):
    return [x for x in itertools.product(range(L + 1), repeat=k) if sum(x) <= L]


def injective_vectors(k, L):
    cells = simplex(k, L)
    m = len(cells)
    deg1 = [x for x in cells if sum(x) <= 1]
    found = tested = 0
    for r in itertools.product(range(m), repeat=k):
        tested += 1
        if len({sum(ri * xi for ri, xi in zip(r, x)) % m for x in deg1}) != len(deg1):
            continue
        if len({sum(ri * xi for ri, xi in zip(r, x)) % m for x in cells}) == m:
            found += 1
    return m, tested, found


if __name__ == "__main__":
    for k, L in ((2, 1), (3, 1), (3, 2), (4, 2), (4, 3)):
        m, tested, found = injective_vectors(k, L)
        print(f"k={k} L={L} m={m} residue_vectors_tested={tested} injective={found}")
