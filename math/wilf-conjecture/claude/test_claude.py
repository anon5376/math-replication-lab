"""Checks behind NOTE.md that are not already a saved result file.

Run from this folder:  python3 -B -m unittest -v test_claude
"""
import os
import random
import sys
import unittest
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.dirname(HERE))

from apery_downset import apery_table, normal_forms, primitives, stats   # noqa: E402
from shape_tiles import phi                                              # noqa: E402
from wilf import compute                                                 # noqa: E402


def tops(B, k):
    def top(x, i):
        y = x
        while True:
            z = y[:i] + (y[i] + 1,) + y[i+1:]
            if z not in B:
                return y
            y = z
    return top


class NoteChecks(unittest.TestCase):
    def test_control(self):
        s = stats(23, (47, 51, 78, 80))
        self.assertEqual([s[key] for key in "mecgnW"], [23, 5, 170, 117, 53, 95])
        # Theorem B on the control: no carries, 86 + 9 - 0
        self.assertEqual((s["sum_delta_top"], s["anticarries"], s["carries"]), (86, 9, 0))

    def test_random_against_repository_verifier(self):
        """Lemmas 2 and 3 and Theorems A, B, C, C+, G are asserted inside stats();
        the invariants are compared with ../wilf.py."""
        random.seed(1)
        count, dims = 0, set()
        for _ in range(20000):
            kk = random.randint(1, 6)
            m = random.randint(2, 40)
            gens = sorted(set([m] + [random.randint(m + 1, 6 * m) for _ in range(kk)]))
            if gcd(*gens) != 1:
                continue
            w = apery_table(gens[0], gens[1:])
            prim = primitives(gens[0], gens[1:], w)
            ref = compute(prim)[1]
            for order in ("lex", "revlex"):
                s = stats(prim[0], prim[1:], order)
                self.assertTrue(all(s[key] == ref[key] for key in "mecgnW"), prim)
            count += 1
            dims.add(s["e"])
        self.assertEqual(count, 17589)
        self.assertEqual(dims, {2, 3, 4, 5, 6, 7})

    def test_failing_lemma_direction(self):
        # <3,4,5>: direction 2 alone gives 1 < 3/2
        m, a = 3, (4, 5)
        w, nf = normal_forms(m, a)
        B, M = set(nf), max(w)
        wt = {x: w[r] for r, x in enumerate(nf)}
        top = tops(B, 2)
        sums = [sum(M - wt[top(x, i)] for x in B) for i in range(2)]
        self.assertEqual(sums, [2, 1])
        self.assertEqual(stats(m, a)["W"], 0)

    def test_failing_lemma_cell(self):
        # <4,6,7>: the maximal cell has one carry and no surplus
        w, nf = normal_forms(4, (6, 7))
        self.assertEqual(w, [0, 13, 6, 7])
        self.assertIn((1, 1), nf)
        self.assertEqual(13 // 4 - 6 // 4 - 7 // 4, 1)
        self.assertEqual(stats(4, (6, 7))["W"], 5)

    def test_triangle_shape_and_hrw_example(self):
        tri = {(i, j) for i in range(3) for j in range(3) if i + j <= 2}
        self.assertEqual(phi(tri, 2), -6)                       # 2 * Phi = -6
        a, m = (9, 10), 6                                        # gamma = (3/2, 5/3)
        wts = [a[0] * x + a[1] * y for x, y in sorted(tri)]
        d = sum(v // m for v in wts)
        u = sum((max(wts) - v) // m for v in wts)
        self.assertEqual((u, d), (5, 11))
        self.assertLess(2 * u, d)
        self.assertLess(len({v % m for v in wts}), m)            # a residue collision

    def test_explicit_ray(self):
        for q in range(1, 7):
            s = stats(22, tuple(22 * q + r for r in (1, 5, 6, 7)), "minres")
            self.assertEqual((s["e"], s["c"], s["g"], s["W"], s["carries"]),
                             (5, 88 * q - 17, 49 * q, 107 * q - 68, 0))
            if q >= 2:
                self.assertEqual(s["topwindow"], 1)              # only F is a gap in [c-m, c)

    def test_equality_families(self):
        for m in range(3, 12):
            for q in (1, 2, 3):
                s = stats(m, tuple(q * m + r for r in range(1, m)), "deglex")
                k = m - 1
                self.assertEqual(s["W"], 0)
                # Theorems C+ and C are equalities here
                self.assertEqual(2 * m * (k * m - s["N0"]) - (k - 1) * m * (m - 1) + 2 * s["rearrangement"], 0)
                self.assertEqual(s["sharpC_times_2m"], 0)
        s = stats(7, (30,), "deglex")
        self.assertEqual((s["W"], s["N0"], s["rearrangement"], s["sharpC_times_2m"]), (0, 7, 0, 0))

    def test_theorem_C_example(self):
        # [25,36,42,43,44]: W = 37, twelve Apéry elements >= c, Theorem C bound 15.56, mean deficit 10.58
        s = stats(25, (36, 42, 43, 44), "deglex")
        self.assertEqual((s["W"], s["window_gaps"][0], s["N0"]), (37, 12, 84))
        self.assertEqual(s["sharpC_times_2m"], 778)          # 778 / 50 = 15.56
        self.assertLess(s["boundH_times_2m"], 0)             # the closed form (C2) does not reach it
        self.assertLess(s["gap_bound_twice"], 0)             # nor does Theorem G


    def test_theorem_G(self):
        # explicit ray: one gap in [c-m, c) for q >= 2, so W >= (e-2)(m-1)/2
        for q in range(2, 6):
            s = stats(22, tuple(22 * q + r for r in (1, 5, 6, 7)), "deglex")
            self.assertEqual(s["window_gaps"][0], 1)
            self.assertGreaterEqual(2 * s["W"], 3 * 21)
        # the one-window bound is an equality for e = 2
        s = stats(7, (30,), "deglex")
        self.assertEqual((s["window_gaps"][0], s["gap_bound_twice"], s["W"]), (1, 0, 0))
        # control: 6 gaps in [147, 170); the bound is 3*(24-12) - 30 = 6 <= 2W
        s = stats(23, (47, 51, 78, 80), "deglex")
        self.assertEqual(s["window_gaps"][0], 6)
        self.assertGreaterEqual(s["gap_bound_twice"], 3 * (23 + 1 - 12) - 6 * 5)

    def test_attempt7_formula(self):
        """Generators just below multiples of m (attempt 7 of the note)."""
        rng = random.Random(7)
        tested = 0
        for m in range(8, 40):
            for _ in range(400):
                k = rng.choice((2, 3, 4))
                b = sorted(rng.sample(range(1, m), k))
                Q = [rng.choice((2, 3)) for _ in b]
                a = tuple(Qi * m - bi for Qi, bi in zip(Q, b))
                if len(set(a)) < k:
                    continue
                w = apery_table(m, a)
                if None in w or primitives(m, a, w) != [m] + sorted(a):
                    continue
                order = sorted(range(k), key=lambda i: a[i])
                a_s = tuple(a[i] for i in order)
                Qs = [Q[i] for i in order]
                bs = [b[i] for i in order]
                _, nf = normal_forms(m, a_s, "lex")
                B = set(nf)
                bv = lambda x: sum(bi * xi for bi, xi in zip(bs, x))
                if any(bv(x) > m - 1 for x in B):
                    continue
                top = tops(B, k)
                qd = lambda x: sum(Qi * xi for Qi, xi in zip(Qs, x))
                Qstar = max(qd(x) for x in B)
                beta = min(bv(x) for x in B if qd(x) == Qstar)
                formula = sum(Qstar - qd(top(x, i)) for x in B for i in range(k)) + (m - 1) - k * beta
                self.assertEqual(formula, stats(m, a_s, "lex")["W"])
                tested += 1
        self.assertEqual(tested, 411)

    def test_difference_packing_count(self):
        """Lemma S: N(k; p, n) counts {z : |z+| <= p, |z-| <= n} and exceeds C(p+n+k, k)."""
        from itertools import product
        from math import comb

        def N(k, p, n):
            return sum(comb(k, j) * comb(n, j) * comb(p + k - j, k - j) for j in range(k + 1))

        for k, p, n in ((2, 1, 1), (2, 2, 1), (3, 2, 2), (4, 2, 1), (4, 2, 2), (3, 3, 2)):
            brute = sum(1 for z in product(range(-n, p + 1), repeat=k)
                        if sum(v for v in z if v > 0) <= p and -sum(v for v in z if v < 0) <= n)
            self.assertEqual(N(k, p, n), brute)
        for k in range(2, 13):
            for p in range(1, 21):
                for n in range(1, p + 1):
                    self.assertGreater(N(k, p, n), comb(p + n + k, k))
        self.assertEqual([N(4, (h + 1) // 2, h // 2) for h in (2, 3, 4, 5)], [21, 55, 131, 255])

    def test_tile_bound(self):
        """Section 14: Proposition T and the failing strong inequality."""
        import itertools
        from tile_check import tiles, profile
        # the semigroup where anti-carries < carries: W = 49 < 50 = sum of delta over the chain tops
        s = stats(14, (22, 23, 48, 49, 57, 61), "deglex")
        self.assertEqual((s["W"], s["sum_delta_top"], s["anticarries"], s["carries"]), (49, 50, 0, 1))
        # every tile of size 7: 198 tiles, the bound w is >= 0 and vanishes only for k = 1 and k = 6
        count = 0
        for k in range(1, 7):
            for r in itertools.combinations(range(1, 7), k):
                for B in tiles(k, 7, r):
                    lo, w = profile(B, k, 7, r)
                    self.assertGreaterEqual(lo, 0)          # the strong inequality still holds at this size
                    self.assertGreaterEqual(w, 0)
                    self.assertEqual(w == 0, k in (1, 6))
                    count += 1
        self.assertEqual(count, 198)


if __name__ == "__main__":
    unittest.main()
