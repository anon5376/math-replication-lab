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
        """Lemma 2, Theorems A, B, C, C+, C2 are asserted inside stats();
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
                # Theorem C+ is an equality here
                self.assertEqual(2 * m * (k * m - s["N0"]) - (k - 1) * m * (m - 1) + 2 * s["rearrangement"], 0)
        s = stats(7, (30,), "deglex")
        self.assertEqual((s["W"], s["N0"], s["rearrangement"]), (0, 7, 0))


if __name__ == "__main__":
    unittest.main()
