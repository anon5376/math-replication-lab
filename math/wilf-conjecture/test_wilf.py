from copy import deepcopy
from itertools import combinations
from math import gcd
import unittest

from wilf import compute, verify


def direct(generators):
    """Independent membership enumeration; m consecutive members close the gaps."""
    m = min(generators)
    bits = [True]
    g, c, run = 0, 0, 1
    t = 1
    while run < m or t <= max(generators):
        belongs = any(t >= x and bits[t-x] for x in generators)
        bits.append(belongs)
        if belongs:
            run += 1
        else:
            g += 1
            c = t + 1
            run = 0
        t += 1
    primitives = [x for x in sorted(set(generators))
                  if not any(bits[i] and bits[x-i] for i in range(1,x))]
    return dict(m=m, e=len(primitives), c=c, g=g, n=c-g,
                W=len(primitives)*(c-g)-c, minimal_generators=primitives)


class WilfTests(unittest.TestCase):
    def test_epoch_example(self):
        cert, stats = compute((5, 7, 9))
        self.assertEqual(cert["apery"], [0, 16, 7, 18, 9])
        self.assertEqual((stats["g"], stats["c"], stats["n"], stats["W"]), (8, 14, 6, 4))

    def test_independent_exhaustive(self):
        for k in range(1, 5):
            for a in combinations(range(1, 15), k):
                if gcd(*a) == 1:
                    self.assertEqual(compute(a)[1], direct(a), a)

    def test_equality_controls(self):
        for m in range(2, 24):
            self.assertEqual(compute([m, 4*m+1])[1]["W"], 0)
            self.assertEqual(compute(range(m, 2*m))[1]["W"], 0)

    def test_false_certificate(self):
        cert, _ = compute((5, 7, 9))
        bad = deepcopy(cert)
        bad["apery_predecessors"][1] = [0, 7]
        with self.assertRaises(ValueError):
            verify(bad)
        # This table has legal paths but ignores a genuinely shorter one.
        long = dict(generators=[3, 4, 5], apery=[0, 10, 5],
                    apery_predecessors=[None, [2, 5], [0, 5]])
        with self.assertRaisesRegex(ValueError, "shorter route"):
            verify(long)

    def test_non_coprime(self):
        with self.assertRaises(ValueError):
            compute([6, 10, 14])


if __name__ == "__main__":
    unittest.main()
