"""Exact arithmetic for Wilf's numerical-semigroup conjecture (Python 3.10+)."""
import argparse
import heapq
import json
from itertools import combinations
from math import gcd


def clean(generators):
    a = tuple(generators)
    if not a or any(type(x) is not int or x <= 0 for x in a) or gcd(*a) != 1:
        raise ValueError("expected positive integer generators with gcd 1")
    return tuple(sorted(set(a)))


def apery(a):
    """Shortest distances from residue 0; each edge adds a generator."""
    m = a[0]
    w = [None] * m
    pred = [None] * m
    w[0] = 0
    queue = [(0, 0)]
    while queue:
        d, r = heapq.heappop(queue)
        if d != w[r]:
            continue
        for x in a[1:]:
            s = (r + x) % m
            if w[s] is None or d + x < w[s]:
                w[s] = d + x
                pred[s] = [r, x]
                heapq.heappush(queue, (w[s], s))
    return w, pred


def verify(certificate):
    """Check shortest-path witnesses without running Dijkstra."""
    a = clean(certificate["generators"])
    m = a[0]
    w = certificate["apery"]
    pred = certificate["apery_predecessors"]
    if len(w) != m or len(pred) != m or w[0] != 0 or pred[0] is not None:
        raise ValueError("wrong Apéry table dimensions or zero entry")
    if any(type(v) is not int or v < 0 or v % m != r for r, v in enumerate(w)):
        raise ValueError("invalid residue or distance")
    for r, v in enumerate(w):
        if r > 0:
            step = pred[r]
            if not isinstance(step, (list, tuple)) or len(step) != 2:
                raise ValueError(f"missing predecessor at residue {r}")
            s, x = step
            if (type(s) is not int or not 0 <= s < m or type(x) is not int
                    or x not in a or w[s] + x != v):
                raise ValueError(f"bad predecessor at residue {r}")
        if any(w[(r + x) % m] > v + x for x in a):
            raise ValueError(f"shorter route through residue {r}")
    return invariants(a, w)


def invariants(a, w):
    m = a[0]
    # Every non-m primitive belongs to Apéry. If an Apéry element splits,
    # each positive summand is itself in Apéry (else subtract m from the sum).
    positive = set(w) - {0}
    primitives = [m] + [x for x in a[1:] if x in positive
                        and not any(x - y in positive for y in positive)]
    c = max(w) - m + 1
    g = sum(v // m for v in w)
    n = c - g
    e = len(primitives)
    return dict(m=m, e=e, c=c, g=g, n=n, W=e*n-c, minimal_generators=primitives)


def compute(generators):
    a = clean(generators)
    w, pred = apery(a)
    cert = dict(generators=list(a), apery=w, apery_predecessors=pred)
    return cert, verify(cert)


def sweep():
    """Fixed clustered-offset family; not an exhaustive genus or multiplicity search."""
    best = None
    total = frontier = violations = 0
    for m in range(19, 56):
        for q in (1, 2, 3):
            for a, b, c, d in combinations(range(1, 13), 4):
                generators = (m, q*m+a, q*m+b, (q+1)*m+c, (q+1)*m+d)
                if gcd(*generators) != 1:
                    continue
                cert, s = compute(generators)
                total += 1
                if s["W"] < 0:
                    violations += 1
                    print(json.dumps(dict(certificate=cert, stats=s)))
                if (s["e"] == 5 and 3*s["e"] < m and s["g"] > 100
                        and s["c"] > 4*m and (s["c"] % m != 0 or s["g"] > 120)):
                    frontier += 1
                    key = (s["W"], m, generators)
                    if best is None or key < best[0]:
                        best = (key, cert, s)
    print(json.dumps(dict(tested=total, beyond_filters=frontier,
                          negative_margins=violations, best_stats=best[2] if best else None,
                          best_certificate=best[1] if best else None), indent=2))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="command", required=True)
    inspect = sub.add_parser("inspect")
    inspect.add_argument("generators", nargs="+", type=int)
    inspect.add_argument("--certificate", action="store_true")
    check = sub.add_parser("verify")
    check.add_argument("certificate")
    sub.add_parser("sweep")
    args = p.parse_args()
    if args.command == "inspect":
        cert, stats = compute(args.generators)
        print(json.dumps(cert if args.certificate else stats, indent=2))
    elif args.command == "verify":
        with open(args.certificate) as f:
            print(json.dumps(verify(json.load(f)), indent=2))
    else:
        sweep()


if __name__ == "__main__":
    main()
