"""Independent re-check of tile_shift.c and of Proposition T (NOTE.md, Section 14).

Standard library only, exact integers.  Shares no code with tile_shift.c: tiles are found by a
different search, and e(theta) and the tile bound w are evaluated straight from their definitions.

    python3 -B tile_check.py tiles 2 11      # every tile for m = 2..11, all k; same PHI and m= lines as tile_shift
    python3 -B tile_check.py tiles 16 30 3   # only k = 3
    python3 -B tile_check.py brute 3 8       # the search against a brute-force list of all down-sets
    python3 -B tile_check.py semigroups 16   # Proposition T on every numerical semigroup of genus <= 16

A tile is (B, r): B a down-set in N^k with |B| = m, the unit vectors in B, r_1 < ... < r_k in
[1, m-1], and x -> r.x mod m a bijection B -> Z/m.
"""
import itertools
import sys

sys.setrecursionlimit(100000)


def candidates(k, m):
    """Cells that can occur in a down-set of size m: prod (z_i + 1) <= m.  Degree, then lex."""
    out = []

    def rec(i, cur, prod):
        if i == k:
            out.append(tuple(cur))
            return
        v = 0
        while prod * (v + 1) <= m:
            cur.append(v)
            rec(i + 1, cur, prod * (v + 1))
            cur.pop()
            v += 1

    rec(0, [], 1)
    out.sort(key=lambda z: (sum(z), z))
    return out


def tiles(k, m, r, need_units=True):
    """Every tile for the residue vector r, by deciding the candidate cells in order."""
    Z = candidates(k, m)
    idx = {z: j for j, z in enumerate(Z)}
    res = [sum(ri * zi for ri, zi in zip(r, z)) % m for z in Z]
    lower = [[idx[z[:i] + (z[i] - 1,) + z[i+1:]] for i in range(k) if z[i] > 0] for z in Z]
    byres = [[] for _ in range(m)]
    for j, v in enumerate(res):
        byres[v].append(j)
    state = [0] * len(Z)                      # 0 undecided, 1 in B, 2 not in B
    used = [False] * m
    units = {idx[tuple(1 if a == i else 0 for a in range(k))] for i in range(k)}
    found = []

    def rec(j, size):
        if size == m:
            found.append(frozenset(Z[a] for a in range(len(Z)) if state[a] == 1))
            return
        if j == len(Z):
            return
        if all(state[a] == 1 for a in lower[j]) and not used[res[j]]:
            state[j] = 1
            used[res[j]] = True
            rec(j + 1, size + 1)
            used[res[j]] = False
            state[j] = 0
        if need_units and j in units:
            return
        if not used[res[j]]:                  # the residue must still be reachable later
            if not any(a > j and all(state[b] != 2 for b in lower[a]) for a in byres[res[j]]):
                return
        state[j] = 2
        rec(j + 1, size)
        state[j] = 0

    rec(0, 0)
    return found


def profile(B, k, m, r):
    """(min e, min w) from the definitions.  rho(t) = r.t mod m,
    mu(t) = sum over i with t + e_i not in B of (t_i + 1),
    e(theta) = [(k+1) m (m-1)/2 - sum_t mu(t) ((rho(t) + theta) mod m)] / m,
    w = (km - N_max) + min over maximal cells z of e(m - 1 - rho(z))."""
    rho = {t: sum(ri * ti for ri, ti in zip(r, t)) % m for t in B}
    assert len(set(rho.values())) == m
    exits = {t: [i for i in range(k) if t[:i] + (t[i] + 1,) + t[i+1:] not in B] for t in B}
    mu = {t: sum(t[i] + 1 for i in exits[t]) for t in B}
    assert sum(mu.values()) == k * m
    e = []
    for theta in range(m):
        num = (k + 1) * m * (m - 1) // 2 - sum(mu[t] * ((rho[t] + theta) % m) for t in B)
        assert num % m == 0
        e.append(num // m)
    maximal = [t for t in B if len(exits[t]) == k]
    nmax = sum(mu[t] for t in maximal)
    w = k * m - nmax + min(e[m - 1 - rho[z]] for z in maximal)
    return min(e), w


def phi(B, k, m):
    """Conjecture Phi: m(km - N_max) + sum_j j * mu_(j) - (k-1) m (m-1)/2, mu sorted decreasing."""
    exits = {t: [i for i in range(k) if t[:i] + (t[i] + 1,) + t[i+1:] not in B] for t in B}
    mu = sorted((sum(t[i] + 1 for i in exits[t]) for t in B), reverse=True)
    nmax = sum(sum(t[i] + 1 for i in exits[t]) for t in B if len(exits[t]) == k)
    return m * (k * m - nmax) + sum(j * v for j, v in enumerate(mu)) - (k - 1) * m * (m - 1) // 2


def scan_tiles(m0, m1, ks=None):
    for m in range(m0, m1 + 1):
        for k in (ks if ks else range(1, m)):
            sets = nt = sf = bf = bz = pn = 0
            mine = minw = minphi = None
            for r in itertools.combinations(range(1, m), k):
                sets += 1
                for B in tiles(k, m, r):
                    nt += 1
                    lo, w = profile(B, k, m, r)
                    sf += lo < 0
                    bf += w < 0
                    bz += w == 0
                    mine = lo if mine is None else min(mine, lo)
                    minw = w if minw is None else min(minw, w)
                    ph = phi(B, k, m)
                    assert ph <= m * w                    # rearrangement: Phi <= m * w
                    pn += ph < 0
                    minphi = ph if minphi is None else min(minphi, ph)
            print("PHI m=%d k=%d phi_neg=%d phi_min=%s" % (m, k, pn, minphi if minphi is not None else 0))
            print("m=%d k=%d residue_sets=%d tiles=%d strong_fail=%d min_e=%s bound_fail=%d bound_zero=%d min_w=%s"
                  % (m, k, sets, nt, sf, mine, bf, bz, minw), flush=True)


def brute(k, m):
    """The search of `tiles` against the list of all down-sets of size m (no unit-vector condition)."""
    from pseudo_tiles import downsets
    ds = downsets(k, m)
    total = 0
    for r in itertools.product(range(1, m), repeat=k):
        a = set(tiles(k, m, r, need_units=False))
        b = {B for B in ds if len({sum(ri * xi for ri, xi in zip(r, x)) % m for x in B}) == m}
        assert a == b, r
        total += len(a)
    print("brute k=%d m=%d: %d (down-set, residue vector) pairs, search and brute force agree" % (k, m, total))


def semigroups(G):
    """Proposition T on every numerical semigroup of genus <= G with e >= 2:
    W = sum_t mu(t) delta(t) + e(theta*), and W >= w."""
    from apery_downset import normal_forms
    count = 0
    least = None
    stack = [((1,), 1)]
    while stack:
        gaps, F = stack.pop()
        gapset = set(gaps)
        inS = lambda s: s >= 0 and s not in gapset
        m = next(x for x in range(1, F + 3) if x not in gapset)
        c = F + 1
        gens = [x for x in range(1, c + m + 1) if inS(x) and not any(inS(y) and inS(x - y) for y in range(1, x))]
        if len(gaps) < G:
            for x in range(F + 1, F + m + 1):
                if not any(inS(y) and inS(x - y) for y in range(1, x)):
                    stack.append((tuple(sorted(gaps + (x,))), x))
        if len(gens) < 2:
            continue
        a = tuple(gens[1:])
        k = len(a)
        W = (k + 1) * (c - len(gaps)) - c
        for order in ("deglex", "lex"):
            w_ap, nf = normal_forms(m, a, order)
            B = set(nf)
            wt = {x: w_ap[i] for i, x in enumerate(nf)}
            M = max(w_ap)
            r = tuple(ai % m for ai in a)
            rho = {t: wt[t] % m for t in B}
            exits = {t: [i for i in range(k) if t[:i] + (t[i] + 1,) + t[i+1:] not in B] for t in B}
            mu = {t: sum(t[i] + 1 for i in exits[t]) for t in B}
            theta = m - 1 - M % m
            num = (k + 1) * m * (m - 1) // 2 - sum(mu[t] * ((rho[t] + theta) % m) for t in B)
            assert num % m == 0
            e_star = num // m
            delta = {t: (M - wt[t]) // m for t in B}
            assert W == sum(mu[t] * delta[t] for t in B) + e_star, gens
            lo, w = profile(B, k, m, r)
            assert W >= w, gens
            if least is None or W - w < least[0]:
                least = (W - w, gens, order)
        count += 1
    print("semigroups of genus <= %d with e >= 2: %d; W = sum mu*delta + e(theta*) and W >= w on all, "
          "for deglex and lex normal forms; least W - w = %d at %s (%s)" % (G, count, least[0], least[1], least[2]))


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "tiles":                    # tiles m0 m1 [k ...]
        scan_tiles(int(sys.argv[2]), int(sys.argv[3]), [int(v) for v in sys.argv[4:]] or None)
    elif mode == "brute":
        brute(int(sys.argv[2]), int(sys.argv[3]))
    elif mode == "semigroups":
        semigroups(int(sys.argv[2]))
    else:
        raise SystemExit("usage: tile_check.py tiles m0 m1 [k ...] | brute k m | semigroups G")
