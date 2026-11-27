/* Exhaustive tile check for a fixed multiplicity (NOTE.md, Section 14).
 *
 *   ./tile_shift m k [part nparts]
 *
 * For every k-subset r = {r_1 < ... < r_k} of {1, ..., m-1} (optionally only those whose index is
 * congruent to `part` modulo `nparts`) it enumerates EVERY set B with
 *   (i)   B a down-set in N^k of size m,
 *   (ii)  x -> r.x mod m a bijection B -> Z/m,
 *   (iii) the unit vectors e_1, ..., e_k in B.
 * The Apéry normal-form down-set of a numerical semigroup <m, a_1, ..., a_k> (m the multiplicity,
 * k + 1 the embedding dimension, r_i = a_i mod m) is such a set, for any monomial tie-break.
 *
 * For each tile: mu(t) = sum over the directions i with t + e_i not in B of (t_i + 1), and
 *
 *   e(theta) = [ (k+1) m (m-1)/2 - sum_t mu(t) * ((r.t + theta) mod m) ] / m,     theta = 0..m-1.
 *
 * Two tests.
 *   strong:  e(theta) >= 0 for every theta                      (false in general, first at m = 14)
 *   tile bound:  for every maximal cell z of B,
 *                 w(z) = e(m - 1 - (r.z mod m)) + (km - N_max) >= 0,
 *            N_max the sum of mu over the maximal cells.  By Proposition T of NOTE.md the Wilf
 *            number of a semigroup with this tile whose largest Apéry element is the cell z is
 *            at least w(z).
 *   Phi:     Phi(B) = m(km - N_max) + sum_j j*mu_(j) - (k-1)m(m-1)/2 >= 0, the mu values sorted
 *            decreasing (Conjecture Phi; it depends on the shape only and implies the tile bound).
 * Output: residue sets, tiles, failures of each test, the least e and the least w, one tile attaining
 * the least w (line ARGMIN), and the number of tiles with Phi < 0 and the least Phi (line PHI).
 * Exact integer arithmetic.
 *
 * Enumeration.  A cell x of a down-set of size m has prod (x_i + 1) <= m; these cells are the
 * candidates, listed by total degree and then lexicographically, so every cell below a candidate
 * comes earlier.  Candidates are decided in that order: put into B, or excluded together with all
 * cells above them.  When a cell is put into B, every other undecided cell with the same residue
 * is excluded.  A branch is abandoned when some residue has neither a cell in B nor a candidate
 * left.  Each tile is produced exactly once (the decisions are determined by B).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXK 40
#define MAXM 64
#define MAXZ 200000

static int k, m;
static int nz;
static signed char (*Z)[MAXK];
static int (*up)[MAXK], (*dn)[MAXK];
static int *res, *deg;
static unsigned char *state;            /* 0 undecided, 1 in B, 2 excluded */
static int *stack, sp;
static int alive[MAXM], used[MAXM];
static int unit_idx[MAXK];
static unsigned char *is_unit;
static int r[MAXK];
static int dead_residues;               /* residues with used = 0 and alive = 0 */

static long long n_sets, n_tiles, n_fail, n_tight, min_e = 1LL << 60, max_e = -(1LL << 60);
static long long n_fail_w, n_w0, min_w = 1LL << 60, printed;
static char best_buf[32768];
static long long phi_neg, phi_min = 1LL << 60;

/* ---- candidates ---- */
static int cmp_cells(const void *a, const void *b) {
    const signed char *x = a, *y = b;
    int dx = 0, dy = 0;
    for (int i = 0; i < k; i++) { dx += x[i]; dy += y[i]; }
    if (dx != dy) return dx - dy;
    for (int i = 0; i < k; i++) if (x[i] != y[i]) return x[i] - y[i];
    return 0;
}
static signed char cur[MAXK];
static void gen(int i, int prod) {
    if (i == k) {
        if (nz >= MAXZ) { fprintf(stderr, "too many candidates\n"); exit(1); }
        memcpy(Z[nz++], cur, MAXK);
        return;
    }
    for (int v = 0; prod * (v + 1) <= m; v++) { cur[i] = (signed char)v; gen(i + 1, prod * (v + 1)); }
    cur[i] = 0;
}
static int find(const signed char *x) {
    int lo = 0, hi = nz - 1;
    while (lo <= hi) {
        int mid = (lo + hi) / 2, c = cmp_cells(Z[mid], x);
        if (c == 0) return mid;
        if (c < 0) lo = mid + 1; else hi = mid - 1;
    }
    return -1;
}
static void build_candidates(void) {
    Z = calloc(MAXZ, sizeof *Z);
    nz = 0;
    gen(0, 1);
    qsort(Z, nz, sizeof *Z, cmp_cells);
    up = malloc(sizeof(*up) * nz); dn = malloc(sizeof(*dn) * nz);
    res = malloc(sizeof(int) * nz); deg = malloc(sizeof(int) * nz);
    state = malloc(nz); stack = malloc(sizeof(int) * nz); is_unit = calloc(nz, 1);
    for (int j = 0; j < nz; j++) {
        signed char y[MAXK];
        deg[j] = 0;
        for (int i = 0; i < k; i++) deg[j] += Z[j][i];
        for (int i = 0; i < k; i++) {
            memcpy(y, Z[j], MAXK); y[i]++;
            up[j][i] = find(y);
            if (Z[j][i] > 0) { memcpy(y, Z[j], MAXK); y[i]--; dn[j][i] = find(y); if (dn[j][i] < 0) { fprintf(stderr, "candidates not a down-set\n"); exit(1); } }
            else dn[j][i] = -1;
        }
        if (deg[j] == 1) for (int i = 0; i < k; i++) if (Z[j][i] == 1) { unit_idx[i] = j; is_unit[j] = 1; }
    }
}

/* ---- search ---- */
static void kill_up(int a) {            /* exclude a and every candidate above it */
    if (state[a] != 0) return;          /* in B cannot happen above an undecided cell; 2 = already done */
    state[a] = 2;
    stack[sp++] = a;
    if (--alive[res[a]] == 0 && !used[res[a]]) dead_residues++;
    for (int i = 0; i < k; i++) if (up[a][i] >= 0) kill_up(up[a][i]);
}
static void undo_to(int mark) {
    while (sp > mark) {
        int a = stack[--sp];
        state[a] = 0;
        if (alive[res[a]]++ == 0 && !used[res[a]]) dead_residues--;
    }
}

static int mu[MAXM];
static long long ee[MAXM];
static void print_tile(const char *tag, long long val) {
    if (printed++ >= 200) return;
    printf("%s m=%d r=", tag, m);
    for (int i = 0; i < k; i++) printf("%d ", r[i]);
    printf("value=%lld B=", val);
    for (int j = 0; j < nz; j++) if (state[j] == 1) { printf("("); for (int i = 0; i < k; i++) printf("%d%s", Z[j][i], i + 1 < k ? "," : ")"); }
    printf("\n");
}
static void finish(void) {
    n_tiles++;
    long long nmax = 0;
    static int maxres[MAXM];
    int nmaxcells = 0;
    for (int j = 0; j < nz; j++) if (state[j] == 1) {
        int s = 0, exits = 0;
        for (int i = 0; i < k; i++) if (up[j][i] < 0 || state[up[j][i]] != 1) { s += Z[j][i] + 1; exits++; }
        mu[res[j]] = s;
        if (exits == k) { nmax += s; maxres[nmaxcells++] = res[j]; }
    }
    long long tot = 0, summu = 0;
    for (int v = 0; v < m; v++) { tot += (long long)mu[v] * v; summu += mu[v]; }
    if (summu != (long long)k * m) { fprintf(stderr, "sum of mu is not km\n"); exit(1); }
    long long num = (long long)(k + 1) * m * (m - 1) / 2 - tot;
    if (num % m) { fprintf(stderr, "e(0) not an integer\n"); exit(1); }
    long long e = num / m, lo = e, hi = e;
    ee[0] = e;
    for (int th = 1; th < m; th++) { e += mu[m - th] - k; ee[th] = e; if (e < lo) lo = e; if (e > hi) hi = e; }
    if (lo < 0) { n_fail++; print_tile("STRONG-FAIL", lo); }
    if (lo == 0) n_tight++;
    if (lo < min_e) min_e = lo;
    if (hi > max_e) max_e = hi;
    /* tile bound: w(z) = e(m-1-res(z)) + km - N_max over the maximal cells z */
    long long wlo = 1LL << 60;
    for (int a = 0; a < nmaxcells; a++) {
        long long wz = ee[m - 1 - maxres[a]] + (long long)k * m - nmax;
        if (wz < wlo) wlo = wz;
    }
    {   /* Conjecture Phi: Phi(B) = m(km - N_max) + sum_j j*mu_(j) - (k-1)m(m-1)/2, mu_(0) >= mu_(1) >= ...
           By the rearrangement inequality Phi <= m * w, so Phi >= 0 implies w >= 0 (NOTE.md, Section 14). */
        static int cntv[MAXM * MAXM]; int mx = 0;
        for (int v = 0; v < m; v++) { cntv[mu[v]]++; if (mu[v] > mx) mx = mu[v]; }
        long long R = 0; int j = 0;
        for (int val = mx; val >= 0; val--) while (cntv[val]) { R += (long long)j * val; j++; cntv[val]--; }
        long long phi = (long long)m * ((long long)k * m - nmax) + R - (long long)(k - 1) * m * (m - 1) / 2;
        if (phi > (long long)m * wlo) { fprintf(stderr, "Phi > m*w: rearrangement violated\n"); exit(1); }
        if (phi < 0) { phi_neg++; print_tile("PHI-NEG", phi); }
        if (phi < phi_min) phi_min = phi;
    }
    if (wlo < 0) { n_fail_w++; print_tile("BOUND-FAIL", wlo); }
    if (wlo == 0) n_w0++;
    if (wlo < min_w) {                  /* remember one tile attaining the least w */
        min_w = wlo;
        int len = snprintf(best_buf, sizeof best_buf, "ARGMIN m=%d k=%d w=%lld min_e=%lld N_nonmax=%lld r=", m, k, wlo, lo, (long long)k * m - nmax);
        for (int i = 0; i < k && len < (int)sizeof best_buf - 64; i++) len += snprintf(best_buf + len, sizeof best_buf - len, "%d ", r[i]);
        len += snprintf(best_buf + len, sizeof best_buf - len, "B=");
        for (int j = 0; j < nz && len < (int)sizeof best_buf - 256; j++) if (state[j] == 1) {
            len += snprintf(best_buf + len, sizeof best_buf - len, "(");
            for (int i = 0; i < k; i++) len += snprintf(best_buf + len, sizeof best_buf - len, "%d%s", Z[j][i], i + 1 < k ? "," : ")");
        }
    }
}

static void rec(int j, int size) {
    if (size == m) { finish(); return; }
    while (j < nz && state[j] != 0) j++;
    if (j == nz) return;
    /* j is undecided: every cell below it is in B and its residue is free */
    int v = res[j], mark = sp;
    /* include j */
    state[j] = 1; used[v] = 1; alive[v]--;
    for (int a = j + 1; a < nz; a++) if (res[a] == v) kill_up(a);
    if (dead_residues == 0) rec(j + 1, size + 1);
    undo_to(mark);
    state[j] = 0; used[v] = 0; alive[v]++;
    /* exclude j (never a unit vector) */
    if (is_unit[j]) return;
    kill_up(j);
    if (dead_residues == 0) rec(j + 1, size);
    undo_to(mark);
}

static void run_residue_set(void) {
    n_sets++;
    memset(alive, 0, sizeof alive); memset(used, 0, sizeof used);
    for (int j = 0; j < nz; j++) {
        long long s = 0;
        for (int i = 0; i < k; i++) s += (long long)r[i] * Z[j][i];
        res[j] = (int)(s % m);
        state[j] = 0;
        alive[res[j]]++;
    }
    sp = 0; dead_residues = 0;
    for (int v = 0; v < m; v++) if (alive[v] == 0) dead_residues++;
    if (dead_residues == 0) rec(0, 0);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: tile_shift m k [part nparts]\n"); return 1; }
    m = atoi(argv[1]); k = atoi(argv[2]);
    int part = argc > 4 ? atoi(argv[3]) : 0, nparts = argc > 4 ? atoi(argv[4]) : 1;
    if (m < 2 || m >= MAXM || k < 1 || k > MAXK || k > m - 1) { fprintf(stderr, "need 2 <= m < %d, 1 <= k <= min(%d, m-1)\n", MAXM, MAXK); return 1; }
    build_candidates();
    long long index = 0;
    for (int i = 0; i < k; i++) r[i] = i + 1;
    for (;;) {
        if (index % nparts == part) run_residue_set();
        index++;
        int i = k - 1;
        while (i >= 0 && r[i] == m - k + i) i--;
        if (i < 0) break;
        r[i]++;
        for (int t = i + 1; t < k; t++) r[t] = r[t - 1] + 1;
    }
    if (n_tiles) printf("%s\n", best_buf);
    printf("PHI m=%d k=%d phi_neg=%lld phi_min=%lld\n", m, k, phi_neg, n_tiles ? phi_min : 0);
    printf("m=%d k=%d part=%d/%d candidates=%d residue_sets=%lld tiles=%lld strong_fail=%lld min_e=%lld bound_fail=%lld bound_zero=%lld min_w=%lld\n",
           m, k, part, nparts, nz, n_sets, n_tiles, n_fail, n_tiles ? min_e : 0, n_fail_w, n_w0, n_tiles ? min_w : 0);
    return 0;
}
