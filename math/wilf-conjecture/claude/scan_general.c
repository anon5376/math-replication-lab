/* Theorem C and the tile bounds (NOTE.md) for any embedding dimension e = k + 1, 2 <= k <= 8.  Exact 64-bit integers.
 *
 *   ./scan_general ray k m0 m1 Q    generators m and Q*m + b for every k-subset b of [1, m-1]
 *   ./scan_general box k m0 m1 K    every k-subset of (m, K*m] with no multiple of m
 *
 * A list is counted only if its embedding dimension is exactly k + 1.  For each such semigroup:
 * Apéry table by relaxation; graded-lex normal forms (minimal length); the down-set property and
 * Theorem A (2mW = 2*sum D(top) - (k-1)m(m-1)) are asserted; then
 *     C = m((k+1)m + k - 1) - 2 * sum over Apéry w >= c of (l(w) + k)(w - c + 1)   (= 2m * Theorem C bound)
 *     G : d(d-1) <= (k-1)(m + 1 - 2d),  d = number of Apéry elements >= c          (Corollary G1)
 * and 2mW >= C is asserted.  Also (NOTE.md, Section 14), with N_T, N_nonmax the numbers of chain-top
 * incidences on cells >= c and on non-maximal cells, and e(theta) the shift function of the tile:
 *     PP    = 2m * [ (km - N_T) + e(theta*) ]        (C'': W >= this; Conjecture C implies PP >= 0)
 *     Tstar = 2m * [ N_nonmax + e(theta*) ]          (the tile bound w at the true largest Apéry element)
 *     Tmin  = 2m * min over maximal cells z of [ N_nonmax + e(theta_z) ]     (= 2m * w(B, r))
 * with 2mW >= PP >= C and PP >= Tstar asserted (Tmin <= Tstar since z = x* is allowed).  Output per multiplicity:
 * count, how many have G, how many have C < 0 (a failure of Conjecture C), W < 0 (a Wilf
 * counterexample), least W, least C with its semigroup; then how many have PP, Tstar, Tmin < 0 and
 * the least value of each with a semigroup attaining it.
 * Build: gcc -O2 -o scan_general scan_general.c        Requires m <= 255.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXM 256
#define MAXK 8
typedef unsigned long long u64;
static int m, k;
static long w[MAXM];
static int nf[MAXM][MAXK], order_[MAXM], mu[MAXM];
#define HS 2048
static u64 hkey[HS]; static int hval[HS]; static char hused[HS];

static inline u64 pack(const int *x) { u64 v = 0; for (int i = 0; i < k; i++) v |= (u64)x[i] << (8 * i); return v; }
static inline unsigned hh(u64 key) { return (unsigned)((key * 0x9E3779B97F4A7C15ULL) >> 53); }
static inline void hput(u64 key, int val) {
    unsigned h = hh(key);
    while (hused[h]) h = (h + 1) & (HS - 1);
    hused[h] = 1; hkey[h] = key; hval[h] = val;
}
static inline int hget(u64 key) {
    unsigned h = hh(key);
    while (hused[h]) { if (hkey[h] == key) return hval[h]; h = (h + 1) & (HS - 1); }
    return -1;
}
static int apery(const long *a) {
    for (int r = 0; r < m; r++) w[r] = -1;
    w[0] = 0;
    for (int changed = 1; changed;) {
        changed = 0;
        for (int r = 0; r < m; r++) if (w[r] >= 0)
            for (int i = 0; i < k; i++) {
                int s = (int)((r + a[i]) % m);
                long v = w[r] + a[i];
                if (w[s] < 0 || v < w[s]) { w[s] = v; changed = 1; }
            }
    }
    for (int r = 0; r < m; r++) if (w[r] < 0) return 0;
    return 1;
}
static int cmp_w(const void *p, const void *q) { long d = w[*(const int *)p] - w[*(const int *)q]; return d < 0 ? -1 : d > 0; }
static int deglex_less(const int *x, const int *y) {
    int dx = 0, dy = 0;
    for (int i = 0; i < k; i++) { dx += x[i]; dy += y[i]; }
    if (dx != dy) return dx < dy;
    for (int i = 0; i < k; i++) if (x[i] != y[i]) return x[i] < y[i];
    return 0;
}

static long cnt, cntG, cntCneg, cntWneg, bestW, bestC, bestC_W;
static long cntPP, cntTs, cntTm, bestPP, bestTs, bestTm, bestPP_W, bestTm_W;
static long bestPPa[MAXK], bestTsa[MAXK], bestTma[MAXK];
static long ee[MAXM];
static long bestWa[MAXK], bestCa[MAXK];

static void consider(const long *a) {
    if (!apery(a)) return;
    for (int i = 0; i < k; i++) {
        if (w[a[i] % m] != a[i]) return;
        for (int r = 1; r < m; r++) {
            long rest = a[i] - w[r];
            if (rest > 0 && w[rest % m] == rest) return;
        }
    }
    long M = 0, g = 0;
    for (int r = 0; r < m; r++) { if (w[r] > M) M = w[r]; g += w[r] / m; }
    long c = M - m + 1, W = (long)(k + 1) * (c - g) - c;
    cnt++;
    for (int r = 0; r < m; r++) order_[r] = r;
    qsort(order_, m, sizeof(int), cmp_w);
    memset(hused, 0, sizeof hused);
    for (int j = 0; j < m; j++) {
        int r = order_[j];
        if (r == 0) { memset(nf[0], 0, sizeof nf[0]); hput(0, 0); continue; }
        int have = 0, best[MAXK];
        for (int i = 0; i < k; i++) {
            int s = (int)(((r - a[i]) % m + m) % m);
            if (w[s] + a[i] != w[r]) continue;
            int cand[MAXK];
            memcpy(cand, nf[s], sizeof cand);
            cand[i]++;
            if (!have || deglex_less(cand, best)) { memcpy(best, cand, sizeof best); have = 1; }
        }
        if (!have) { fprintf(stderr, "no predecessor\n"); exit(1); }
        memcpy(nf[r], best, sizeof best);
        hput(pack(best), r);
    }
    memset(mu, 0, sizeof(int) * m);
    long sumD = 0;
    for (int r = 0; r < m; r++)
        for (int i = 0; i < k; i++) {
            int t[MAXK];
            memcpy(t, nf[r], sizeof t);
            if (t[i]) { t[i]--; if (hget(pack(t)) < 0) { fprintf(stderr, "not a down-set\n"); exit(1); } t[i]++; }
            int top = r;
            for (;;) { t[i]++; int s = hget(pack(t)); if (s < 0) break; top = s; }
            mu[top]++;
            sumD += M - w[top];
        }
    if (2 * m * W != 2 * sumD - (long)(k - 1) * m * (m - 1)) { fprintf(stderr, "Theorem A fails\n"); exit(1); }
    long sharp = 0; int d = 0;
    for (int r = 0; r < m; r++) if (M - w[r] < m) {
        int deg = 0;
        for (int i = 0; i < k; i++) deg += nf[r][i];
        if (mu[r] != deg + k) { fprintf(stderr, "top-window cell not maximal\n"); exit(1); }
        d++; sharp += (long)mu[r] * (w[r] - c + 1);
    }
    long C = (long)m * ((long)(k + 1) * m + k - 1) - 2 * sharp;
    if (2 * m * W < C) { fprintf(stderr, "Theorem C violated\n"); exit(1); }
    /* C'' : 2m * [ (km - N_T) + e(theta*) ];  T* : 2m * [ N_nonmax + e(theta*) ];  Tmin: min over maximal z */
    {
        long NT = 0, Nnon = 0, sumMuDb = 0;
        static int ismax[MAXM], resmu[MAXM];
        long rstar = M % m;
        for (int r = 0; r < m; r++) {
            int t[MAXK]; memcpy(t, nf[r], sizeof t);
            int ex = 0;
            for (int i = 0; i < k; i++) { t[i]++; if (hget(pack(t)) < 0) ex++; t[i]--; }
            ismax[r] = (ex == k);
            if (!ismax[r]) Nnon += mu[r];
            if (M - w[r] < m) NT += mu[r];
            sumMuDb += (long)mu[r] * ((M - w[r]) % m);
            resmu[r] = mu[r];            /* the cell of residue r */
        }
        long base = (long)(k - 1) * m * (m - 1);
        long PP = 2 * ((long)m * ((long)k * m - NT) + sumMuDb) - base;
        long Ts = 2 * ((long)m * Nnon + sumMuDb) - base;
        if (!(2 * m * W >= PP && PP >= Ts && PP >= C)) { fprintf(stderr, "C'' ordering violated\n"); exit(1); }
        /* e(theta), theta = 0..m-1, with m*e(theta) = (k+1)m(m-1)/2 - sum mu*((r+theta) mod m) */
        long tot = 0; for (int r = 0; r < m; r++) tot += (long)resmu[r] * r;
        long num = (long)(k + 1) * m * (m - 1) / 2 - tot;
        if (num % m) { fprintf(stderr, "e(0) not integral\n"); exit(1); }
        ee[0] = num / m;
        for (int th = 1; th < m; th++) ee[th] = ee[th - 1] + resmu[m - th] - k;
        if (2 * m * (Nnon + ee[m - 1 - rstar]) != Ts) { fprintf(stderr, "e(theta*) mismatch\n"); exit(1); }
        long Tm = 1L << 60;
        for (int r = 0; r < m; r++) if (ismax[r]) { long v = 2L * m * (Nnon + ee[m - 1 - r]); if (v < Tm) Tm = v; }
        if (PP < 0) cntPP++;
        if (Ts < 0) cntTs++;
        if (Tm < 0) cntTm++;
        if (PP < bestPP) { bestPP = PP; bestPP_W = W; memcpy(bestPPa, a, sizeof(long) * k); }
        if (Ts < bestTs) { bestTs = Ts; memcpy(bestTsa, a, sizeof(long) * k); }
        if (Tm < bestTm) { bestTm = Tm; bestTm_W = W; memcpy(bestTma, a, sizeof(long) * k); }
    }
    if ((long)d * (d - 1) <= (long)(k - 1) * (m + 1 - 2 * d)) cntG++;
    if (C < 0) cntCneg++;
    if (W < 0) { cntWneg++; printf("WILF COUNTEREXAMPLE m=%d W=%ld gens:", m, W); for (int i = 0; i < k; i++) printf(" %ld", a[i]); printf("\n"); }
    if (W < bestW) { bestW = W; memcpy(bestWa, a, sizeof(long) * k); }
    if (C < bestC) { bestC = C; bestC_W = W; memcpy(bestCa, a, sizeof(long) * k); }
}

static long cur[MAXK], pool[4096]; static int npool;
static void rec(int depth, int start) {
    if (depth == k) { consider(cur); return; }
    for (int i = start; i <= npool - (k - depth); i++) { cur[depth] = pool[i]; rec(depth + 1, i + 1); }
}

int main(int argc, char **argv) {
    if (argc != 6) { fprintf(stderr, "usage: scan_general ray|box k m0 m1 Q|K\n"); return 2; }
    char mode = argv[1][0];
    k = atoi(argv[2]);
    int m0 = atoi(argv[3]), m1 = atoi(argv[4]);
    long P = atol(argv[5]);
    if (k < 2 || k > MAXK || m0 < 2 || m1 > 255) { fprintf(stderr, "need 2 <= k <= 8 and 2 <= m <= 255\n"); return 2; }
    long T = 0, TG = 0, TC = 0, TW = 0;
    for (m = m0; m <= m1; m++) {
        cnt = cntG = cntCneg = cntWneg = cntPP = cntTs = cntTm = 0; bestW = bestC = bestPP = bestTs = bestTm = 1L << 60;
        npool = 0;
        if (mode == 'r') { for (int b = 1; b < m; b++) pool[npool++] = P * m + b; }
        else { for (long x = m + 1; x <= P * m; x++) if (x % m) pool[npool++] = x; }
        if (npool >= k) rec(0, 0);
        T += cnt; TG += cntG; TC += cntCneg; TW += cntWneg;
        if (cnt) {
            printf("k=%d m=%d count=%ld G=%ld Cneg=%ld Wneg=%ld minW=%ld at [%d", k, m, cnt, cntG, cntCneg, cntWneg, bestW, m);
            for (int i = 0; i < k; i++) printf(",%ld", bestWa[i]);
            printf("] min(2m*Cbound)=%ld (W=%ld) at [%d", bestC, bestC_W, m);
            for (int i = 0; i < k; i++) printf(",%ld", bestCa[i]);
            printf("] PPneg=%ld Tsneg=%ld Tmneg=%ld min(2m*PP)=%ld (W=%ld) at [%d", cntPP, cntTs, cntTm, bestPP, bestPP_W, m);
            for (int i = 0; i < k; i++) printf(",%ld", bestPPa[i]);
            printf("] min(2m*Tstar)=%ld at [%d", bestTs, m);
            for (int i = 0; i < k; i++) printf(",%ld", bestTsa[i]);
            printf("] min(2m*Tmin)=%ld (W=%ld) at [%d", bestTm, bestTm_W, m);
            for (int i = 0; i < k; i++) printf(",%ld", bestTma[i]);
            printf("]\n");
        } else printf("k=%d m=%d count=0\n", k, m);
        fflush(stdout);
    }
    printf("total=%ld G=%ld Cneg=%ld Wneg=%ld\n", T, TG, TC, TW);
    return 0;
}
