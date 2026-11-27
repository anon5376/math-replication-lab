/* Bounded exhaustive scans with the criteria of NOTE.md evaluated on every semigroup.
 *
 *   ./scan_criteria box m0 m1 K qmin     {a1<a2<a3<a4} in (m, K*m], no a_i divisible by m
 *   ./scan_criteria pos m0 m1 Q qmin     a_i = Q*m + b_i, 1 <= b1<b2<b3<b4 <= m-1
 *                                        (Q = 1: every 4-subset of the open interval (m, 2m))
 *   ./scan_criteria rnd m0 m1 N qmin     N pseudo-random lists per m (fixed seed), a_i = q_i*m + b_i,
 *                                        q_i in {1,2}; a heuristic sample, not an exhaustive scan
 *
 * Only lists with embedding dimension exactly 5 and conductor c > qmin*m are counted.  For each:
 *   - Apéry table by relaxation, normal forms with the graded-lex tie-break (minimal length);
 *   - the down-set property and the identity  2mW = 2*sum D(top) - 3m(m-1)  are asserted;
 *   - type t (FGH covers t <= 4);
 *   - C  : 2*N0 <= 5m + 3                                   (Theorem C, k = 4)
 *   - C+ : 2m(4m - N0) - 3m(m-1) + 2R >= 0                  (Theorem C+, R = rearrangement sum)
 *   - S  : the same expression with N0 replaced by the mu-mass of ALL maximal cells of the
 *          down-set (a quantity of the shape alone; S <= C+ always)
 *   - P  : at most 2 Apéry elements >= c, i.e. at most 2 pseudo-Frobenius numbers in [c-m, c)
 *          (Corollary C2 with e = 5; it implies C when m >= 9, which is asserted)
 * and the bound  2mW >= [C+ left side]  is asserted.  Output per multiplicity: counts, the
 * least W, and the least value of the C+ bound (as the integer 2m*bound) with its semigroup.
 * Exact 64-bit integers.  Build: gcc -O2 -o scan_criteria scan_criteria.c
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXM 512
static int m;
static long w[MAXM];
static int nf[MAXM][4], order[MAXM], mu[MAXM];
#define HS 4096
static int hkey[HS], hval[HS];

static inline int pack(const int *x) { return x[0] | (x[1] << 8) | (x[2] << 16) | (x[3] << 24); }
static inline void hput(int key, int val) {
    unsigned h = ((unsigned)key * 2654435761u) >> 20;
    while (hkey[h] != -1) h = (h + 1) & (HS - 1);
    hkey[h] = key; hval[h] = val;
}
static inline int hget(int key) {
    unsigned h = ((unsigned)key * 2654435761u) >> 20;
    while (hkey[h] != -1) { if (hkey[h] == key) return hval[h]; h = (h + 1) & (HS - 1); }
    return -1;
}

static int apery(const long *a) {
    for (int r = 0; r < m; r++) w[r] = -1;
    w[0] = 0;
    for (int changed = 1; changed;) {
        changed = 0;
        for (int r = 0; r < m; r++) if (w[r] >= 0)
            for (int i = 0; i < 4; i++) {
                int s = (int)((r + a[i]) % m);
                long v = w[r] + a[i];
                if (w[s] < 0 || v < w[s]) { w[s] = v; changed = 1; }
            }
    }
    for (int r = 0; r < m; r++) if (w[r] < 0) return 0;
    return 1;
}

static int cmp_w(const void *p, const void *q) {
    long d = w[*(const int *)p] - w[*(const int *)q];
    return d < 0 ? -1 : d > 0;
}
static int cmp_desc(const void *p, const void *q) { return *(const int *)q - *(const int *)p; }

static int deglex_less(const int *x, const int *y) {
    int dx = x[0] + x[1] + x[2] + x[3], dy = y[0] + y[1] + y[2] + y[3];
    if (dx != dy) return dx < dy;
    for (int i = 0; i < 4; i++) if (x[i] != y[i]) return x[i] < y[i];
    return 0;
}

static long cnt, cnt_type5, cnt_notC, cnt_notC_type5, cnt_notCp, cnt_notCp_type5, cnt_notS, cnt_P, cnt_P_type5;
static long bestW, bestWa[4], bestB, bestBa[4], bestB_W, bestS, bestSa[4], bestS_W;
static int qmin;

static void consider(const long *a) {
    if (!apery(a)) return;
    for (int i = 0; i < 4; i++) {
        if (w[a[i] % m] != a[i]) return;
        for (int r = 1; r < m; r++) {
            long rest = a[i] - w[r];
            if (rest > 0 && w[rest % m] == rest) return;
        }
    }
    long M = 0, g = 0;
    for (int r = 0; r < m; r++) { if (w[r] > M) M = w[r]; g += w[r] / m; }
    long c = M - m + 1, W = 5 * (c - g) - c;
    if (c <= (long)qmin * m) return;
    cnt++;
    /* normal forms, graded-lex */
    for (int r = 0; r < m; r++) order[r] = r;
    qsort(order, m, sizeof(int), cmp_w);
    memset(hkey, -1, sizeof hkey);
    for (int j = 0; j < m; j++) {
        int r = order[j];
        if (r == 0) { nf[0][0] = nf[0][1] = nf[0][2] = nf[0][3] = 0; hput(0, 0); continue; }
        int have = 0, best[4] = {0, 0, 0, 0};
        for (int i = 0; i < 4; i++) {
            int s = (int)(((r - a[i]) % m + m) % m);
            if (w[s] + a[i] != w[r]) continue;
            int cand[4] = {nf[s][0], nf[s][1], nf[s][2], nf[s][3]};
            cand[i]++;
            if (!have || deglex_less(cand, best)) { memcpy(best, cand, sizeof best); have = 1; }
        }
        if (!have) { fprintf(stderr, "no predecessor\n"); exit(1); }
        memcpy(nf[r], best, sizeof best);
        hput(pack(best), r);
    }
    /* down-set check, chain tops, mu */
    memset(mu, 0, sizeof(int) * m);
    long sumD = 0;
    for (int r = 0; r < m; r++) {
        for (int i = 0; i < 4; i++) {
            if (nf[r][i]) {
                int y[4] = {nf[r][0], nf[r][1], nf[r][2], nf[r][3]};
                y[i]--;
                if (hget(pack(y)) < 0) { fprintf(stderr, "not a down-set\n"); exit(1); }
            }
            int t[4] = {nf[r][0], nf[r][1], nf[r][2], nf[r][3]}, top = r;
            for (;;) { t[i]++; int s = hget(pack(t)); if (s < 0) break; top = s; }
            mu[top]++;
            sumD += M - w[top];
        }
    }
    if (2 * m * W != 2 * sumD - 3L * m * (m - 1)) { fprintf(stderr, "identity fails\n"); exit(1); }
    long N0 = 0, Nmax = 0;
    int ttop = 0;
    for (int r = 0; r < m; r++) {
        int deg = nf[r][0] + nf[r][1] + nf[r][2] + nf[r][3];
        if (M - w[r] < m) { ttop++; N0 += mu[r]; if (mu[r] != deg + 4) { fprintf(stderr, "top-window cell not maximal\n"); exit(1); } }
        if (mu[r] == deg + 4) Nmax += mu[r];          /* maximal cell of the down-set */
    }
    static int srt[MAXM];
    memcpy(srt, mu, sizeof(int) * m);
    qsort(srt, m, sizeof(int), cmp_desc);
    long R = 0;
    for (int j = 0; j < m; j++) R += (long)j * srt[j];
    long boundC = 2L * m * (4L * m - N0) - 3L * m * (m - 1);       /* = 2m * (Theorem C bound) */
    long boundCp = boundC + 2 * R;                                 /* = 2m * (Theorem C+ bound) */
    long boundS = 2L * m * (4L * m - Nmax) - 3L * m * (m - 1) + 2 * R;   /* shape-only */
    if (2 * m * W < boundCp || boundCp < boundS) { fprintf(stderr, "bound violated\n"); exit(1); }
    if (boundS < 0) cnt_notS++;
    if (boundS < bestS) { bestS = boundS; memcpy(bestSa, a, sizeof bestSa); bestS_W = W; }
    /* type */
    int type = 0;
    for (int r = 0; r < m; r++) {
        int maximal = 1;
        for (int s = 0; s < m && maximal; s++) {
            long d = w[s] - w[r];
            if (d > 0 && d >= w[d % m]) maximal = 0;
        }
        type += maximal;
    }
    if (type >= 5) cnt_type5++;
    if (ttop <= 2) {
        cnt_P++; if (type >= 5) cnt_P_type5++;
        if (m >= 9 && boundC < 0) { fprintf(stderr, "Corollary C2 violated\n"); exit(1); }
    }
    if (boundC < 0) { cnt_notC++; if (type >= 5) cnt_notC_type5++; }
    if (boundCp < 0) { cnt_notCp++; if (type >= 5) cnt_notCp_type5++; }
    if (W < bestW) { bestW = W; memcpy(bestWa, a, sizeof bestWa); }
    if (boundCp < bestB) { bestB = boundCp; memcpy(bestBa, a, sizeof bestBa); bestB_W = W; }
}

int main(int argc, char **argv) {
    if (argc != 6) { fprintf(stderr, "usage: scan_criteria box|pos|rnd m0 m1 K|Q|N qmin\n"); return 2; }
    char mode = argv[1][0];
    int m0 = atoi(argv[2]), m1 = atoi(argv[3]);
    long P = atol(argv[4]);
    qmin = atoi(argv[5]);
    if (m1 > 255 || m0 < 2) { fprintf(stderr, "need 2 <= m <= 255 (exponents are packed in 8 bits)\n"); return 2; }
    long T = 0, T5 = 0, TnC5 = 0, TnCp = 0, TnCp5 = 0, TnS = 0, TP = 0, TP5 = 0;
    for (m = m0; m <= m1; m++) {
        cnt = cnt_type5 = cnt_notC = cnt_notC_type5 = cnt_notCp = cnt_notCp_type5 = cnt_notS = cnt_P = cnt_P_type5 = 0;
        bestW = bestB = bestS = 1L << 60;
        long a[4];
        if (mode == 'b') {
            long hi = P * m;
            for (a[0] = m + 1; a[0] <= hi; a[0]++) { if (a[0] % m == 0) continue;
            for (a[1] = a[0] + 1; a[1] <= hi; a[1]++) { if (a[1] % m == 0) continue;
            for (a[2] = a[1] + 1; a[2] <= hi; a[2]++) { if (a[2] % m == 0) continue;
            for (a[3] = a[2] + 1; a[3] <= hi; a[3]++) { if (a[3] % m == 0) continue;
                consider(a); }}}}
        } else if (mode == 'r') {
            unsigned long long st = 88172645463325252ULL ^ (unsigned long long)m * 0x9E3779B97F4A7C15ULL;
            for (long it = 0; it < P; it++) {
                int b[4], ok = 1;
                for (int i = 0; i < 4; i++) {
                    st ^= st << 13; st ^= st >> 7; st ^= st << 17;        /* xorshift64 */
                    b[i] = 1 + (int)(st % (unsigned long long)(m - 1));
                    a[i] = (1 + (long)((st >> 40) & 1)) * m + b[i];
                }
                for (int i = 0; i < 4; i++) for (int j = 0; j < i; j++) if (a[i] == a[j]) ok = 0;
                if (ok) consider(a);
            }
        } else {
            int b[4];
            for (b[0] = 1; b[0] < m; b[0]++)
            for (b[1] = b[0] + 1; b[1] < m; b[1]++)
            for (b[2] = b[1] + 1; b[2] < m; b[2]++)
            for (b[3] = b[2] + 1; b[3] < m; b[3]++) {
                for (int i = 0; i < 4; i++) a[i] = P * m + b[i];
                if (a[0] <= m || a[3] <= m) continue;
                consider(a);
            }
        }
        T += cnt; T5 += cnt_type5; TnC5 += cnt_notC_type5; TnCp += cnt_notCp; TnCp5 += cnt_notCp_type5; TnS += cnt_notS; TP += cnt_P; TP5 += cnt_P_type5;
        if (cnt)
            printf("m=%d count=%ld type>=5=%ld P=%ld P&type>=5=%ld notC=%ld notC&type>=5=%ld notC+=%ld notC+&type>=5=%ld notS=%ld "
                   "minW=%ld at [%d,%ld,%ld,%ld,%ld] min(2m*C+bound)=%ld (W=%ld) at [%d,%ld,%ld,%ld,%ld] "
                   "min(2m*Sbound)=%ld (W=%ld) at [%d,%ld,%ld,%ld,%ld]\n",
                   m, cnt, cnt_type5, cnt_P, cnt_P_type5, cnt_notC, cnt_notC_type5, cnt_notCp, cnt_notCp_type5, cnt_notS,
                   bestW, m, bestWa[0], bestWa[1], bestWa[2], bestWa[3],
                   bestB, bestB_W, m, bestBa[0], bestBa[1], bestBa[2], bestBa[3],
                   bestS, bestS_W, m, bestSa[0], bestSa[1], bestSa[2], bestSa[3]);
        else printf("m=%d count=0\n", m);
        fflush(stdout);
    }
    printf("total=%ld type>=5=%ld P=%ld P&type>=5=%ld notC&type>=5=%ld notC+=%ld notC+&type>=5=%ld notS=%ld\n",
           T, T5, TP, TP5, TnC5, TnCp, TnCp5, TnS);
    return 0;
}
