# Simple negative roots at every rank for the pattern 132

For every integer $N\ge0$, the big-descent polynomial $B_N$ of 132-avoiding permutations has degree $\lfloor2(N-1)/3\rfloor$ at positive rank and has that many distinct, strictly negative real roots. At rank zero it is the constant 1. This proof concerns the single forbidden pattern 132. The write-up and certificates were developed with AI assistance. No priority claim is made. On October 13, 2026, Per Alexandersson's RealRooted project posted [an earlier computer-assisted proof of the same all-rank result](https://github.com/PerAlexandersson/RealRooted/blob/3599edd18d47d7fbc3253cdcba46982f1538261b/research/big-descents-132/README.md), using a cutoff of 100 and exact Sturm counts for ranks 0–99. The present package gives an end-to-end Lean verification of the literal permutation polynomial, using the effective argument below with cutoff 128.

Here $B_N(t)=\sum_{\pi}t^{\#\{i:\pi_i>\pi_{i+1}+1\}}$ over the actual 132-avoiders. The starting Lean commit proves the maximum decomposition for this definition, its exact degree and the three-cut integral for the same polynomial. Its earlier eventual theorem gives no numerical rank threshold. Below the analytic argument uses $N\ge128$. Integer certificates cover $0\le N\le127$. [Pinned starting commit](https://github.com/anon5376/math-replication-lab/tree/3b39ea25676433157c42bbfe36a2df1c18f33bd5/math/big-descents-132) · [Elizalde, Rivera and Zhuang, Conjecture 4.4](https://arxiv.org/html/2408.15111v2#S4.SS2).

## A coordinate for the four branch points

Write $s=1-t$. For $0<p<1$ set

$$
S=\sqrt{1+6p^2-3p^4},\quad z=\frac{1-p^2}{S+2p},
\quad h=p+z,\quad Q=1+3p^2 .
$$

Then $0<z<1$ and $p^2+4pz+z^2+3p^2z^2=1$. This follows by solving the quadratic in $z$ and rationalizing. Define

$$
\eta=\frac{(1-p^2)z^2 Q}{h^4},\quad s=1/\eta,\quad
r=\frac{(1-p)^2}{h^2},\quad R=\frac{(1+p)^2}{h^2},\quad
u=\frac{z^2(1+i\sqrt3p)^2}{h^2},\quad \mu=|u|.
$$

The conic-in-$z$ identity above also gives $1-\eta=(1-z^2)p^2(1+3z^2)/h^4$, hence $s>1$. The four numbers $(p-1)/h,(p+1)/h,z(1\pm i\sqrt3p)/h$ are the roots of $w^4-2w^3+2\eta w-\eta$. To check, multiply their two quadratic factors and apply that same identity. Squaring $1-sw^4=2w(1-sw^2)$ proves their squares are precisely the roots of the required quartic
$$
D_s(x)=(1-sx^2)^2-4x(1-sx)^2.
$$
They are distinct, $r<R$ and $\Im u>0$. These conditions identify the two real roots and the unique upper root in the starting theorem. The map $p\mapsto s$ is continuous with endpoint limits 1 and $+\infty$. Equality of two parameters $s$ gives equality of their unique upper roots, whose argument is $\theta=2\arctan(\sqrt3p)$. Since this argument is strictly increasing in $p$, the map $p\mapsto s$ is injective, and hence strictly increasing onto $(1,\infty)$.

Put $E=p(1-p)$ and $\rho=r/\mu$. Directly from the formulas,
$$
g=\frac{1-\mu/r}{E}=\frac{6(1+p)^2}{(2+S)(S+2p)},\qquad
\rho=\frac{(S+2p)^2}{(1+p)^2 Q}.
$$
For example $r-\mu=2p(p+2z-1)/h^2$, and $2-S=3(1-p^2)^2/(2+S)$. Use those identities before estimating the gap near the two ends.

## Real algebraic bounds

Use $\sigma=\mu/\Im u$, $P=|u-\eta|/\Im u$, $V_0=|u-\eta|/r$, $V_1=|u-\eta|/(r-\eta)$, and the amplitude $A$ denoted by [`Points.amplitudeRatio`](BigDescents132/InteriorGeometry.lean) in the Lean source. The following bounds hold on the full indicated closed ranges, with continuous extension where used.

| Range of $p$ | Bounds |
|---|---|
| $[0,1]$ | $g\ge4/3,\quad P\le3/2,\quad A\le5/8$ |
| $[0,1/4]$ | $p\sigma\le7/20$ |
| $[1/4,1]$ | $\sigma\le3/2$ |
| $[0,1/2]$ | $V_0\le5p$ |
| $[1/2,1]$ | $V_1\le7/2$ |
| $[19/20,1]$ | $V_1\le6/5$ |
| $[0,1/16]$ | $15\le(s-1)/p^3\le20$ |

The exact interval certificate is [all_ranks_geometry.py](all_ranks_geometry.py). Here are the formulas it encloses. Write $\beta=\eta/\mu=(1-p^2)/h^2$ and
$$
H=\frac{(2z+3pz^2-p)Q+6ph^2}{2\sqrt3h^2},\qquad
J=\frac{\rho(1-p)gQ+6p}{2\sqrt3}.
$$
Since $\cos\theta=(1-3p^2)/Q$ and $\sin\theta=2\sqrt3p/Q$, these are respectively $(\beta-\cos\theta)/\sin\theta$ and $(\rho-\cos\theta)/\sin\theta$. Consequently
$$
\sigma=\frac Q{2\sqrt3p},\quad P=\sqrt{1+H^2},\quad
V_0/p=(1-Eg)\frac{2\sqrt3 P}Q,\quad
V_1=\frac{2\sqrt3pP}{Q(\rho-\beta)}.
$$
The proven [`Points.amplitude_sq_le`](BigDescents132/AmplitudeBound.lean) gives $A^2\le(\rho/8)\sqrt{1+J^2}$. The last row of the table follows by enclosing
$$
\frac{s-1}{p^3}=\frac{(p+4z+3pz^2)(1+3z^2)}{(z+4p+3p^2z)Q z^3}.
$$
The certificate subdivides $[0,1]$ into 1,600 rational closed intervals. It encloses each arithmetic operation with rational endpoints. Each square root uses an outward integer-square-root enclosure with denominator $2^{64}$. The range ends are subdivision boundaries, and the script checks every denominator it divides by. A second certificate reduces eleven polynomial inequalities modulo $S^2=1+6p^2-3p^4$ and verifies their Bernstein coefficients on fourteen rational subintervals. The generator emits ordinary Lean polynomial-identity proofs of these inequalities. [Independent polynomial check](all_ranks_independent.py) · [Lean Bernstein certificates](BigDescents132/AllRankBernstein.lean).

## Uniform strict sign at every required interior phase level

Fix $N\ge128$. Let $v>0$ have normalized density proportional to $v^{1/2}(1+v)^{-N-1}$ and use $\mathbb E$ for its integral. The angular component of the normalized three-cut formula has unit modulus. Its cosine is $\cos\Phi_N$ with $\Phi_N=N\theta-\phi$, where $\phi$ is [`Points.phaseOffset`](BigDescents132/PhaseLift.lean). There is a strictly positive normalization of $B_N(1-s)$ for which the absolute difference from this cosine is at most
$$
\mathbb E|U-1|+A(\mu/r)^{N+1}\,
   \mathbb E\!\left[\mathbf1_{0<v<(R-r)/r}|V(v)|\right].
$$
This is the triangle inequality in [`Points.scaled_coefficient` and `Points.scaled_real_size`](BigDescents132/Balanced.lean). On the real segment the existing [real-cut bounds](BigDescents132/RealBounds.lean) give
$$
|V(v)|\le(1+(1+\sigma)v)\min(V_0/v,V_1).
$$

For the complex multiplier, write $U=(1+v)^{-1}P_v a_1 a_2 a_3$. The factors $a_i$ have nonnegative real part and $a_i^2=1+\lambda_i v$ with $\lambda_i=u/(u-c_i)$ for $c_i=r,R,\bar u$. Thus $|a_i-1|\le|\lambda_i|v$. The first two $|\lambda_i|$ are bounded by $\sigma$ and the third equals $\sigma/2$. Also $P_v=(1+\lambda_0 v)^{-1}$ with $|\lambda_0|\le\sigma$ and $|P_v|\le P$. These are the same factor identities used in the [complex-cut proof](BigDescents132/UpperBounds.lean). Expanding the product of $1+(a_i-1)$ gives
$$
|U-1|\le (1+\tfrac72 P\sigma)v+2P\sigma^2v^2+
              \tfrac12 P\sigma^3v^3.
$$
Indeed $|P_v-1|\le P\sigma v$ and $|(1+v)^{-1}-1|\le v$, and the remaining difference is bounded by $P[(1+\sigma v)^2(1+\sigma v/2)-1]$.

The exact beta-moment ratios are $m_0=1$, $m_{-1}=2N-1$ and $m_j/m_{j-1}=(2j+1)/(2N-(2j+1))$ for $j=1,2,3$. Hence $m_j\le c_j/N^j$ for $(c_1,c_2,c_3)=(8/5,21/5,15)$. With $a=\sigma/N$ the complex error is bounded by
$$
U_*(a)=\tfrac85(\tfrac1{128}+\tfrac72\cdot\tfrac32a)
 +\tfrac{21}5\,3a^2+\tfrac{45}4a^3 .
$$

For the real error use $(\mu/r)^{N+1}\le\exp(-NEg)$, which follows from $1-x\le e^{-x}$. The new sufficient condition is
$$
                        p\ge 5/N .
$$
It places **no restriction on how close $p$ may be to 1**. The following rational upper bounds include both the complex and the real error.

| $p$ | Upper bound on the total error |
|---|---:|
| $5/N\le p\le1/4$ | $9514927/10400000$ |
| $1/4\le p\le1/2$ | $79769131/335544320$ |
| $1/2\le p\le19/20$ | $189199291/335544320$ |
| $19/20\le p<1$ | $297333691/335544320$ |

For the first range put $T=Np\ge5$. Then $\sigma/N\le(7/20)/5$. The real error is at most $(5/8)5(2T+7/20)e^{-T}$ using $g(1-p)\ge1$ and the inverse moment. The last expression decreases for $T\ge5$ and $e^5>130$. In the second range $\sigma/N\le(3/2)/128$, $T\ge32$, and the real error is bounded by $(5/8)5(2T+3/4)e^{-2T/3}$. Use $\exp(2T/3)\ge(2T/3)^3/6$. In the third range $NEg>4$ and $e^4>5$. Use $V_1\le7/2$ and $1+(1+\sigma)m_1\le1+(5/2)(8/5)/128$. In the fourth range use $V_1\le6/5$ and $(\mu/r)^{N+1}\le1$. All four bounds are strictly below 1. At any integer phase extremum on this interval the sign of the literal polynomial is consequently the sign of the cosine.

## Six endpoint signs for all integers $N\ge128$

Write $a_{N,k}=[t^k]B_N$. The positive coefficient formula in the starting project simplifies to
$$
a_{N,k}=\sum_{m+i+j=k} C_m {m\choose i}{2m+j\choose j}
                   {N+m\choose 2m+j+k+1}\quad(N\ge1).
$$
In the prior formula the $y^h$ summand contains $\binom{2m+h}{h}\binom{m+h}{k-m}$. The column generating function is therefore
$
\begin{aligned}
\sum_{N\ge1} a_{N,k}y^{N-1}
&=\sum_{m=0}^k \frac{C_m y^{m+k}}{(1-y)^{k+1}}[x^{k-m}]\frac{(1+x)^m}{(1-y(1+x))^{2m+1}}\\
&=\sum_{m+i+j=k} C_m\binom{m}{i}\binom{2m+j}{j}\frac{y^{m+k+j}}{(1-y)^{2m+j+k+2}}.
\end{aligned}
$
Taking $[y^{N-1}]$ gives the displayed coefficient expression. It makes each column a polynomial in $N$ of degree at most $3k+1$, with the usual zero convention for out-of-range binomials. [Original formal coefficient formula](BigDescents132/PositiveFormula.lean).

Uniformly for $N\ge1$,
$$
 0\le\frac{a_{N,k}}{N^{3k+1}}\le\frac{10^k}{(3k+1)!}.
$$
Above the degree the coefficient vanishes. Otherwise $3k+1\le2N$. Write $r_0=2m+j+k+1$. In a nonzero summand the $r_0$ consecutive numerator factors in $\binom{N+m}{r_0}$ have arithmetic mean $N-(j+k)/2\le N$, so their product is at most $N^{r_0}$. Also $3k+1-r_0=2i+j$. Multiplying the normalized term by $(3k+1)!$ bounds it by $4^m\binom mi\binom{2m+j}j4^i2^j$. The ordinary generating function of the sum of these bounds is
$$
\sum_{m\ge0}(4x)^m(1+4x)^m(1-2x)^{-2m-1}
=\frac{1-2x}{1-8x-12x^2}.
$$
Its coefficients start $1,6$ and obey $c_k=8c_{k-1}+12c_{k-2}\le10^k$ by induction.

Use $(R_1,R_2,R_3,R_4,R_5,R_6)=(74,271,672,1348,2370,3800)$. For $K=40$ the absolute tail of $B_N(-R_i/N^3)/N$ beyond $K$ is less than $1/256$. Indeed the successive majorants have ratio at most $1/2$ there and $512(10R_i)^{41}<124!$. For fixed $i$ form the polynomial
$$
H_i(N)=256(-1)^i\sum_{k=0}^{40}a_{N,k}(-R_i)^k N^{3(40-k)}-N^{121}.
$$
It has degree at most 121. Exact arithmetic checks $\Delta^j H_i(128)>0$ for $0\le j\le121$ and all six $i$. Newton interpolation gives
$H_i(128+b)=\sum_{j=0}^{121}\binom bj\Delta^jH_i(128)>0$ for every integer $b\ge0$. Subtracting the tail proves $(-1)^i B_N(-R_i/N^3)>0$ for all $N\ge128$. At positive rank the constant term is $a_{N,0}=N$.

## Matching the phase and counting the roots

Fix $N\ge128$ and choose $p_L$ corresponding to $s=1+3800/N^3$. Since $3800/128^3<15/16^3$, strict monotonicity and the scale bound at $p=1/16$ show $p_L<1/16$. The two scale inequalities now give $5<Np_L<19/3$. The phase offset obeys
$$
\phi=\tfrac{3\pi}{4}+
 \tfrac12\big(\arg(r-u)+\arg(R-u)\big)-\theta/2-\arg(\eta-u).
$$
This is [`Points.offset_formula`](BigDescents132/PhaseEnds.lean). At $p_L$ we have $r>|u|$, so the two arguments in parentheses lie in $(-\pi/2,0)$, $\arg(\eta-u)<0$ and $\theta<\pi/2$. Hence $\phi>0$. Therefore
$$
 \Phi_N(p_L)<N\theta<2\sqrt3 Np_L<7\pi.
$$
The last comparison follows from $\sqrt3<26/15$ and $\pi>3.14$.

As $p\uparrow1$, the upper argument tends to $2\pi/3$ and the verified far offset tends to $2\pi/3$. Thus $\Phi_N\to2(N-1)\pi/3\ge d\pi$, where $d=\lfloor2(N-1)/3\rfloor$. Choose $p_H$ sufficiently close to 1 that $\Phi_N(p_H)>(d-1)\pi$ and $(-1)^d B_N(1-s(p_H))>0$. The second assertion follows from the exact degree, the positive leading coefficient and $s(p)\to\infty$.

The six left samples give the signs numbered $0,\ldots,6$ in order of increasing magnitude. On $[p_L,p_H]$, continuity of $\Phi_N$ gives ordered successive crossings of $7\pi,8\pi,\ldots,(d-1)\pi$ by the intermediate value theorem. At each crossing the total normalized error is strictly below 1. The sign there is $(-1)^j$. The last sample supplies sign $(-1)^d$. Increasing $p$ strictly decreases the real polynomial argument, so the $d$ intervening open intervals are disjoint and each contains a strictly negative root. A degree-$d$ polynomial with $d$ distinct roots has only simple roots and splits over the reals.

## Verification and finite ranks

Run from this directory with Python 3.10 or later. No network or floating-point input is required for the primary certificate.

~~~sh
python3 all_ranks_certificate.py
~~~

The finite-rank portion proves the required sign changes through rank 127 by integer Horner evaluation at ordered rational points. It finds 5,292 disjoint open intervals across the 128 ranks, with exactly the degree-many intervals for every row. Lean also verifies these finite ranks through `finite127_simple_negative`. It proves the two radix evaluations determine the polynomial recurrence and checks the signs using integer Horner evaluation. [Finite Lean theorem](BigDescents132/Through127.lean).

The computation of coefficients for the finite rows and for the Newton differences uses $G^2=D_{1-t}$ and $G(0)=1$, hence $2DG'=D'G$. If $D=\sum d_jx^j$, then $2n g_n=\sum_{j=1}^4(3j-2n)d_jg_{n-j}$ with absent terms zero. The signed formal germ gives $g_{N+1}=-2t(B_N-(1-t)B_{N-1})$ for $N\ge2$. Every row used, through 249, is independently checked against both subtraction-free first-maximum recurrences from the literal permutation definition. For that second check, packing in a radix larger than every row sum is injective. The row sum is the $N$th Catalan number by the same recurrence at $t=1$.

Lean proves the all-rank statement for the defining permutation sum in `BigDescents132.all_ranks_simple_negative`. Its endpoint verification multiplies the truncated polynomials by $121!$ to clear denominators, expands at the shift $N=128+x$, and checks the nonnegative ordinary coefficients and positive constant via radix $2^{2048}$. The digit-sum bound verifies that addition introduces no carries. The uniform estimate $25\cdot20^k/(3k+1)!$ for the normalized coefficients suffices at all six radii. For the second parameter interval Lean bounds the exponential at $64/3$ by $1024$, which still gives a strict error below one. To pass to the polynomial argument, the intermediate value theorem gives a geometric parameter for every magnitude. The small-scale bound puts every such parameter in the range of the uniform estimate. [Formal certificate](BigDescents132/EndpointHeadCheck.lean) · [Four contour ranges](BigDescents132/AllRankUniform.lean) · [Root count](BigDescents132/AllRanks.lean) · [Axiom audit](Axioms.lean).

The optional independent replay uses SymPy 1.14.0. It checks the quartic algebra symbolically, certifies the geometric inequalities in Bernstein form, enumerates literal permutations through rank 9, and constructs all finite rows from the positive binomial formula. SymPy isolates their real roots by its exact polynomial algorithm. The same replay checks that each truncated sign polynomial has strictly positive coefficients in the ordinary powers of $N-128$.

~~~sh
python3 all_ranks_independent.py
~~~
