"""Exact finite and all-integer sign checks for the 132 big-descent proof."""
from fractions import Fraction
from math import comb, factorial, gcd
from all_ranks_geometry import geometry


def ranks(limit):
    """Use 2D G' = D' G for G = sqrt(D), then extract B from its formal germ."""
    ds = [[], [-4], [6,-6], [-4,8,-4], [1,-2,1]]
    g = [[1]]
    rows = [[1],[1]]
    for n in range(1, limit+2):
        total = [0]*(n+1)
        for j in range(1,min(4,n)+1):
            for v,c in enumerate(ds[j]):
                for k,a in enumerate(g[n-j]):
                    total[k+v] += (3*j-2*n)*c*a
        assert all(x%(2*n) == 0 for x in total)
        while len(total)>1 and total[-1] == 0:
            total.pop()
        g.append([v//(2*n) for v in total])
        if n>=3:
            assert total[0] == 0 and all(y%2 == 0 for y in g[-1][1:])
            row = [0]*max(len(rows[-1])+1,len(g[-1])-1)
            for k,y in enumerate(rows[-1]):
                row[k] += y
                row[k+1] -= y
            for k,y in enumerate(g[-1][1:]):
                row[k] -= y//2
            while len(row)>1 and row[-1] == 0:
                row.pop()
            assert min(row)>0 and sum(row) == comb(2*(n-1),n-1)//n
            assert len(row)-1 == 2*(n-2)//3
            rows.append(row)
    return rows


def recurrence_agrees(rows):
    """Check every entry independently against the literal permutation recurrence."""
    # Evaluation in a radix larger than all coefficients is an injective packing.
    limit = len(rows)-1
    place = 1 << (2*limit+2)
    def pack(row):
        value = 0
        for c in reversed(row):
            assert 0 <= c < place
            value = place*value+c
        return value
    total = [1,1]
    first, other = 1,0
    for n in range(2,limit+1):
        first,other = first+place*other, total[n-1]+place*sum(
            total[i]*total[n-1-i] for i in range(1,n-1))
        total.append(first+other)
        assert total[n] == pack(rows[n]), n
    # All true permutation coefficients are separately <= Catalan(n) < place.
    assert all(comb(2*n,n)//(n+1) < place for n in range(limit+1))


def numerator(row,a,b):
    v = row[-1]
    factor = 1
    for c in reversed(row[:-1]):
        factor *= b
        v = -a*v+c*factor
    return v


def finite_roots(rows, maximum):
    number = 0
    for n in range(maximum+1):
        row = rows[n]
        sign, found = 1, []
        if len(row)>1:
            for exponent in range(-26,27):
                if len(found) == len(row)-1:
                    break
                for m in range(48,96):
                    a,b = m << max(0,exponent), 48 << max(0,-exponent)
                    g = gcd(a,b)
                    a,b = a//g,b//g
                    if sign*numerator(row,a,b) < 0:
                        found.append(Fraction(a,b))
                        sign = -sign
                        if len(found) == len(row)-1:
                            break
        assert len(found) == len(row)-1 == 2*max(0,n-1)//3, n
        assert all(a<b for a,b in zip([0]+found,found))
        number += len(found)
    print(f"Ranks 0..{maximum}: {number} disjoint strict negative-root intervals.")


def all_left_signs(rows, start=128, K=40):
    radii = (74,271,672,1348,2370,3800)
    degree = 3*K+1
    for i,R in enumerate(radii,1):
        sign = (-1)**i
        base = 10*R
        assert 2*base <= (3*K+5)*(3*K+6)*(3*K+7)
        assert 512*base**(K+1) < factorial(3*K+4)
        values = []
        for n in range(start,start+degree+1):
            b = rows[n]
            value = sum(b[k]*(-R)**k*n**(3*(K-k)) for k in range(min(K+1,len(b))))
            values.append(256*sign*value-n**degree)
        for j in range(degree+1):
            assert values[0]>0, (i,j)
            values = [b-a for a,b in zip(values,values[1:])]
    print(f"All ranks n >= {start}: six endpoint signs via {len(radii)*(degree+1)} positive Newton differences.")


def error_arithmetic():
    Q = Fraction
    # E[v], E[v^2], E[v^3] <= (8/5,21/5,15)/N^j for every N>=128.
    ratios = [Q(3,2-Q(3,128)),Q(5,2-Q(5,128)),Q(7,2-Q(7,128))]
    assert ratios[0] <= Q(8,5) and ratios[0]*ratios[1] <= Q(21,5)
    assert ratios[0]*ratios[1]*ratios[2] <= 15
    P,D = Q(3,2),Q(5,8)
    def upper(s_over_N):
        a = s_over_N
        return Q(8,5)*(Q(1,128)+Q(7,2)*P*a) + Q(21,5)*2*P*a*a + 15*P*a**3/2
    small = upper(Q(7,20)/5)
    regular = upper(Q(3,2)/128)
    # exp(5)>130 and exp(4)>5 are rational Taylor lower bounds.
    assert sum(Q(5**k,factorial(k)) for k in range(11))>130
    assert small + D*5*(10+Q(7,20))/130 < 1
    # On p in [1/4,1/2], T=Np>=32. exp(2T/3)>=(2T/3)^3/6.
    assert regular + D*5*6*(2+Q(3,4)/32)/(Q(2,3)**3*32**2)<1
    # On [1/2,19/20] use damping. On [19/20,1) use the far-pole bound.
    assert Q(4,3)*128*Q(1,2)*Q(1,20)>4
    assert regular + D*Q(7,2)*(1+Q(5,2)*Q(8,5)/128)/5<1
    assert regular + D*Q(6,5)*(1+Q(5,2)*Q(8,5)/128)<1
    assert Q(3800,128**3)<Q(15,16**3)
    assert 15*Q(19,3)**3>3800 and 20*5**3<3800
    assert 3<Q(26,15)**2 and 2*Q(26,15)*Q(19,3)<7*Q(314,100)
    errors = [small + D*5*(10+Q(7,20))/130,
              regular + D*5*6*(2+Q(3,4)/32)/(Q(2,3)**3*32**2),
              regular + D*Q(7,2)*(1+Q(5,2)*Q(8,5)/128)/5,
              regular + D*Q(6,5)*(1+Q(5,2)*Q(8,5)/128)]
    assert errors == [Q(9514927,10400000), Q(79769131,335544320),
                      Q(189199291,335544320), Q(297333691,335544320)]
    print("Normalized contour-error bounds: " + ", ".join(map(str,errors)) + " (all < 1).")


def main():
    if not __debug__:
        raise SystemExit("Run without -O so every certificate check is active.")
    geometry()
    error_arithmetic()
    rows = ranks(128+121)
    recurrence_agrees(rows)
    finite_roots(rows,127)
    all_left_signs(rows)
    print("All exact certificate checks passed.")


if __name__ == "__main__":
    main()
