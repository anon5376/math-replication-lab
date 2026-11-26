"""Independent checks using SymPy polynomials, binomial extraction and Descartes isolation."""
from fractions import Fraction
from functools import lru_cache
from math import comb, factorial
from itertools import combinations, permutations

import sympy as S


def identities():
    p,z,w,V = S.symbols("p z w V")
    D = p+z
    F = p**2+4*p*z+z**2+3*p*p*z*z-1
    Q = 1+3*p*p
    eta = (1-p*p)*z*z*Q
    dual = (1-z*z)*p*p*(1+3*z*z)
    product = ((D*w-p)**2-1)*((D*w-z)**2+3*p*p*z*z)
    for expression in (product-(D**4*w**4-2*D**4*w**3+2*eta*w-eta), eta+dual-D**4):
        assert S.rem(expression,F,z).expand()==0
    W = 1+6*p**2-3*p**4
    Z = (1-p*p)/(V+2*p)
    def zero(expr):
        num = S.together(expr).as_numer_denom()[0]
        assert S.rem(num,V**2-W,V).expand()==0
    zero(F.subs(z,Z))
    rho = (V+2*p)**2/((1+p)**2*Q)
    gap=6*(1+p)**2/((2+V)*(V+2*p))
    zero(1-1/rho-p*(1-p)*gap)
    beta=(1-p*p)/(p+Z)**2
    cosine=(1-3*p*p)/Q
    zero((beta-cosine)*Q-( (2*Z+3*p*Z*Z-p)*Q/(p+Z)**2+6*p)*p)
    zero((rho-cosine)*Q-(rho*(1-p)*gap*Q+6*p)*p)
    print("All symbolic quartic, complement, separation and angular identities verified.")


@lru_cache(None)
def choose(a,b):
    return comb(a,b) if 0<=b<=a else 0


@lru_cache(None)
def weights(k):
    return [(m,2*m+j+k+1,choose(2*m,m)//(m+1)*choose(m,i)*choose(2*m+j,j))
            for m in range(k+1) for i in range(min(m,k-m)+1) for j in [k-m-i]]


def coeff(n,k):
    if n==0:
        return int(k==0)
    return sum(c*choose(n+m,r) for m,r,c in weights(k))


def cone(values):
    # Return d! H(start+x) in the ordinary monomial basis.
    n=len(values)-1
    accum=[0]*(n+1)
    prod=[1]
    for j in range(n+1):
        v=values[0]*(factorial(n)//factorial(j))
        for k,c in enumerate(prod):
            accum[k]+=v*c
        prod=[b-j*a for a,b in zip(prod+[0],[0]+prod)]
        values=[b-a for a,b in zip(values,values[1:])]
    return accum



def geometric_bernstein(report=None):
    """Second geometry certificate: polynomial reduction and exact Bernstein coefficients."""
    p,v=S.symbols("p v")
    W=1+6*p**2-3*p**4
    b=v+2*p
    Z=1-p**2
    q=1+3*p**2
    u=p*b+Z
    rd=(1+p)**2*q
    h=(2*Z*b+3*p*Z**2-p*b**2)*q+6*p*u**2
    pp=12*u**4+h**2
    dd=u**2-Z*rd
    fn=(p*b**2+4*Z*b+3*p*Z**2)*(b**2+3*Z**2)
    fd=(Z+4*p*b+3*p*p*Z)*q*Z**3
    polynomials=[
        (0,1,18*(1+p)**2-4*(2+v)*b),
        (0,1,15*u**4-h**2),
        (0,1,625*768*rd**2*(2+v)**2-4096*b**4*(12*(2+v)**2+36*(v+4*p-2*p**2)**2)),
        (0,Fraction(1,2),25*b**4*u**4-(1+p)**4*pp),
        (Fraction(1,2),1,dd),
        (Fraction(1,2),1,49*b**4*dd**2-4*p**2*pp*(1+p)**4),
        (Fraction(19,20),1,36*b**4*dd**2-25*p**2*pp*(1+p)**4),
        (0,Fraction(1,4),12*49-400*q**2),
        (Fraction(1,4),1,27*p**2-q**2),
        (0,Fraction(1,16),fn-15*fd),
        (0,Fraction(1,16),20*fd-fn),
    ]
    def bernstein(poly,lo,hi):
        coeff=[Fraction(x) for x in reversed(S.Poly(poly,p).all_coeffs())]
        n=len(coeff)-1
        power=[sum(coeff[j]*comb(j,k)*lo**(j-k)*(hi-lo)**k for j in range(k,n+1)) for k in range(n+1)]
        return [sum(power[k]*Fraction(comb(j,k),comb(n,k)) for k in range(j+1)) for j in range(n+1)]
    def halves(a):
        left,right=[a[0]],[a[-1]]
        while len(a)>1:
            a=[(x+y)/2 for x,y in zip(a,a[1:])]
            left.append(a[0]);right.append(a[-1])
        return left,list(reversed(right))
    def positive(a,b,t,depth=0):
        # T = A^2-W B^2. Each case implies A+B sqrt(W) > 0.
        if (min(a)>0 and min(b)>=0) or (min(a)>0 and min(t)>0) or (min(b)>0 and max(t)<0):
            return 1
        if depth>=30:
            raise ArithmeticError("Bernstein positivity certificate failed")
        left,right=zip(*(halves(x) for x in (a,b,t)))
        return positive(*left,depth+1)+positive(*right,depth+1)
    counts=[]
    for index,(lo,hi,f) in enumerate(polynomials):
        remainder=S.Poly(S.rem(f,v*v-W,v),v)
        aa,bb=remainder.nth(0),remainder.nth(1)
        tt=S.expand(aa**2-W*bb**2)
        series=[bernstein(g,Fraction(lo),Fraction(hi)) for g in (aa,bb,tt)]
        counts.append(positive(*series))
        if report is not None:
            report(index,p,v,W,f,Fraction(lo),Fraction(hi),aa,bb,tt,bernstein)
    print(f"Independent Bernstein proof of all {len(counts)} geometric inequalities: {sum(counts)} certified subintervals.")


def verify():
    if not __debug__:
        raise SystemExit("Run without -O.")
    identities()
    geometric_bernstein()
    for n in range(10):
        row=[0]*(1+2*max(0,n-1)//3)
        triples=list(combinations(range(n),3))
        for word in permutations(range(n)):
            if any(word[i]<word[k]<word[j] for i,j,k in triples):
                continue
            row[sum(a>b+1 for a,b in zip(word,word[1:]))]+=1
        assert row==[coeff(n,k) for k in range(len(row))]
    print("Literal permutation enumeration agrees with the closed form for ranks 0..9.")
    x=S.Symbol("x")
    count=0
    for n in range(128):
        degree=2*max(0,n-1)//3
        row=[coeff(n,k) for k in range(degree+1)]
        assert sum(row)==comb(2*n,n)//(n+1)
        poly=S.Poly.from_list(row[::-1],gens=x,domain=S.ZZ)
        boxes=poly.intervals()
        assert len(boxes)==degree and all(m==1 and left<0 and right<=0 for (left,right),m in boxes)
        count+=len(boxes)
    print(f"Direct binomial rows and independent exact real-root isolation: {count} simple negative roots at ranks 0..127.")
    ns=range(128,250)
    rows={n:[coeff(n,k) for k in range(41)] for n in ns}
    for i,R in enumerate([74,271,672,1348,2370,3800],1):
        values=[256*(-1)**i*sum(rows[n][k]*(-R)**k*n**(3*(40-k)) for k in range(41))-n**121 for n in ns]
        assert min(cone(values))>0, R
    print("All 732 shifted ordinary monomial coefficients of the six interpolation polynomials are strictly positive.")


if __name__=="__main__":
    verify()
