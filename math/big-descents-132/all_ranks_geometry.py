"""Certified interval bounds for the 132 quartic. Uses integers and fractions only."""
from fractions import Fraction as F
from math import isqrt


class Interval:
    def __init__(self, lo, hi=None):
        self.lo = F(lo)
        self.hi = F(lo if hi is None else hi)
        if self.lo > self.hi:
            raise ArithmeticError("empty interval")

    @staticmethod
    def wrap(x):
        return x if isinstance(x, Interval) else Interval(x)

    def __add__(self, y):
        y = self.wrap(y)
        return Interval(self.lo + y.lo, self.hi + y.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, y):
        return self + (-self.wrap(y))

    def __rsub__(self, y):
        return self.wrap(y) - self

    def __mul__(self, y):
        y = self.wrap(y)
        values = [a * b for a in (self.lo, self.hi) for b in (y.lo, y.hi)]
        return Interval(min(values), max(values))

    __rmul__ = __mul__

    def __truediv__(self, y):
        y = self.wrap(y)
        if y.lo <= 0 <= y.hi:
            raise ArithmeticError("interval divisor contains zero")
        return self * Interval(1/y.hi, 1/y.lo)

    def __rtruediv__(self, y):
        return self.wrap(y) / self

    def sq(self):
        low = 0 if self.lo <= 0 <= self.hi else min(self.lo**2, self.hi**2)
        return Interval(low, max(self.lo**2, self.hi**2))

    def sqrt(self):
        if self.lo < 0:
            raise ArithmeticError("negative square-root interval")
        scale = 1 << 64
        floor = lambda x: isqrt((x.numerator * scale**2) // x.denominator)
        return Interval(F(floor(self.lo), scale), F(floor(self.hi)+1, scale))


def geometry(number=1600):
    """Check finite interval inclusions covering every real 0 <= p <= 1."""
    if number % 80:
        raise ValueError("subdivision must include each rational regime endpoint")
    root3 = Interval(3).sqrt()
    for i in range(number):
        p = Interval(F(i,number), F(i+1,number))
        a = 1 + 3*p.sq()
        S = (1 + 3*p.sq()*(2-p.sq())).sqrt()
        z = ((1-p)*(1+p))/(S+2*p)
        d2 = (p+z).sq()
        E = p*(1-p)
        gap = 6*(1+p).sq()/((2+S)*(S+2*p))
        rho = (S+2*p).sq()/((1+p).sq()*a)
        beta = (1-p.sq())/d2
        pole_angle = ((2*z+3*p*z.sq()-p)*a+6*p*d2)/(2*root3*d2)
        pole = (1+pole_angle.sq()).sqrt()
        radial_angle = (rho*(1-p)*gap*a+6*p)/(2*root3)
        amplitude_squared = rho*(1+radial_angle.sq()).sqrt()/8
        assert gap.lo >= F(4,3), ("gap",i)
        assert pole.hi <= F(3,2), ("complex pole",i)
        assert amplitude_squared.hi <= F(25,64), ("real amplitude",i)
        if p.hi <= F(1,2):
            # nearPole/p = |u-pole|/(rp).
            near = (1-E*gap)*2*root3*pole/a
            assert near.hi <= 5, ("near real pole",i)
        if p.lo >= F(1,2):
            far = (2*root3*p/a)*pole/(rho-beta)
            assert far.hi <= F(7,2), ("far real pole",i)
            if p.lo >= F(19,20):
                assert far.hi <= F(6,5), ("last real pole",i)
        if p.hi <= F(1,4):
            assert (a/(2*root3)).hi <= F(7,20), ("small slope",i)
        if p.lo >= F(1,4):
            assert (a/(2*root3*p)).hi <= F(3,2), ("regular slope",i)
        if p.hi <= F(1,16):
            scale = (p+4*z+3*p*z.sq())*(1+3*z.sq())/((z+4*p+3*p.sq()*z)*a*z.sq()*z)
            assert scale.lo >= 15 and scale.hi <= 20, ("left scale",i)
    print(f"Geometry: {number} exact rational interval cells cover [0, 1].")


if __name__ == "__main__":
    geometry()
