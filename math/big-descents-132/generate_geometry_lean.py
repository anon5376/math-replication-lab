"""Generate Lean certificates for the exact quartic inequalities from Bernstein coefficients."""
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import sympy as S
from all_ranks_independent import geometric_bernstein

NAMES = ["gap_numerator","pole_numerator","amplitude_numerator","near_numerator",
         "far_denominator","far_numerator","outer_numerator","small_slope_numerator",
         "large_slope_numerator","scale_lower_numerator","scale_upper_numerator"]

def num(x):
    x=Q(x)
    return str(x.numerator) if x.denominator==1 else f"({x.numerator}/{x.denominator})"

def formula(x):
    return str(x).replace("**","^")

def render():
    lines=["import BigDescents132.AllRankCoordinate","","namespace BigDescents132.AllRanks.Bernstein",
           "open Set","","set_option maxRecDepth 50000","set_option maxHeartbeats 12000000","",
           "private theorem radical_positive {a b s w : ℝ} (hs : 0<s) (sq : s^2=w)",
           "    (h : (0<a ∧ 0≤b) ∨ (0<a ∧ 0<a^2-w*b^2) ∨ (0<b ∧ a^2-w*b^2<0)) :",
           "    0<a+b*s := by",
           "  have v : (b*s)^2=w*b^2 := by rw [mul_pow,sq]; ring",
           "  rcases h with ⟨x,y⟩|⟨x,y⟩|⟨x,y⟩",
           "  · exact add_pos_of_pos_of_nonneg x (mul_nonneg y hs.le)",
           "  · by_contra! z",
           "    have l : a≤ -(b*s) := by linarith",
           "    nlinarith only [v,y,pow_le_pow_left₀ x.le l 2]",
           "  · by_contra! z",
           "    have l : b*s≤ -a := by linarith",
           "    nlinarith only [v,y,pow_le_pow_left₀ (mul_pos x hs).le l 2]",""]
    def report(index,p,v,W,raw,lo,hi,A,B,T,bernstein):
        name=NAMES[index]
        full=lambda f: formula(S.horner(f,p))
        polys=[A,B,T]
        leaves=[]
        def partition(l,h):
            vals=[bernstein(f,l,h) for f in polys]
            av,bv,tv=vals
            if min(av)>0 and min(bv)>=0:
                branch=0
            elif min(av)>0 and min(tv)>0:
                branch=1
            elif min(bv)>0 and max(tv)<0:
                branch=2
            else:
                middle=(l+h)/2
                partition(l,middle)
                partition(middle,h)
                return
            leaves.append((l,h,branch))
        partition(lo,hi)
        def emit_pos(f,strict,l,h):
            if f==0: return ["    norm_num"]
            vals=bernstein(f,l,h)
            eps=min(vals)/2 if strict else Q(0)
            n=len(vals)-1
            assert eps>=0 and (not strict or eps>0)
            terms=[]
            for j,b in enumerate(vals):
                t=(b-eps)*comb(n,j)/(h-l)**n
                if not t: continue
                term=num(t)
                if j:
                    term+=f"*(p-{num(l)})^{j}"
                if j<n:
                    term+=f"*({num(h)}-p)^{n-j}"
                terms.append(term)
            expr=" +\n        ".join([num(eps),*terms])
            rel="<" if strict else "≤"
            return ["    calc",f"      0 {rel} {expr} := by positivity",f"      _ = _ := by ring"]
        for k,(lo0,hi0,branch) in enumerate(leaves):
            fn=f"{name}_{k}"
            lines.extend([f"private theorem {fn} {{p v : ℝ}} (lo : {num(lo0)}≤p) (hi : p≤{num(hi0)})",
                f"    (hs : 0<v) (sq : v^2={formula(W)}) : 0 < ({formula(raw)}) := by",
                f"  have hx : 0≤p-{num(lo0)} := sub_nonneg.mpr lo",
                f"  have hy : 0≤{num(hi0)}-p := sub_nonneg.mpr hi"])
            branches=([("a",A,True),("b",B,False)],[("a",A,True),("t",T,True)],[("b",B,True),("t",-T,True)])
            for label,f,strict in branches[branch]:
                lines.append(f"  have h{label} : (0:ℝ){'<' if strict else '≤'}({full(f)}) := by")
                lines.extend(emit_pos(f,strict,lo0,hi0))
            quotient=S.div(raw-(A+B*v),v*v-W,v)[0]
            lcombo=f"linear_combination ({formula(quotient)})*sq" if quotient!=0 else "ring"
            lines.append(f"  have red : {formula(raw)}=({full(A)})+({full(B)})*v := by {lcombo}")
            lines.append("  rw [red]")
            if branch==0:
                lines.append("  exact radical_positive hs sq (Or.inl ⟨ha,hb⟩)")
            else:
                lines.append(f"  have id : ({full(A)})^2-({formula(W)})*({full(B)})^2=({full(T)}) := by ring")
                if branch==1:
                    lines.append("  exact radical_positive hs sq (Or.inr (Or.inl ⟨ha,by rw [id]; exact ht⟩))")
                else:
                    lines.append("  exact radical_positive hs sq (Or.inr (Or.inr ⟨hb,by rw [id]; linarith only [ht]⟩))")
            lines.append("")
        lines.extend([f"theorem {name} {{p v : ℝ}} (hp : p∈Icc {num(lo)} {num(hi)})",
            f"    (hs : 0<v) (sq : v^2={formula(W)}) : 0 < ({formula(raw)}) := by"])
        for k,(l,h,_) in enumerate(leaves):
            if k<len(leaves)-1:
                lines.extend([f"  by_cases s{k} : p≤{num(h)}",f"  · exact {name}_{k} (by linarith [hp.1]) s{k} hs sq"])
            else:
                lines.append(f"  exact {name}_{k} (by linarith [hp.1]) hp.2 hs sq")
        lines.append("")
    geometric_bernstein(report)
    return "\n".join(lines+["end BigDescents132.AllRanks.Bernstein",""])

if __name__=="__main__":
    import argparse
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--write",action="store_true")
    a=p.parse_args()
    out=Path(__file__).parent/"BigDescents132"/"AllRankBernstein.lean"
    source=render()
    if a.write:
        out.write_text(source)
    assert out.read_text()==source
    print(f"Verified generated Lean Bernstein identities ({len(source)} characters).")
