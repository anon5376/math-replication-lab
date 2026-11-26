"""Regenerate the extended Lean finite certificate. Run from this directory."""
from pathlib import Path
from fractions import Fraction
from math import gcd
from replay52 import paper_counts, lean_grid
from all_ranks_certificate import numerator


def grid(row):
    sign = 1
    samples = []
    for exponent in range(-26,27):
        for m in range(48,96):
            a,b=m<<max(0,exponent),48<<max(0,-exponent)
            g=gcd(a,b)
            a,b=a//g,b//g
            if sign*numerator(row,a,b)<0:
                samples.append(Fraction(a,b))
                sign=-sign
                if len(samples)==len(row)-1:
                    return samples
    raise ValueError("could not isolate roots")


def source():
    rows=paper_counts(127)
    result=["import BigDescents132.Through52", "", "namespace BigDescents132.Certificate127",
            "open Coefficients", "", "def table : ℕ → Counts"]
    for n in range(53,128):
        b,a,c=rows[n]
        result.extend([f"  | {n} => ⟨{b},",f"      {a},",f"      {c}⟩"])
    result.extend(["  | n => Certificate52.table n","","def grid : ℕ → List ℚ"])
    for n in range(53,128):
        result.append(f"  | {n} => {lean_grid(grid(rows[n][0]))}")
    result.extend(["  | n => Certificate52.grid n","","end BigDescents132.Certificate127",""])
    return "\n".join(result)


def packed():
    """A balanced lookup keeps kernel reduction of fixed indices logarithmic."""
    rows = paper_counts(127)
    result = ["import BigDescents132.PackedRows", "", "namespace BigDescents132.Certificate127", "open Packing", ""]
    for name, q in [("stored", 2**260), ("masses", 1)]:
        for n, components in enumerate(rows):
            digits = [sum(c*q**k for k, c in enumerate(r)) for r in components]
            result.append(f"private def {name}Value{n} : Triple := ⟨" + ", ".join(hex(v) for v in digits) + "⟩")
        def branch(lo, hi):
            if hi == lo+1:
                return f"{name}Value{lo}"
            mid = (lo+hi)//2
            left, right = branch(lo, mid), branch(mid, hi)
            label = f"{name}From{lo}To{hi}"
            result.append(f"private def {label} (n : ℕ) : Triple := if n<{mid} then {left} else {right}")
            return f"{label} n"
        value = branch(0, len(rows))
        result.extend([f"def {name} (n : ℕ) : Triple := if n<128 then {value} else ⟨0,0,0⟩", ""])
    result.extend(["end BigDescents132.Certificate127", ""])
    return "\n".join(result)


def blocks():
    names=[("rows","rowCheck",128),("steps","recurrenceCheck",126),("grids","gridCheck",128)]
    result={}
    for k in range(16):
        dep="RankChecks" if k==0 else f"FiniteBlock{k-1:02d}"
        lines=[f"import BigDescents132.{dep}","","namespace BigDescents132.Certificate127","",
               "set_option maxRecDepth 250000","set_option maxHeartbeats 8000000",""]
        for name,check,end in names:
            size=min(8,end-k*8)
            if k < 12:
                lines.extend([f"theorem {name}{k} : (List.range {size}).all (fun j => {check} ({k*8}+j))=true := by decide +kernel", ""])
            else:
                lines.append("set_option Elab.async false")
                tests=[]
                for offset in range(size):
                    label=f"{name}{k}At{offset}"
                    tests.append(label)
                    lines.append(f"private theorem {label} : {check} {k*8+offset}=true := by decide +kernel")
                numbers=", ".join(str(x) for x in range(size))
                lines.extend([f"theorem {name}{k} : (List.range {size}).all (fun j => {check} ({k*8}+j))=true := by",
                              f"  rw [show List.range {size}=[{numbers}] by decide]",
                              "  simp only [List.all_cons,List.all_nil,Nat.reduceAdd," + ",".join(tests) + ",Bool.and_self]", ""])
        result[f"FiniteBlock{k:02d}.lean"]="\n".join(lines+["end BigDescents132.Certificate127",""])
    lines=["import BigDescents132.FiniteBlock15","","namespace BigDescents132.Certificate127",""]
    for name,check,end in names:
        lines.append(f"private theorem all_{name} (n : ℕ) (hn : n<{end}) : {check} n=true := by")
        for k in range(16):
            start=k*8
            if k<15:
                lines.append(f"  by_cases h{start+8} : n<{start+8}")
            term=f"simpa only [show {start}+(n-{start})=n by omega] using List.all_eq_true.mp {name}{k} (n-{start}) (List.mem_range.mpr (by omega))"
            lines.append(("  · " if k<15 else "  ")+term)
        lines.append("")
    lines.extend(["end BigDescents132.Certificate127","","namespace BigDescents132","open Certificate127","",
                  "/-- Exact coefficient and sign checks for every rank through 127. -/",
                  "theorem finite127_simple_negative (n : ℕ) (hn : n≤127) :",
                  "    (B n).natDegree=expectedDegree n ∧ SimpleNegative (B n) :=",
                  "  grid_sound (row_steps_sound all_rows all_steps n hn) (all_grids n (by omega))","","end BigDescents132",""])
    result["Through127.lean"]="\n".join(lines)
    return result


if __name__=="__main__":
    from argparse import ArgumentParser
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("--write",action="store_true")
    opts=parser.parse_args()
    directory=Path(__file__).parent/"BigDescents132"
    files={"Data127.lean":source(),"PackedData.lean":packed(),**blocks()}
    for name,content in files.items():
        path=directory/name
        if opts.write:
            path.write_text(content)
        if path.read_text()!=content:
            raise SystemExit(f"{name} differs from regenerated certificate")
    print("Verified the 75 extended coefficient rows and rational grids, and the complete packed recurrence.")
