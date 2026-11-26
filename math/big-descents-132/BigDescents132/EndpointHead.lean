import BigDescents132.EndpointTail
import BigDescents132.PackedRows
import Mathlib.Data.Nat.Choose.Central

namespace BigDescents132.AllRanks
open Finset Polynomial

/-- Recursive range sum used by the certificate's closed natural-number reductions. -/
def totalNat (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => totalNat f n + f n

theorem totalNat_eq (f : ℕ → ℕ) (n : ℕ) : totalNat f n = ∑ i∈range n,f i := by
  induction n with
  | zero => simp [totalNat]
  | succ n ih => rw [totalNat,ih,sum_range_succ]

def quickChoose (n k : ℕ) := n.descFactorial k / k.factorial
theorem quickChoose_eq (n k : ℕ) : quickChoose n k = n.choose k := by
  simp [quickChoose,Nat.descFactorial_eq_factorial_mul_choose,Nat.factorial_pos]

def quickCatalan (m : ℕ) := quickChoose (2*m) m/(m+1)
theorem quickCatalan_eq (m : ℕ) : quickCatalan m=catalan m := by
  rw [quickCatalan,quickChoose_eq,catalan_eq_centralBinom_div];rfl

def countFast (N k : ℕ) := totalNat (fun m => quickCatalan m*totalNat (fun i =>
  let j:=k-m-i
  quickChoose m i*quickChoose (2*m+j) (2*m)*quickChoose (N+m) (2*m+j+k+1)) (k-m+1)) (k+1)

theorem countFast_eq (N k : ℕ) : countFast N k=binomialCount N k := by
  unfold countFast binomialCount
  simp only [totalNat_eq,quickChoose_eq,quickCatalan_eq,seriesBin,Finset.mul_sum]
  apply sum_congr rfl;intro m _
  apply sum_congr rfl;intro i _
  ring

private def natRow (p : ℕ[X]) := (List.range (p.natDegree+1)).map p.coeff

private theorem pack_map (q : ℕ) (f : ℕ → ℕ) (n : ℕ) :
    Packing.pack q ((List.range n).map f)=∑ k∈range n,f k*q^k := by
  have append (xs ys : List ℕ) : Packing.pack q (xs++ys)=Packing.pack q xs+q^xs.length*Packing.pack q ys := by
    induction xs with
    | nil => simp [Packing.pack]
    | cons a l ih => simp [Packing.pack,ih,pow_succ];ring
  induction n with
  | zero => simp [Packing.pack]
  | succ n ih => rw [List.range_succ,List.map_append,append,sum_range_succ,ih];simp [Packing.pack,mul_comm]

private theorem pack_natRow (q : ℕ) (p : ℕ[X]) : Packing.pack q (natRow p)=p.eval q :=
  (pack_map ..).trans (Polynomial.eval_eq_sum_range q).symm

/-- A no-carry positive representation at one radix certifies a polynomial identity
at every natural input. The two digit-sum bounds include all coefficients. -/
theorem eval_eq_from_radix {q : ℕ} (hq : 0<q) (p m : ℕ[X]) (w : List ℕ)
    (hp : p.eval 1<q) (hm : m.eval 1+Packing.pack 1 w<q)
    (eq : p.eval q=m.eval q+Packing.pack q w) (x : ℕ) :
    p.eval x=m.eval x+Packing.pack x w := by
  have bridge (b : ℕ) : Packing.pack b (addRows (natRow m) w)=m.eval b+Packing.pack b w := by
    have z:=congrArg (Polynomial.eval (b:ℝ)) (ofRow_add (natRow m) w)
    simp only [Polynomial.eval_add,Packing.eval_eq,pack_natRow] at z
    exact_mod_cast z
  have c:=Packing.inject hq (natRow p) (addRows (natRow m) w)
    ((pack_natRow ..).trans_lt hp) ((bridge 1).trans_lt hm) ((pack_natRow ..).trans (eq.trans (bridge q).symm))
  have v:=congrArg (Polynomial.eval (x:ℝ)) c
  simp only [Packing.eval_eq,pack_natRow,bridge] at v
  exact_mod_cast v

/-- Descending factorial in the shifted rank, with nonnegative coefficients. -/
noncomputable def falling (a : ℕ) : ℕ → ℕ[X]
  | 0 => 1
  | r+1 => (X+Polynomial.C (a-r))*falling a r

theorem falling_eval (x a r : ℕ) (hr : r≤a+1) :
    (falling a r).eval x=(x+a).descFactorial r := by
  induction r with
  | zero => simp [falling]
  | succ r ih =>
    rw [falling,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,ih (by omega),Nat.descFactorial_succ]
    have e : x+(a-r)=x+a-r := by omega
    rw [e]

/-- Multiplication by 121! clears the denominators in all 41 columns. -/
noncomputable def columnPoly (k : ℕ) : ℕ[X] :=
  ∑ m∈range (k+1), ∑ i∈range (k-m+1),
    let j:=k-m-i
    let r:=2*m+j+k+1
    Polynomial.C (catalan m*m.choose i*seriesBin (2*m) j*(121:ℕ).factorial/r.factorial) *
      falling (128+m) r

theorem column_eval (x k : ℕ) (hk : k≤40) :
    (columnPoly k).eval x=(121:ℕ).factorial*countFast (x+128) k := by
  rw [countFast_eq,binomialCount,columnPoly,Polynomial.eval_finset_sum,Finset.mul_sum]
  apply sum_congr rfl;intro m hm
  rw [Polynomial.eval_finset_sum,Finset.mul_sum]
  apply sum_congr rfl;intro i hi
  have mk : m≤k := by have := mem_range.mp hm;omega
  have ik : i≤k-m := by have := mem_range.mp hi;omega
  let j:=k-m-i
  let r:=2*m+j+k+1
  let v:=catalan m*m.choose i*seriesBin (2*m) j
  have h : r≤121 := by dsimp [r,j];omega
  change (Polynomial.C (v*(121:ℕ).factorial/r.factorial)*falling (128+m) r).eval x=(121:ℕ).factorial*(v*(x+128+m).choose r)
  rw [Polynomial.eval_mul,Polynomial.eval_C,falling_eval _ _ _ (by omega),Nat.descFactorial_eq_factorial_mul_choose]
  have dvd : r.factorial ∣ v*(121:ℕ).factorial := dvd_mul_of_dvd_right (Nat.factorial_dvd_factorial h) _
  rw [←Nat.mul_assoc,Nat.div_mul_cancel dvd]
  ring

end BigDescents132.AllRanks
