import BigDescents132.EndpointHead

set_option maxRecDepth 20000

namespace BigDescents132.AllRanks
open Finset Polynomial

def parityPart (c : ℕ → ℕ) (N R : ℕ) (par : Bool) : ℕ :=
  256*totalNat (fun k => if decide (k%2=0)=par then c k*R^k*N^(3*(40-k)) else 0) 41

noncomputable def headPart (R : ℕ) (par : Bool) : ℕ[X] :=
  ∑ k∈range 41, if decide (k%2=0)=par then
    Polynomial.C (256*R^k)*columnPoly k*(X+Polynomial.C 128)^(3*(40-k)) else 0

private theorem part_eval (x R : ℕ) (par : Bool) :
    (headPart R par).eval x=(121:ℕ).factorial*parityPart (countFast (x+128)) (x+128) R par := by
  rw [headPart,Polynomial.eval_finset_sum,parityPart,totalNat_eq,←Nat.mul_assoc,Finset.mul_sum]
  apply sum_congr rfl;intro k hk
  have cut : k≤40 := by have := mem_range.mp hk;omega
  by_cases h : decide (k%2=0)=par
  · simp only [if_pos h,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
      Polynomial.eval_add,Polynomial.eval_X,column_eval _ _ cut];ring
  · simp [h]

def radixDigits (q : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | L+1, z => z%q::radixDigits q L (z/q)

private theorem digits_pack (q : ℕ) (hq : 0<q) (L z : ℕ) (hz : z<q^L) :
    Packing.pack q (radixDigits q L z)=z := by
  induction L generalizing z with
  | zero => simp only [pow_zero,Nat.lt_one_iff] at hz;simp [hz,radixDigits,Packing.pack]
  | succ L ih =>
    rw [radixDigits,Packing.pack,ih _ ((Nat.div_lt_iff_lt_mul hq).mpr (by simpa [pow_succ] using hz)),Nat.mod_add_div]

private theorem signed_parts (N R : ℕ) (hN : 0<N) (par : Bool) :
    ((parityPart (countFast N) N R par:ℕ):ℝ) - ((parityPart (countFast N) N R (!par):ℕ):ℝ) =
      256*(if par then 1 else -1)*(N:ℝ)^121*scaledHead N R := by
  have np : (0:ℝ)<N := by exact_mod_cast hN
  have ct (k : ℕ) : (countFast N k:ℝ)=(B N).coeff k := by
    obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hN.ne'
    rw [countFast_eq,coefficient_eq_binomialCount]
  simp only [parityPart,totalNat_eq,Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat,Nat.cast_ite,
    Nat.cast_zero,Nat.cast_pow,ct,scaledHead,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply sum_congr rfl;intro k hk
  have kn : k≤40 := by have := mem_range.mp hk;omega
  have expo : (N:ℝ)^121=(N:ℝ)^(3*(40-k))*(N:ℝ)^(3*k)*(N:ℝ) := by
    rw [←pow_add,←pow_succ,show 3*(40-k)+3*k+1=121 by omega]
  rw [expo,div_pow,←pow_mul]
  by_cases ev : k%2=0
  · have eq:= (Nat.even_iff.mpr ev).neg_pow (R:ℝ)
    cases par <;> simp [ev,eq] <;> field_simp <;> ring
  · have od : Odd k := Nat.not_even_iff_odd.mp (fun h => ev (Nat.even_iff.mp h))
    have eq := od.neg_pow (R:ℝ)
    cases par <;> simp [ev,eq] <;> field_simp <;> ring

def fixedRadix : ℕ := 2^2048

def positiveEval (c : ℕ → ℕ) (x R : ℕ) (par : Bool) : ℕ :=
  (121:ℕ).factorial*parityPart c (x+128) R par

def negativeEval (c : ℕ → ℕ) (x R : ℕ) (par : Bool) : ℕ :=
  (121:ℕ).factorial*(parityPart c (x+128) R (!par)+(x+128)^121)

/-- The checker uses the ordinary coefficients at the shift N=128.
The radix digit-sum inequality also detects every possible borrow. -/
def radixCheck (q pa ma pq mq : ℕ) : Bool :=
  let z := pq-mq
  decide (mq≤pq ∧ z<q^122 ∧ 0<z%q ∧ pa<q ∧ ma+Packing.pack 1 (radixDigits q 122 z)<q)

private theorem radix_surplus {q : ℕ} (qp : 0<q) (a m : ℕ[X])
    (check : radixCheck q (a.eval 1) (m.eval 1) (a.eval q) (m.eval q)=true) (x : ℕ) :
    m.eval x<a.eval x := by
  let z:=a.eval q-m.eval q
  let w:=radixDigits q 122 z
  obtain ⟨ord,bd,strict,pa,ma⟩:=of_decide_eq_true check
  have pack : Packing.pack q w=z := digits_pack q qp _ _ bd
  have eq : a.eval q=m.eval q+Packing.pack q w := by
    rw [pack,Nat.add_comm];exact (Nat.sub_add_cancel ord).symm
  have posw : 0<Packing.pack x w := Nat.add_pos_left strict _
  rw [eval_eq_from_radix qp a m w pa ma eq x]
  exact Nat.lt_add_of_pos_right posw

def headCheck (small large : ℕ → ℕ) (R : ℕ) (par : Bool) : Bool :=
  radixCheck fixedRadix (positiveEval small 1 R par) (negativeEval small 1 R par)
    (positiveEval large fixedRadix R par) (negativeEval large fixedRadix R par)

attribute [local irreducible] countFast fixedRadix parityPart headPart columnPoly positiveEval negativeEval radixCheck

theorem headCheck_sound (small large : ℕ → ℕ)
    (hs : ∀ k, k<41 → small k=countFast (1+128) k)
    (hl : ∀ k, k<41 → large k=countFast (fixedRadix+128) k)
    (R : ℕ) (par : Bool) (check : headCheck small large R par=true)
    (N : ℕ) (hN : 128≤N) (hR : R≤3800) :
    0 < (if par then (1:ℝ) else -1)*(B N).eval (-(R:ℝ)/(N:ℝ)^3) := by
  let q:=fixedRadix
  have qp : 0<q := by unfold q fixedRadix;positivity
  let a:=headPart R par
  let m:=headPart R (!par)+Polynomial.C (121:ℕ).factorial*(X+Polynomial.C 128)^121
  have eqv (c : ℕ → ℕ) (x : ℕ) (s : ∀ k,k<41 → c k=countFast (x+128) k) :
      a.eval x=positiveEval c x R par ∧ m.eval x=negativeEval c x R par := by
    have equal (e : Bool) : parityPart (countFast (x+128)) (x+128) R e=parityPart c (x+128) R e := by
      unfold parityPart;rw [totalNat_eq,totalNat_eq]
      apply congrArg (256*·)
      apply sum_congr rfl;intro k hk
      exact congrArg (fun v => if decide (k%2=0)=e then v*R^k*(x+128)^(3*(40-k)) else 0) (s k (mem_range.mp hk)).symm
    constructor
    · unfold positiveEval
      exact (part_eval x R par).trans (congrArg ((121:ℕ).factorial*·) (equal par))
    · change (_+_ : ℕ[X]).eval x=_
      rw [Polynomial.eval_add,part_eval,equal (!par)]
      simp only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,negativeEval,Nat.mul_add]
  have sm:=eqv small 1 hs
  have lg:=eqv large q hl
  have sc : radixCheck q (a.eval 1) (m.eval 1) (a.eval q) (m.eval q)=true := by
    rw [sm.1,sm.2,lg.1,lg.2];exact check
  let x:=N-128
  have rank : x+128=N := by dsimp [x];omega
  have gt:=radix_surplus qp a m sc x
  obtain ⟨hx,hy⟩:=eqv (countFast (x+128)) x (fun _ _ => rfl)
  rw [hx,hy] at gt
  simp only [positiveEval,negativeEval,rank,Nat.mul_lt_mul_left (Nat.factorial_pos 121)] at gt
  have gtr : (N:ℝ)^121 <
      (parityPart (countFast N) N R par:ℝ)-(parityPart (countFast N) N R (!par):ℝ) := by
    have cast : (parityPart (countFast N) N R (!par):ℝ)+(N:ℝ)^121 < (parityPart (countFast N) N R par:ℝ) := by exact_mod_cast gt
    linarith
  rw [signed_parts N R (by omega) par] at gtr
  have npos : 0<N := by omega
  have nR : (0:ℝ)<N := by exact_mod_cast npos
  have np : 0<(N:ℝ)^121 := pow_pos nR _
  have tail:=endpoint_tail (N:=N) (by omega) (R:=(R:ℝ)) (by positivity) (by exact_mod_cast hR)
  have eH := abs_lt.mp tail
  have fact : 1 < (256*(if par then (1:ℝ) else -1))*scaledHead N R := by
    apply lt_of_mul_lt_mul_left (a:=(N:ℝ)^121) (by simpa only [mul_one] using (gtr.trans_eq (by ring))) np.le
  suffices sg : 0<((if par then (1:ℝ) else -1)*(B N).eval (-(R:ℝ)/(N:ℝ)^3))/N by
    simpa only [zero_mul] using (lt_div_iff₀ nR).mp sg
  rw [mul_div_assoc]
  cases par <;> simp only [Bool.false_eq_true,if_false,if_true,mul_neg,neg_mul,mul_one,one_mul] at fact ⊢ <;>
    linarith only [fact,eH.1,eH.2]

end BigDescents132.AllRanks
