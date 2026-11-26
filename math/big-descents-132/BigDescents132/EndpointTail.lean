import BigDescents132.EndpointEnvelope
import Mathlib.Algebra.Polynomial.Eval.Degree

namespace BigDescents132.AllRanks
open Finset

/-- The first 41 terms of the normalized permutation polynomial. -/
noncomputable def scaledHead (N : ℕ) (R : ℝ) : ℝ :=
  ∑ k∈range 41, (B N).coeff k*(-R/(N:ℝ)^3)^k/N

private noncomputable def majorant (k : ℕ) : ℝ := 25*76000^k/(3*k+1).factorial

private theorem term_bound {N : ℕ} (hN : 0 < N) {R : ℝ} (hR : 0≤R) (hr : R≤3800) (k : ℕ) :
    |(B N).coeff k*(-R/(N:ℝ)^3)^k/N|≤majorant k := by
  have pos : (0:ℝ)<N := by exact_mod_cast hN
  have fact : (0:ℝ)<(3*k+1).factorial := by exact_mod_cast Nat.factorial_pos _
  rw [abs_div,abs_of_pos pos,abs_mul,abs_of_nonneg (B_coeff_nonneg ..),abs_pow,abs_div,abs_neg,
    abs_of_nonneg hR,abs_of_pos (pow_pos pos _),div_pow,←pow_mul]
  unfold majorant
  rw [le_div_iff₀ fact,div_mul_eq_mul_div,div_le_iff₀ pos]
  have env:=endpoint_envelope N k hN
  have powbd : R^k≤(3800:ℝ)^k := pow_le_pow_left₀ hR hr _
  have e0 := mul_le_mul env powbd (pow_nonneg hR _) (by positivity)
  have den := pow_pos pos (3*k)
  apply (le_of_mul_le_mul_right (a:=(N:ℝ)^(3*k)) _ den)
  rw [pow_succ] at e0
  rw [show (76000:ℝ)=20*3800 by norm_num,mul_pow]
  field_simp
  nlinarith only [e0]

private theorem majorant_ratio (k : ℕ) (hk : 41≤k) : majorant (k+1) ≤ (1/2)*majorant k := by
  have a : (152000:ℝ)≤(3*(k:ℝ)+4)*(3*k+3)*(3*k+2) := by
    have h : (41:ℝ)≤k := by exact_mod_cast hk
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (sq_nonneg (k:ℝ)),mul_nonneg (sub_nonneg.mpr h) (by positivity : 0≤(k:ℝ))]
  unfold majorant
  rw [show 3*(k+1)+1=(3*k+1)+1+1+1 by omega,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,pow_succ]
  push_cast
  have f : (0:ℝ)<(3*k+1).factorial := by exact_mod_cast Nat.factorial_pos _
  have D : (0:ℝ)<((3*(k:ℝ)+1+1+1+1)*((3*k+1+1+1)*((3*k+1+1)*(3*k+1).factorial))) := by positivity
  rw [show (1/2:ℝ)*(25*76000^k/(3*k+1).factorial)=(25*76000^k)/(2*(3*k+1).factorial) by ring]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_left a (by positivity : 0≤(25:ℝ)*76000^k*(3*k+1).factorial)]

private theorem majorant_start : 2*majorant 41 < 1/256 := by
  change 2*(25*(76000:ℝ)^41/((124:ℕ).factorial:ℝ))<1/256
  have f : (0:ℝ)<(124:ℕ).factorial := by exact_mod_cast Nat.factorial_pos _
  rw [←mul_div_assoc,div_lt_div_iff₀ f (by norm_num)]
  exact_mod_cast (show 2*(25*76000^41)*256 < 1*(124:ℕ).factorial by decide +kernel)

private theorem geometric_tail (L : ℕ) :
    (∑ j∈range L, majorant (41+j)) + 2*majorant (41+L) ≤ 2*majorant 41 := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ]
    have rat:=majorant_ratio (41+L) (by omega)
    change _ + 2*majorant ((41+L)+1) ≤ _
    linarith

/-- All six endpoint radii satisfy the same strict, rank-uniform remainder estimate. -/
theorem endpoint_tail {N : ℕ} (hN : 0 < N) {R : ℝ} (hR : 0≤R) (hr : R≤3800) :
    |(B N).eval (-R/(N:ℝ)^3)/N-scaledHead N R| < 1/256 := by
  let L := (B N).natDegree+1
  have degree : (B N).natDegree < 41+L := by dsimp [L];omega
  rw [Polynomial.eval_eq_sum_range' degree,div_eq_mul_inv,Finset.sum_mul,Finset.sum_range_add,scaledHead]
  simp only [←div_eq_mul_inv,add_sub_cancel_left]
  calc
    _ ≤ ∑ j∈range L, |(B N).coeff (41+j)*(-R/(N:ℝ)^3)^(41+j)/N| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ j∈range L, majorant (41+j) := sum_le_sum fun j _ => term_bound hN hR hr _
    _ < _ := by
      have h:=geometric_tail L
      have z : 0≤majorant (41+L) := by unfold majorant;positivity
      linarith only [h,z,majorant_start]

end BigDescents132.AllRanks
