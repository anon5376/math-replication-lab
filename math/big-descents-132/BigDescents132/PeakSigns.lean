import BigDescents132.PeakApprox
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Complex.ExponentialBounds

namespace BigDescents132.Peak
open Real

private theorem gamma_lower : (5/6:ℝ)<gammaHalf := by
  rw [gamma_value]
  nlinarith [Real.pi_gt_three,Real.sq_sqrt Real.pi_pos.le,Real.sqrt_nonneg Real.pi]

private theorem first_exact {q : ℝ} (qp : 0<q) :
    q*Real.sqrt q*((1/3)*(2/q)^(7/2:ℝ)*Real.Gamma (7/2))=
      (10*Real.sqrt 2/q^2)*gammaHalf := by
  rw [show (7/2:ℝ)=3+1/2 by norm_num,Real.rpow_add (div_pos (by norm_num) qp),←Real.sqrt_eq_rpow,
    Real.sqrt_div (by norm_num)]
  have gg : Real.Gamma (3+1/2)=(5/2)*(3/2)*gammaHalf := by
    rw [show (3+1/2:ℝ)=5/2+1 by norm_num,Real.Gamma_add_one (by norm_num),
      show (5/2:ℝ)=3/2+1 by norm_num,Real.Gamma_add_one (by norm_num)]
    dsimp [gammaHalf]; ring
  rw [gg,show (2/q)^(3:ℝ)=(2/q)^3 by norm_cast]
  field_simp [qp.ne',(Real.sqrt_pos_of_pos qp).ne']; ring

private theorem exp_five : 130<Real.exp 5 := by
  have h : (8/3:ℝ)<Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have HH := pow_lt_pow_left₀ h (by norm_num : (0:ℝ)≤8/3) (by decide : (5:ℕ)≠0)
  rw [←Real.exp_nat_mul] at HH
  norm_num at HH
  linarith

private theorem exp_controls {q : ℝ} (hq : 20≤q) :
    q*Real.sqrt q*Real.exp (-q/4)≤7/10 ∧ q*Real.sqrt q*Real.exp (-q/2)≤7/1000 := by
  have p : 0<q := by linarith
  have root : Real.sqrt q≤(9/40)*q := Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith [mul_nonneg p.le (sub_nonneg.mpr hq)]⟩
  have poly : q*Real.sqrt q ≤ 90*(q/20)^2 := by nlinarith only [mul_le_mul_of_nonneg_left root p.le]
  let x := (q-20)/8
  have xbd : q/20≤Real.exp x := by dsimp [x]; linarith [Real.add_one_le_exp ((q-20)/8)]
  have ei := pow_le_pow_left₀ (div_nonneg p.le (by norm_num)) xbd 2
  have eq : Real.exp x^2*Real.exp (-q/4)=Real.exp (-5) := by
    rw [←Real.exp_nat_mul,←Real.exp_add]; dsimp [x]; congr 1; ring
  have first : q*Real.sqrt q*Real.exp (-q/4)≤7/10 := calc
    _ ≤ (90*Real.exp x^2)*Real.exp (-q/4) := mul_le_mul_of_nonneg_right (poly.trans (mul_le_mul_of_nonneg_left ei (by norm_num))) (Real.exp_pos _).le
    _ = 90/Real.exp 5 := by rw [mul_assoc,eq,Real.exp_neg]; ring
    _ ≤ _ := (div_le_iff₀ (Real.exp_pos _)).mpr (by linarith [exp_five])
  have e : Real.exp (-q/4)≤1/100 := calc
    _ ≤ Real.exp (-5) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ _ := by rw [Real.exp_neg,←one_div]; exact one_div_le_one_div_of_le (by norm_num) (by linarith [exp_five])
  refine ⟨first,?_⟩
  calc
    _ = (q*Real.sqrt q*Real.exp (-q/4))*Real.exp (-q/4) := by rw [mul_assoc (q*_) _ _,←Real.exp_add]; congr 2; ring
    _ ≤ (7/10)*(1/100) := mul_le_mul first e (Real.exp_pos _).le (by norm_num)
    _ = _ := by norm_num

/-- The quantitative error is strictly smaller than the leading oscillation at
every real q ≥ 20. -/
theorem error_strict {q : ℝ} (hq : 20≤q) :
    2*Real.sqrt 3*Real.exp (q/2)*(innerErr q+tailErr q)+Real.sqrt Real.pi/Real.sqrt q < envelope q := by
  have qp : 0<q := by linarith
  have gp : 0<gammaHalf := by linarith [gamma_lower]
  have sqp := Real.sqrt_pos_of_pos qp
  have sr : 1≤Real.sqrt q := Real.one_le_sqrt.mpr (by linarith)
  have s3 : 1≤Real.sqrt 3 := Real.one_le_sqrt.mpr (by norm_num)
  have a : 10*Real.sqrt 2/q^2≤1/20 := by
    have rt : Real.sqrt 2≤2 := Real.sqrt_le_iff.mpr (by norm_num)
    apply (div_le_iff₀ (sq_pos_of_pos qp)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hq) (show 0≤q+20 by linarith)]
  have f := (first_exact qp).trans_le (mul_le_mul_of_nonneg_right a gp.le)
  have root : 2*Real.sqrt (1/2)/Real.sqrt 3≤1 := by
    apply (div_le_one (Real.sqrt_pos_of_pos (by norm_num))).mpr
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤1/2),Real.sq_sqrt (by norm_num : (0:ℝ)≤3),
      Real.sqrt_nonneg (1/2),Real.sqrt_nonneg 3]
  obtain ⟨ex,ex2⟩ := exp_controls hq
  have t : 2/q+4/q^2≤1 := by
    have a : 2/q≤1/2 := (div_le_iff₀ qp).mpr (by linarith)
    have b : 4/q^2≤1/2 := (div_le_iff₀ (sq_pos_of_pos qp)).mpr (by nlinarith [mul_nonneg qp.le (sub_nonneg.mpr hq)])
    linarith
  have qi : q/Real.sqrt 3≤q*Real.sqrt q := (div_le_self qp.le s3).trans (le_mul_of_one_le_right qp.le sr)
  have dc := mul_le_mul_of_nonneg_right qi (Real.exp_pos (-q/2)).le
  have A : q*Real.sqrt q*(innerErr q+tailErr q) + gammaHalf*(q/Real.sqrt 3*Real.exp (-q/2))<gammaHalf := by
    have u := mul_le_mul_of_nonneg_left root (show 0≤q*Real.sqrt q*Real.exp (-q/4) by positivity)
    have v := mul_le_mul_of_nonneg_left t (show 0≤q*Real.sqrt q*Real.exp (-q/2) by positivity)
    have z := mul_le_mul_of_nonneg_left (dc.trans ex2) gp.le
    dsimp [innerErr,tailErr]
    linarith only [f,u,v,z,ex,ex2,gamma_lower]
  have sn : Real.sqrt 3≠0 := (Real.sqrt_pos_of_pos (by norm_num : 0<(3:ℝ))).ne'
  have eq : Real.exp (-q/2)*Real.exp (q/2)=1 := by rw [←Real.exp_add,show -q/2+q/2=0 by ring,Real.exp_zero]
  have H := mul_lt_mul_of_pos_left A (show 0<2*Real.sqrt 3*Real.exp (q/2)/(q*Real.sqrt q) by positivity)
  convert H using 1
  · have g : Real.sqrt Real.pi=2*gammaHalf := by rw [gamma_value]; ring
    rw [g]; field_simp [qp.ne',sqp.ne',sn]
    linear_combination -2*Real.sqrt 3*Real.sqrt q*gammaHalf*q*eq
  · unfold envelope; ring

noncomputable def witness (i : ℕ) := 2*((i:ℝ)*Real.pi+5*Real.pi/6)/Real.sqrt 3

theorem witness_ge {i : ℕ} (hi : 5≤ i) : 20≤witness i := by
  have n : (5:ℝ)≤ i := by exact_mod_cast hi
  have p := Real.pi_gt_three
  have s : Real.sqrt 3≤7/4 := Real.sqrt_le_iff.mpr (by norm_num)
  unfold witness
  apply (le_div_iff₀ (Real.sqrt_pos_of_pos (by norm_num))).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr n) Real.pi_pos.le]

/-- Each indexed peak after the four separate rational checks has the sign
required to start the interior phase grid. -/
theorem witness_sign {i : ℕ} (hi : 5≤ i) :
    0<(-1:ℝ)^i*smallLimit (-(witness i)^3/4) := by
  let q := witness i
  have ge : 20≤q := witness_ge hi
  have qp : 0<q := by linarith
  have level : Real.sqrt 3*q/2-5*Real.pi/6=(i:ℝ)*Real.pi := by unfold q witness; field_simp; ring
  have cos : Real.cos ((i:ℝ)*Real.pi)=(-1:ℝ)^i := by simpa using Real.cos_nat_mul_pi_sub 0 i
  have bd := (peak_approx qp).trans_lt (error_strict ge)
  rw [level,cos,abs_lt] at bd
  rw [smallLimit_integral qp]
  have pref : 0<2/(Real.pi*q) := by positivity
  rcases neg_one_pow_eq_or ℝ i with p|p <;> rw [p] at bd ⊢
  · rw [one_mul]; apply mul_pos pref; linarith only [bd.1]
  · rw [neg_one_mul,neg_pos]; apply mul_neg_of_pos_of_neg pref; linarith only [bd.2]

end BigDescents132.Peak
