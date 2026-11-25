import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace BigDescents132.Far
open Finset Real Complex

private noncomputable def angle (u : ℝ) : ℂ := (u : ℂ)*I

private theorem phase_term (w : ℝ) (e n : ℕ) :
    (Complex.exp (angle (-(e:ℝ)*π/3)) *
      ((w:ℂ) * Complex.exp (angle (π/3)))^n / (n.factorial:ℂ)).re =
      w^n / n.factorial * Real.cos (((n:ℝ)-e)*π/3) := by
  have h : angle (-(e:ℝ)*π/3) + (n:ℂ)*angle (π/3) =
      angle (((n:ℝ)-e)*π/3) := by unfold angle; push_cast; ring
  rw [mul_pow, ← Complex.exp_nat_mul, ← mul_left_comm, ← Complex.exp_add, h]
  rw [← Complex.ofReal_natCast, Complex.div_ofReal_re, ← Complex.ofReal_pow,
    Complex.re_ofReal_mul, Complex.exp_re]
  simp [angle, div_mul_eq_mul_div, mul_comm]

private theorem phase_value (w : ℝ) (e : ℕ) :
    (Complex.exp (angle (-(e:ℝ)*π/3)) *
      Complex.exp ((w:ℂ) * Complex.exp (angle (π/3)))).re =
      Real.exp (w/2) * Real.cos (Real.sqrt 3*w/2-e*π/3) := by
  rw [← Complex.exp_add, Complex.exp_re]
  have h : Complex.exp (angle (π/3)) =
      ((1/2:ℝ):ℂ) + ((Real.sqrt 3/2:ℝ):ℂ)*I := by
    rw [angle, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      Real.cos_pi_div_three, Real.sin_pi_div_three]
  rw [h]
  simp [angle, Complex.mul_re, Complex.mul_im]
  congr 2
  ring

private theorem residue_phase (e r : Fin 3) :
    (-1:ℝ)^e.val * (-1:ℝ)^r.val + 2*Real.cos (((r.val:ℝ)-e.val)*π/3) =
      if r=e then 3 else 0 := by
  have hp : Real.cos (2*π/3) = -(1/2:ℝ) := by
    rw [show 2*π/3 = π-π/3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
  fin_cases e <;> fin_cases r <;>
    norm_num [Real.cos_pi_div_three, hp, show -(2*π)/3 = -(2*π/3) by ring,
      show -π/3 = -(π/3) by ring, show -(2:ℝ)*π/3 = -(2*π/3) by ring]

private theorem selected_term (w : ℝ) (e r : Fin 3) (j : ℕ) :
    let n := j*3+r.val
    (-1:ℝ)^e.val * ((-w)^n / n.factorial) +
      2*(w^n / n.factorial * Real.cos (((n:ℝ)-e.val)*π/3)) =
      if r=e then 3*(-1:ℝ)^j*w^n/n.factorial else 0 := by
  dsimp only
  have hn : (-1:ℝ)^(j*3+r.val) = (-1:ℝ)^j * (-1:ℝ)^r.val := by
    rw [pow_add, mul_comm j 3, pow_mul]; norm_num
  have ha : (((j*3+r.val:ℕ):ℝ)-e.val)*π/3 =
      ((r.val:ℝ)-e.val)*π/3 + (j:ℝ)*π := by push_cast; ring
  rw [show -w = (-1)*w by ring, mul_pow, hn, ha, Real.cos_add_nat_mul_pi]
  have q := residue_phase e r
  split <;> rename_i hr
  · rw [if_pos hr] at q
    linear_combination ((-1:ℝ)^j*w^(j*3+r.val)/((j*3+r.val).factorial:ℝ))*q
  · rw [if_neg hr] at q
    linear_combination ((-1:ℝ)^j*w^(j*3+r.val)/((j*3+r.val).factorial:ℝ))*q

/-- The reciprocal endpoint series indexed by the degree defect. -/
noncomputable def farLimit (e : ℕ) (y : ℝ) : ℝ :=
  ∑' j : ℕ, (e.factorial:ℝ)*(y/2)^j/(3*j+e).factorial

/-- The third-roots-of-unity filter in real form. -/
theorem filtered_exp (e : Fin 3) (w : ℝ) :
    HasSum (fun j : ℕ => 3*(-1:ℝ)^j*w^(j*3+e.val)/(j*3+e.val).factorial)
      ((-1:ℝ)^e.val * Real.exp (-w) +
       2*(Real.exp (w/2)*Real.cos (Real.sqrt 3*w/2-e.val*π/3))) := by
  have hr := (NormedSpace.expSeries_div_hasSum_exp ℝ (-w)).mul_left ((-1:ℝ)^e.val)
  have hc := (Complex.hasSum_re ((NormedSpace.expSeries_div_hasSum_exp ℂ
    ((w:ℂ)*Complex.exp (angle (π/3)))).mul_left (Complex.exp (angle (-(e.val:ℝ)*π/3))))).mul_left 2
  simp only [← Real.exp_eq_exp_ℝ] at hr
  simp only [← Complex.exp_eq_exp_ℂ, phase_value, ← mul_div_assoc, phase_term] at hc
  have hs := (Nat.divModEquiv 3).symm.hasSum_iff.mpr (hr.add hc)
  apply hs.prod_fiberwise
  intro j
  dsimp [Function.comp_def]
  convert hasSum_fintype (_ : Fin 3 → ℝ) using 1
  symm
  rw [Finset.sum_eq_single_of_mem e (Finset.mem_univ e)]
  · simpa using selected_term w e e j
  · intro r _ hr
    simpa [hr] using selected_term w e r j

theorem farLimit_closed (e : Fin 3) {w : ℝ} (hw : 0<w) :
    farLimit e.val (-2*w^3) = e.val.factorial / (3*w^e.val) *
      ((-1:ℝ)^e.val * Real.exp (-w) +
       2*(Real.exp (w/2)*Real.cos (Real.sqrt 3*w/2-e.val*π/3))) := by
  have h := (filtered_exp e w).mul_left ((e.val.factorial:ℝ)/(3*w^e.val))
  unfold farLimit
  rw [← h.tsum_eq]
  apply tsum_congr
  intro j
  rw [show -2*w^3/2=(-1)*w^3 by ring, mul_pow, pow_add, mul_comm j 3, pow_mul]
  field_simp [hw.ne']
  ring

noncomputable def witness (j e : ℕ) : ℝ := 2*((j:ℝ)*π+e*π/3)/Real.sqrt 3

/-- Alternating sign at every indexed witness in all three residue classes. -/
theorem farLimit_witness (e : Fin 3) {j : ℕ} (hj : 0<j) :
    0 < (-1:ℝ)^j * farLimit e.val (-2*(witness j e.val)^3) := by
  have hj' : 0<(j:ℝ) := by exact_mod_cast hj
  have hroot : 0<Real.sqrt 3 := by positivity
  have hp := Real.pi_pos
  have hw : 0<witness j e.val := by unfold witness; positivity
  have hangle : Real.sqrt 3*witness j e.val/2-e.val*π/3 = (j:ℝ)*π := by
    unfold witness
    field_simp
    ring
  rw [farLimit_closed e hw, hangle]
  have hc : Real.cos ((j:ℝ)*π) = (-1:ℝ)^j := by
    simpa using Real.cos_nat_mul_pi_sub 0 j
  rw [hc]
  have he := Real.exp_lt_exp.mpr (show -witness j e.val < witness j e.val/2 by linarith)
  have hpos := Real.exp_pos (-witness j e.val)
  have hfac : 0 < (e.val.factorial:ℝ)/(3*witness j e.val^e.val) := by positivity
  rcases neg_one_pow_eq_or ℝ j with hjp|hjp <;>
    rcases neg_one_pow_eq_or ℝ e.val with hep|hep <;>
    rw [hjp,hep] <;> nlinarith [mul_pos hfac (sub_pos.mpr he),
      mul_pos hfac (Real.exp_pos (witness j e.val/2)), mul_pos hfac hpos]

end BigDescents132.Far
