import BigDescents132.CatalanIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace BigDescents132.Peak
open Real Complex Set MeasureTheory Filter
open scoped Topology

noncomputable def ray : ℂ := Complex.exp (((Real.pi/3:ℝ):ℂ)*I)
theorem ray_re : ray.re=1/2 := by simp [ray,Complex.exp_re,Real.cos_pi_div_three]
theorem ray_im : ray.im=Real.sqrt 3/2 := by simp [ray,Complex.exp_im,Real.sin_pi_div_three]
theorem ray_norm : ‖ray‖=1 := by simp [ray,Complex.norm_exp]
theorem ray_ne : ray≠0 := Complex.exp_ne_zero _
theorem ray_cube : ray^3= -1 := by
  rw [ray,←Complex.exp_nat_mul,←Complex.exp_pi_mul_I]
  congr 1; push_cast; ring

noncomputable def lap (b : ℂ) (r t : ℝ) := ((t^r:ℝ):ℂ)*Complex.exp (-b*(t:ℂ))

theorem norm_lap {b : ℂ} {r t : ℝ} (ht : 0≤t) :
    ‖lap b r t‖=t^r*Real.exp (-b.re*t) := by
  simp [lap,norm_mul,Complex.norm_exp,Complex.mul_re,Real.norm_of_nonneg (Real.rpow_nonneg ht _)]

theorem lap_integrable {b : ℂ} (hb : 0<b.re) {r : ℝ} (hr : -1<r) : IntegrableOn (lap b r) (Ioi 0) := by
  have H : IntegrableOn (fun t : ℝ => t^r*Real.exp (-b.re*t)) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_rpow hr (le_rfl : (1:ℝ)≤1) hb
  apply H.mono' (by apply Measurable.aestronglyMeasurable; unfold lap; fun_prop)
  exact ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => (norm_lap hx.le).le

/-- Integration by parts and the complex half-line Gaussian integral evaluate
the complex Laplace moment with exponent 1/2. -/
theorem lap_half {b : ℂ} (hb : 0<b.re) :
    (∫ x in Ioi (0:ℝ), lap b (1/2) x)=(Real.pi/b)^(1/2:ℂ)/(2*b) := by
  have bne : b≠0 := by intro e; simp [e] at hb
  have gm : (∫ t in Ioi (0:ℝ), lap b (-1/2) t)=(Real.pi/b)^(1/2:ℂ) := by
    rw [←integral_comp_rpow_Ioi_of_pos (g:=lap b (-1/2)) zero_lt_two]
    have eq (x : ℝ) (hx : x∈Ioi 0) :
        (2*x^((2:ℝ)-1)) • lap b (-1/2) (x^(2:ℝ)) = (2:ℂ)*Complex.exp (-b*(x:ℂ)^2) := by
      have p : 0<x := hx
      have r : (x^(2:ℝ))^(-1/2:ℝ)=x⁻¹ := by rw [←Real.rpow_mul p.le,show (2:ℝ)*(-1/2)= -1 by norm_num,Real.rpow_neg_one]
      rw [lap,r,Complex.real_smul]
      norm_num
      field_simp [p.ne']; ring
    rw [setIntegral_congr_fun measurableSet_Ioi eq,integral_const_mul,integral_gaussian_complex_Ioi hb]
    ring
  let f := lap b (1/2)
  let fp := fun x => (1/2:ℂ)*lap b (-1/2) x-b*f x
  have D (x : ℝ) (hx : x∈Ioi 0) : HasDerivAt f (fp x) x := by
    have p : 0<x := hx
    have m := (Real.hasDerivAt_rpow_const (p:=1/2) (Or.inl p.ne')).ofReal_comp
    have ex := ((Complex.ofRealCLM.hasFDerivAt (x:=x)).hasDerivAt.const_mul (-b)).cexp
    convert m.mul ex using 1
    · dsimp [fp,f,lap]; norm_num; ring
  have G : IntegrableOn fp (Ioi 0) := ((lap_integrable hb (by norm_num : (-1:ℝ)< -1/2)).const_mul (1/2:ℂ)).sub
    ((lap_integrable hb (by norm_num : (-1:ℝ)<1/2)).const_mul b)
  have lim : Tendsto f atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1/2) b.re hb)
    filter_upwards [Ioi_mem_atTop (0:ℝ)] with x hx
    simpa [f,neg_mul] using (norm_lap (b:=b) (r:=1/2) hx.le).le
  have cont : Continuous f := by
    dsimp [f,lap]
    exact (Complex.continuous_ofReal.comp (Real.continuous_rpow_const (by norm_num))).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  have H := integral_Ioi_of_hasDerivAt_of_tendsto cont.continuousWithinAt D G lim
  have f0 : f 0=0 := by simp [f,lap,Real.zero_rpow (by norm_num : (1/2:ℝ)≠0)]
  rw [f0,sub_zero] at H
  dsimp only [fp] at H
  rw [integral_sub ((lap_integrable hb (by norm_num : (-1:ℝ)< -1/2)).const_mul _) ((lap_integrable hb (by norm_num : (-1:ℝ)<1/2)).const_mul _),
    integral_const_mul,integral_const_mul,gm] at H
  apply (eq_div_iff (mul_ne_zero (by norm_num : (2:ℂ)≠0) bne)).mpr
  linear_combination -2*H

/-- The special angle pi/3 makes the leading moment a negative imaginary scalar. -/
theorem ray_lap {q : ℝ} (qp : 0<q) :
    (∫ x in Ioi (0:ℝ), lap ((q:ℂ)*ray) (1/2) x)=
      ((gammaHalf/(q*Real.sqrt q):ℝ):ℂ)*(-I) := by
  have bp : 0<((q:ℂ)*ray).re := by rw [Complex.re_ofReal_mul,ray_re]; positivity
  rw [lap_half bp]
  let z : ℂ := ((Real.sqrt (Real.pi/q):ℝ):ℂ)*((-I)*ray)
  have zp : 0<z.re := by
    rw [show z.re=Real.sqrt (Real.pi/q)*ray.im by simp [z,Complex.mul_re]]
    rw [ray_im]; positivity
  have Z : z^2=(Real.pi:ℂ)/((q:ℂ)*ray) := by
    apply (eq_div_iff (mul_ne_zero (ofReal_ne_zero.mpr qp.ne') ray_ne)).mpr
    have sq := Real.sq_sqrt (div_pos Real.pi_pos qp).le
    have sqc : ((Real.sqrt (Real.pi/q):ℝ):ℂ)^2=(Real.pi:ℂ)/(q:ℂ) := by exact_mod_cast sq
    calc
      _ = ((Real.sqrt (Real.pi/q):ℝ):ℂ)^2*I^2*(q:ℂ)*ray^3 := by dsimp [z]; ring
      _ = _ := by rw [sqc,Complex.I_sq,ray_cube]; field_simp [ofReal_ne_zero.mpr qp.ne']
  rw [←Z,one_div,Complex.sq_cpow_two_inv zp]
  dsimp [z]
  rw [gamma_value,Real.sqrt_div Real.pi_pos.le]
  push_cast
  field_simp [qp.ne',ray_ne,(Real.sqrt_pos_of_pos qp).ne']; ring

end BigDescents132.Peak
