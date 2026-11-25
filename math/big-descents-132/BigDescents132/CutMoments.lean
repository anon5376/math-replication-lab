import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace BigDescents132.Cut
open Real Set MeasureTheory Filter
open scoped Topology

noncomputable def betaWeight (a b x : ℝ) := x^(a-1)*(1-x)^(b-1)

/-- The beta-prime density and its unnormalized mass on the positive ray. -/
noncomputable def rayWeight (a b v : ℝ) := v^(a-1)/(1+v)^(a+b)

theorem unit_beta {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (betaWeight a b) (Ioo 0 1) ∧
    ∫ x in Ioo 0 1, betaWeight a b x = Gamma a * Gamma b / Gamma (a+b) := by
  let f := fun x : ℝ => (x:ℂ)^((a:ℂ)-1) * (1-(x:ℂ))^((b:ℂ)-1)
  have e (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) : f x = (betaWeight a b x : ℂ) := by
    dsimp [f,betaWeight]
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le, Complex.ofReal_cpow (sub_nonneg.mpr hx.2.le)]
    push_cast
    rfl
  have hi : IntegrableOn f (Ioo 0 1) := by
    apply ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp
      (Complex.betaIntegral_convergent (u:=(a:ℂ)) (v:=(b:ℂ)) (by simpa) (by simpa))).mono_set
    exact Ioo_subset_Ioc_self
  have hc : (∫ x in Ioo 0 1, betaWeight a b x : ℝ) = Gamma a * Gamma b / Gamma (a+b) := by
    apply Complex.ofReal_injective
    have he : (∫ x in Ioo 0 1, f x) = ((∫ x in Ioo 0 1, betaWeight a b x : ℝ) : ℂ) := by
      rw [setIntegral_congr_fun measurableSet_Ioo e]
      exact integral_ofReal
    rw [← he, setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    change Complex.betaIntegral (a:ℂ) b = _
    have h := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (a:ℂ)) (t := (b:ℂ)) (by simpa) (by simpa)
    rw [← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal] at h
    push_cast
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr (Gamma_pos_of_pos (add_pos ha hb)).ne')).mpr
    rw [mul_comm]
    exact h.symm
  refine ⟨?_, hc⟩
  exact (integrableOn_congr_fun (f := fun x => (f x).re) (g := betaWeight a b)
    (fun x hx => by change (f x).re = _; rw [e x hx]; simp) measurableSet_Ioo).mp hi.re

private theorem substitution_image :
    (fun v : ℝ => v/(1+v)) '' Ioi 0 = Ioo 0 1 := by
  ext y
  constructor
  · rintro ⟨v,hv,rfl⟩
    change 0 < v at hv
    exact ⟨div_pos hv (by linarith), (div_lt_one (by linarith)).mpr (by linarith)⟩
  · intro hy
    have h := sub_pos.mpr hy.2
    refine ⟨y/(1-y), div_pos hy.1 h, ?_⟩
    field_simp

private theorem substitution_deriv (v : ℝ) (hv : v ∈ Ioi (0:ℝ)) :
    HasDerivWithinAt (fun x : ℝ => x/(1+x)) (1/(1+v)^2) (Ioi 0) v := by
  have h : 1+v ≠ 0 := by have := mem_Ioi.mp hv; positivity
  convert ((hasDerivAt_id v).div ((hasDerivAt_const v (1:ℝ)).add (hasDerivAt_id v)) h).hasDerivWithinAt using 1
  dsimp
  ring

private theorem substitution_inj : InjOn (fun v : ℝ => v/(1+v)) (Ioi 0) := by
  intro x hx y hy he
  have hx' : 0<x := hx
  have hy' : 0<y := hy
  have h := (div_eq_div_iff (by positivity : 1+x ≠ 0) (by positivity : 1+y ≠ 0)).mp he
  linarith

private theorem substitution_weight (a b v : ℝ) (hv : v ∈ Ioi (0:ℝ)) :
    |1/(1+v)^2| • betaWeight a b (v/(1+v)) = rayWeight a b v := by
  have hv' : 0<v := hv
  have hp : 0<1+v := by positivity
  have hs : 1-v/(1+v) = 1/(1+v) := by field_simp
  rw [smul_eq_mul, abs_of_pos (by positivity), betaWeight, rayWeight, hs,
    Real.div_rpow hv'.le hp.le, Real.div_rpow (by norm_num : (0:ℝ) ≤ 1) hp.le, Real.one_rpow]
  have hp' : (1+v)^(a+b) = (1+v)^2 * ((1+v)^(a-1)*(1+v)^(b-1)) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_add hp, ← Real.rpow_add hp]
    congr 1
    ring
  rw [hp']
  field_simp [hp.ne', (Real.rpow_pos_of_pos hp (a-1)).ne', (Real.rpow_pos_of_pos hp (b-1)).ne']

/-- Evaluate the moments on (0,∞) by the change of variables x=v/(1+v). -/
theorem ray_beta {a b : ℝ} (ha : 0<a) (hb : 0<b) : IntegrableOn (rayWeight a b) (Ioi 0) ∧
    ∫ v in Ioi 0, rayWeight a b v = Gamma a * Gamma b / Gamma (a+b) := by
  obtain ⟨hi, he⟩ := unit_beta ha hb
  rw [← substitution_image] at hi he
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi substitution_deriv
    substitution_inj] at hi
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi substitution_deriv substitution_inj] at he
  exact ⟨(integrableOn_congr_fun (substitution_weight a b) measurableSet_Ioi).mp hi,
    (setIntegral_congr_fun measurableSet_Ioi (substitution_weight a b)).symm.trans he⟩

/-- The kernel v^(1/2) (1+v)^(-n-1) in the cut coefficient formula. -/
noncomputable def kernel (n : ℕ) (v : ℝ) := v^(1/2:ℝ)/(1+v)^(n+1)

noncomputable def moment (n : ℕ) (j : ℝ) : ℝ :=
  Gamma (3/2+j) * Gamma ((n:ℝ)-1/2-j) / Gamma ((n:ℝ)+1)

theorem moment_integral (n : ℕ) (j : ℝ) (ha : 0<3/2+j) (hb : 0<(n:ℝ)-1/2-j) :
    IntegrableOn (fun v => kernel n v * v^j) (Ioi (0:ℝ)) ∧
    ∫ v in Ioi (0:ℝ), kernel n v * v^j = moment n j := by
  have e (v : ℝ) (hv : v ∈ Ioi (0:ℝ)) :
      rayWeight (3/2+j) ((n:ℝ)-1/2-j) v = kernel n v * v^j := by
    have hv' : 0<v := hv
    rw [rayWeight, kernel, show 3/2+j-1 = 1/2+j by ring, Real.rpow_add hv',
      show 3/2+j+((n:ℝ)-1/2-j) = (n+1:ℕ) by push_cast; ring, Real.rpow_natCast]
    ring
  obtain ⟨hi,he⟩ := ray_beta ha hb
  refine ⟨(integrableOn_congr_fun e measurableSet_Ioi).mp hi, ?_⟩
  rw [← setIntegral_congr_fun measurableSet_Ioi e, he, moment]
  congr 2
  ring

theorem moment_pos (n : ℕ) (j : ℝ) (ha : 0<3/2+j) (hb : 0<(n:ℝ)-1/2-j) :
    0 < moment n j := div_pos (mul_pos (Gamma_pos_of_pos ha) (Gamma_pos_of_pos hb))
      (Gamma_pos_of_pos (by positivity))

theorem moment_step (n : ℕ) (j : ℝ) (ha : 0<3/2+j) (hb : 0<(n:ℝ)-3/2-j) :
    moment n (j+1) * ((n:ℝ)-3/2-j) = (3/2+j) * moment n j := by
  simp only [moment]
  rw [show 3/2+(j+1) = 3/2+j+1 by ring,
    show (n:ℝ)-1/2-(j+1) = (n:ℝ)-3/2-j by ring,
    show (n:ℝ)-1/2-j = ((n:ℝ)-3/2-j)+1 by ring,
    Gamma_add_one ha.ne', Gamma_add_one hb.ne']
  ring

/-- The real cut can require the inverse first moment at the coalescing pole. -/
theorem inverse_moment {n : ℕ} (hn : 1 ≤ n) : moment n (-1) = (2*n-1) * moment n 0 := by
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have h := moment_step n (-1) (by norm_num) (by linarith)
  norm_num at h
  linarith

/-- Uniform bounds for the three positive moments used in the complex cut.
The constant 7 applies simultaneously for n≥8. -/
theorem moments_le {n j : ℕ} (hn : 8 ≤ n) (hj : j ≤ 3) :
    moment n j ≤ moment n 0 * (7/(n:ℝ))^j := by
  have hn' : (8:ℝ) ≤ n := by exact_mod_cast hn
  induction j with
  | zero => simp
  | succ j ih =>
    have hj' : (j:ℝ) ≤ 2 := by exact_mod_cast (show j ≤ 2 by omega)
    have hb : 0<(n:ℝ)-3/2-j := by linarith
    have hm : 0 ≤ moment n (j:ℝ) := (moment_pos n j (by positivity) (by linarith)).le
    have hs := (eq_div_iff hb.ne').mpr (moment_step n j (by positivity) hb)
    have ratio : (3/2+(j:ℝ))/((n:ℝ)-3/2-j) ≤ 7/(n:ℝ) := by
      apply (div_le_div_iff₀ hb (by linarith)).mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hj') (show 0 ≤ (n:ℝ) from Nat.cast_nonneg n)]
    rw [Nat.cast_succ, hs, pow_succ]
    calc
      _ = moment n j * ((3/2+(j:ℝ))/((n:ℝ)-3/2-j)) := by ring
      _ ≤ moment n j * (7/(n:ℝ)) := mul_le_mul_of_nonneg_left ratio hm
      _ ≤ (moment n 0 * (7/(n:ℝ))^j) * (7/(n:ℝ)) := mul_le_mul_of_nonneg_right (ih (by omega)) (by positivity)
      _ = _ := by ring

private theorem natural_moment {n j : ℕ} (hn : 8 ≤ n) (hj : j ≤ 3) :
    IntegrableOn (fun v : ℝ => kernel n v * v^j) (Ioi 0) ∧
      ∫ v in Ioi (0:ℝ), kernel n v * v^j = moment n j := by
  have hn' : (8:ℝ) ≤ n := by exact_mod_cast hn
  have hj' : (j:ℝ) ≤ 3 := by exact_mod_cast hj
  simpa only [Real.rpow_natCast] using moment_integral n j (by positivity) (by linarith)

/-- Uniform error in the complex-cut integral for a multiplier U satisfying the
pointwise distortion bound from the branch-point geometry. -/
theorem complex_cut_error {n : ℕ} (hn : 8 ≤ n) {h K : ℝ} (hh : 0<h) (hK : 0≤K)
    (U : ℝ → ℂ) (hU : ContinuousOn U (Ioi 0))
    (pointwise : ∀ v ∈ Ioi (0:ℝ), ‖U v-1‖ ≤ K*(v/h)*(1+v/h)^2) :
    ‖(∫ v in Ioi (0:ℝ), kernel n v • U v) - (moment n 0:ℂ)‖ ≤
      K*moment n 0*((7/((n:ℝ)*h)) + 2*(7/((n:ℝ)*h))^2 + (7/((n:ℝ)*h))^3) := by
  obtain ⟨hi₁, he₁⟩ := natural_moment (j:=1) hn (by decide)
  obtain ⟨hi₂, he₂⟩ := natural_moment (j:=2) hn (by decide)
  obtain ⟨hi₃, he₃⟩ := natural_moment (j:=3) hn (by decide)
  have i₀ : IntegrableOn (kernel n) (Ioi 0) := by simpa using (natural_moment (j:=0) hn (by decide)).1
  have e₀ : ∫ v in Ioi (0:ℝ), kernel n v = moment n 0 := by
    simpa using (natural_moment (j:=0) hn (by decide)).2
  let D := fun v => (K/h)*(kernel n v*v^1) + (2*K/h^2)*(kernel n v*v^2) + (K/h^3)*(kernel n v*v^3)
  have hD : IntegrableOn D (Ioi 0) :=
    ((hi₁.const_mul _).add (hi₂.const_mul _)).add (hi₃.const_mul _)
  have bound : ∀ᵐ v ∂volume.restrict (Ioi 0), ‖kernel n v • (U v-1)‖ ≤ D v := by
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with v hv
    have hv' : 0<v := hv
    have hk : 0≤kernel n v := by unfold kernel; positivity
    rw [norm_smul, Real.norm_of_nonneg hk]
    calc
      _ ≤ kernel n v * (K*(v/h)*(1+v/h)^2) := mul_le_mul_of_nonneg_left (pointwise v hv) hk
      _ = D v := by dsimp [D]; ring
  have hdiff : IntegrableOn (fun v => kernel n v • (U v - 1)) (Ioi 0) :=
    hD.mono' (i₀.aestronglyMeasurable.smul ((hU.aestronglyMeasurable measurableSet_Ioi).sub
      aestronglyMeasurable_const)) bound
  have split (v : ℝ) : kernel n v • U v =
      kernel n v • (U v-1) + ((kernel n v : ℝ) : ℂ) := by simp [smul_sub, Complex.real_smul]
  simp_rw [split]
  have addInt : (∫ v in Ioi (0:ℝ), kernel n v • (U v-1) + (kernel n v : ℂ)) =
      (∫ v in Ioi (0:ℝ), kernel n v • (U v-1)) + (∫ v in Ioi (0:ℝ), (kernel n v : ℂ)) :=
    integral_add hdiff (i₀.ofReal (𝕜:=ℂ))
  have coeInt : (∫ v in Ioi (0:ℝ), (kernel n v : ℂ)) = (moment n 0:ℂ) := by
    rw [← e₀]
    exact integral_ofReal
  rw [addInt, coeInt, add_sub_cancel_right]
  calc
    _ ≤ ∫ v in Ioi (0:ℝ), D v := norm_integral_le_of_norm_le hD bound
    _ = K/h * moment n 1 + 2*K/h^2 * moment n 2 + K/h^3 * moment n 3 := by
      dsimp [D]
      erw [integral_add ((hi₁.const_mul (K/h)).add (hi₂.const_mul (2*K/h^2))) (hi₃.const_mul (K/h^3)),
        integral_add (hi₁.const_mul (K/h)) (hi₂.const_mul (2*K/h^2))]
      simp only [integral_const_mul, he₁, he₂, he₃, Nat.cast_one, Nat.cast_ofNat]
    _ ≤ K/h*(moment n 0*(7/(n:ℝ))^1) + 2*K/h^2*(moment n 0*(7/(n:ℝ))^2) +
        K/h^3*(moment n 0*(7/(n:ℝ))^3) := by
      gcongr
      · exact_mod_cast moments_le (j:=1) hn (by decide)
      · exact_mod_cast moments_le (j:=2) hn (by decide)
      · exact_mod_cast moments_le (j:=3) hn (by decide)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- On n*h≥7 the relative error of the complex cut is at most 28*K/(n*h). -/
theorem moving_complex_cut_bound {n : ℕ} (hn : 8 ≤ n) {h K : ℝ} (hh : 0<h) (hK : 0≤K)
    (hm : 7 ≤ (n:ℝ)*h) (U : ℝ → ℂ) (hU : ContinuousOn U (Ioi 0))
    (pointwise : ∀ v ∈ Ioi (0:ℝ), ‖U v-1‖ ≤ K*(v/h)*(1+v/h)^2) :
    ‖(∫ v in Ioi (0:ℝ), kernel n v • U v) - (moment n 0:ℂ)‖ / moment n 0 ≤ 28*K/((n:ℝ)*h) := by
  have hn' : (8:ℝ) ≤ n := by exact_mod_cast hn
  have hm0 := moment_pos n 0 (by norm_num) (by linarith)
  have hr : 7/((n:ℝ)*h) ≤ 1 := (div_le_one (by positivity)).mpr hm
  have hr0 : 0 ≤ 7/((n:ℝ)*h) := by positivity
  let r := 7/((n:ℝ)*h)
  have h₂ : r^2 ≤ r := by dsimp [r]; nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hr)]
  have h₃ : r^3 ≤ r := (show r^3 ≤ r^2 by rw [pow_succ]; nlinarith [mul_le_mul_of_nonneg_right hr (sq_nonneg r)]).trans h₂
  apply (div_le_iff₀ hm0).mpr
  apply (complex_cut_error hn hh hK U hU pointwise).trans
  calc
    K*moment n 0*(r+2*r^2+r^3) ≤ K*moment n 0*(4*r) := by gcongr; linarith
    _ = _ := by dsimp [r]; ring

end BigDescents132.Cut
