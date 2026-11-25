import BigDescents132.CutMoments

namespace BigDescents132.Cut
open Real Set MeasureTheory

/-- A bound for a real-cut integral up to an arbitrary endpoint. The pole
factor can cost one inverse moment when the branch points coalesce at 1. -/
theorem real_cut_bound {n : ℕ} (hn : 8≤n) {h K T : ℝ} (hh : 0<h) (hK : 0≤K)
    (V : ℝ → ℂ)
    (pointwise : ∀ v∈Ioo (0:ℝ) T, ‖V v‖≤K*(h/v)*(1+v/h)^2) :
    ‖∫ v in Ioo (0:ℝ) T, kernel n v • V v‖ ≤
      K*moment n 0*(h*(2*n-1)+2+7/((n:ℝ)*h)) := by
  have hn' : (8:ℝ)≤n := by exact_mod_cast hn
  have hm := moment_integral n (-1) (by norm_num) (by linarith)
  have hz := moment_integral n 0 (by norm_num) (by linarith)
  have hp := moment_integral n 1 (by norm_num) (by linarith)
  simp only [Real.rpow_neg_one, Real.rpow_zero, Real.rpow_one, mul_one] at hm hz hp
  let D := fun v => (K*h)*(kernel n v*v⁻¹)+2*K*kernel n v+(K/h)*(kernel n v*v)
  have Di : IntegrableOn D (Ioi 0) :=
    ((hm.1.const_mul (K*h)).add (hz.1.const_mul (2*K))).add (hp.1.const_mul (K/h))
  have hk (v : ℝ) (hv : 0<v) : 0≤kernel n v := by unfold kernel; positivity
  have bound : ∀ᵐ v ∂volume.restrict (Ioo 0 T), ‖kernel n v • V v‖≤D v := by
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioo] with v hv
    rw [norm_smul,Real.norm_of_nonneg (hk v hv.1)]
    calc
      _ ≤ kernel n v*(K*(h/v)*(1+v/h)^2) := mul_le_mul_of_nonneg_left (pointwise v hv) (hk v hv.1)
      _ = D v := by dsimp [D]; field_simp [hv.1.ne',hh.ne']; ring
  have posD : ∀ᵐ v ∂volume.restrict (Ioi 0), 0≤D v := by
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with v hv
    have hv' : 0<v := hv
    have hk' := hk v hv'
    dsimp [D]
    positivity
  calc
    _ ≤ ∫ v in Ioo (0:ℝ) T, D v := norm_integral_le_of_norm_le (Di.mono_set Ioo_subset_Ioi_self) bound
    _ ≤ ∫ v in Ioi (0:ℝ), D v := setIntegral_mono_set Di posD (Filter.Eventually.of_forall (fun _ hx => hx.1))
    _ = K*h*moment n (-1)+2*K*moment n 0+K/h*moment n 1 := by
      dsimp [D]
      erw [integral_add ((hm.1.const_mul (K*h)).add (hz.1.const_mul (2*K))) (hp.1.const_mul (K/h)),
        integral_add (hm.1.const_mul (K*h)) (hz.1.const_mul (2*K))]
      simp only [integral_const_mul,hm.2,hz.2,hp.2]
    _ ≤ K*h*((2*n-1)*moment n 0)+2*K*moment n 0+K/h*(moment n 0*(7/(n:ℝ))) := by
      rw [inverse_moment (by omega)]
      gcongr
      simpa using moments_le (j:=1) hn (by decide)
    _ = _ := by simp [div_eq_mul_inv]; ring

/-- Away from the coalescing pole the real multiplier costs only ordinary
moments. This bound holds for the full range of the truncated real cut. -/
theorem regular_real_cut_bound {n : ℕ} (hn : 8≤n) {h K T : ℝ} (hh : 0<h) (hK : 0≤K)
    (V : ℝ → ℂ)
    (pointwise : ∀ v∈Ioo (0:ℝ) T, ‖V v‖≤K*(1+v/h)^2) :
    ‖∫ v in Ioo (0:ℝ) T, kernel n v • V v‖ ≤
      K*moment n 0*(1+7/((n:ℝ)*h))^2 := by
  have hn' : (8:ℝ)≤n := by exact_mod_cast hn
  have hz := moment_integral n 0 (by norm_num) (by linarith)
  have hp := moment_integral n 1 (by norm_num) (by linarith)
  have hq := moment_integral n 2 (by norm_num) (by linarith)
  simp only [Real.rpow_zero,Real.rpow_one,Real.rpow_two,mul_one] at hz hp hq
  let D := fun v => K*kernel n v + (2*K/h)*(kernel n v*v) + (K/h^2)*(kernel n v*v^2)
  have Di : IntegrableOn D (Ioi 0) :=
    ((hz.1.const_mul K).add (hp.1.const_mul (2*K/h))).add (hq.1.const_mul (K/h^2))
  have hk (v : ℝ) (hv : 0<v) : 0≤kernel n v := by unfold kernel; positivity
  have bound : ∀ᵐ v ∂volume.restrict (Ioo 0 T), ‖kernel n v • V v‖≤D v := by
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioo] with v hv
    rw [norm_smul,Real.norm_of_nonneg (hk v hv.1)]
    calc
      _ ≤ kernel n v*(K*(1+v/h)^2) := mul_le_mul_of_nonneg_left (pointwise v hv) (hk v hv.1)
      _ = D v := by dsimp [D]; ring
  have posD : ∀ᵐ v ∂volume.restrict (Ioi 0), 0≤D v := by
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with v hv
    have hv' : 0<v := hv
    have hk' := hk v hv'
    dsimp [D]; positivity
  calc
    _ ≤ ∫ v in Ioo (0:ℝ) T, D v := norm_integral_le_of_norm_le (Di.mono_set Ioo_subset_Ioi_self) bound
    _ ≤ ∫ v in Ioi (0:ℝ), D v := setIntegral_mono_set Di posD (Filter.Eventually.of_forall (fun _ hx => hx.1))
    _ = K*moment n 0+(2*K/h)*moment n 1+(K/h^2)*moment n 2 := by
      dsimp [D]
      erw [integral_add ((hz.1.const_mul K).add (hp.1.const_mul (2*K/h))) (hq.1.const_mul (K/h^2)),
        integral_add (hz.1.const_mul K) (hp.1.const_mul (2*K/h))]
      simp only [integral_const_mul,hz.2,hp.2,hq.2]
    _ ≤ K*moment n 0+(2*K/h)*(moment n 0*(7/(n:ℝ)))+(K/h^2)*(moment n 0*(7/(n:ℝ))^2) := by
      gcongr
      · simpa using moments_le (j:=1) hn (by decide)
      · simpa using moments_le (j:=2) hn (by decide)
    _ = _ := by simp [div_eq_mul_inv]; ring

end BigDescents132.Cut
