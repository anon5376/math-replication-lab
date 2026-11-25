import BigDescents132.ActualInterior

namespace BigDescents132.Slit
open Complex Set MeasureTheory
open scoped ComplexConjugate

variable {s : ℝ} (g : Points s)

noncomputable def Points.poleScale := ‖1-(s:ℂ)*g.u‖ / |1-s*g.r|
noncomputable def Points.scaledReal (N : ℕ) := g.relativeReal N/g.poleScale
noncomputable def Points.scaledRealMultiplier (v : ℝ) := g.poleScale • g.realMultiplier v

theorem Points.sr_gt : 1<s*g.r := by
  simpa [mul_comm] using (div_lt_iff₀ (zero_lt_one.trans g.parameter)).mp g.small.1

theorem Points.spole_ne : 1-(s:ℂ)*g.u≠0 := by
  intro e
  have h := congrArg im e
  simp [Complex.mul_im,(zero_lt_one.trans g.parameter).ne',g.upper.ne'] at h

theorem Points.poleScale_pos : 0<g.poleScale :=
  div_pos (norm_pos_iff.mpr g.spole_ne) (abs_pos.mpr (sub_ne_zero.mpr g.sr_gt.ne))

theorem Points.scaled_coefficient (n : ℕ) :
    (B (n+1)).eval (1-s)/(2*‖g.complexWeight (n+1)‖*Cut.moment (n+1) 0)=
    Cut.normalizedCuts (n+1) (g.unitPhase (n+1)) (g.scaledReal (n+1)) g.endReal
      g.upperMultiplier g.scaledRealMultiplier := by
  rw [g.normalized_coefficient]
  have e (v) : Cut.kernel (n+1) v • g.scaledRealMultiplier v =
      g.poleScale • (Cut.kernel (n+1) v • g.realMultiplier v) := smul_comm _ _ _
  simp only [Cut.normalizedCuts,Points.scaledReal,e,add_right_inj]
  rw [integral_smul,Complex.real_smul,Complex.re_ofReal_mul]
  have w := Cut.moment_pos (n+1) 0 (by norm_num) (by push_cast; linarith [Nat.cast_nonneg (α:=ℝ) n])
  field_simp [g.poleScale_pos.ne',w.ne']; ring

/-- Removing the real pole from the scalar prefactor leaves a pure modulus
ratio with exponential decay from the dominant pair. -/
theorem Points.scaled_real_size (N : ℕ) :
    |g.scaledReal N| = ‖g.realOther g.r‖/(2*‖g.rayOther g.u g.u‖) *
      (‖g.u‖/g.r)^(N+1) := by
  have hs := zero_lt_one.trans g.parameter
  have u0 := norm_pos_iff.mpr g.u_ne
  have A : g.rayOther g.u g.u≠0 := by simpa using g.rayOther_ne g.upper.ne' (le_rfl : (0:ℝ)≤0)
  have pi := Real.pi_pos
  have sp := norm_pos_iff.mpr g.spole_ne
  have rp := abs_pos.mpr (sub_ne_zero.mpr g.sr_gt.ne)
  have rpos := g.rpos
  have eq : ((g.realWeight N).re:ℂ)=g.realWeight N := Complex.ext rfl (g.realWeight_im _).symm
  have mag : |(g.realWeight N).re|=‖g.realWeight N‖ := by
    rw [←eq,Complex.norm_real,Real.norm_eq_abs]; rfl
  have eh : |g.scaledReal N|=‖g.realWeight N‖/(2*‖g.complexWeight N‖)/g.poleScale := by
    rw [Points.scaledReal,Points.relativeReal,abs_div,abs_div,mag,abs_of_pos g.poleScale_pos,
      abs_of_pos (mul_pos (by norm_num : (0:ℝ)<2) (norm_pos_iff.mpr (g.complexWeight_ne N)))]
  rw [eh]
  simp only [Points.realWeight,
    Points.complexWeight,weight,amplitude,Points.poleScale,norm_mul,norm_pow,norm_inv,norm_div,
    Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos pi,abs_of_pos rpos,
    show (1:ℂ)-(s:ℂ)=((1-s:ℝ):ℂ) by push_cast; rfl,
    show (1:ℂ)-(s:ℂ)*g.r=((1-s*g.r:ℝ):ℂ) by push_cast; rfl]
  have t0 : |1-s|≠0 := abs_ne_zero.mpr (sub_ne_zero.mpr g.parameter.ne)
  have a0 := norm_ne_zero_iff.mpr A
  rw [div_pow,pow_succ,pow_succ]
  field_simp [u0.ne',rpos.ne',sp.ne',rp.ne',t0,Real.pi_ne_zero,a0]
  ring

theorem Points.scaled_moving_cosine (n : ℕ) (hn : 8≤n+1) {h E K D c : ℝ}
    (hE : 0<E) (hEh : E≤h) (hK : 0≤K) (hD : 0≤D) (hc : 0<c) (hu : 7≤((n+1:ℕ):ℝ)*E)
    (complexBound : ∀ v∈Ioi (0:ℝ), ‖g.upperMultiplier v-1‖≤K*(v/h)*(1+v/h)^2)
    (realBound : (h=E ∧ ∀ v∈Ioo (0:ℝ) g.endReal, ‖g.scaledRealMultiplier v‖≤K*(h/v)*(1+v/h)^2) ∨
      (∀ v∈Ioo (0:ℝ) g.endReal, ‖g.scaledRealMultiplier v‖≤K*(1+v/h)^2))
    (damping : |g.scaledReal (n+1)|≤D*Real.exp (-(c*(((n+1:ℕ):ℝ)*E)))) :
    |(B (n+1)).eval (1-s)/(2*‖g.complexWeight (n+1)‖*Cut.moment (n+1) 0)-
      Real.cos (g.complexWeight (n+1)).arg|≤(28*K+6*D*K/c^2)/(((n+1:ℕ):ℝ)*E) := by
  have ne := g.complexWeight_ne (n+1)
  have un : ‖g.unitPhase (n+1)‖=1 := by simp [Points.unitPhase,norm_div,norm_ne_zero_iff.mpr ne]
  have wave : (g.unitPhase (n+1)).re=Real.cos (g.complexWeight (n+1)).arg := by
    rw [Points.unitPhase,Complex.div_ofReal_re,Complex.cos_arg ne]
  rw [g.scaled_coefficient]
  exact Cut.moving_cut_cosine hn hE hEh hK hD hc hu _ un wave _ _ g.upper_continuous
    complexBound realBound damping

end BigDescents132.Slit
