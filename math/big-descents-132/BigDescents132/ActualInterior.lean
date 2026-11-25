import BigDescents132.RayParam

namespace BigDescents132.Slit
open Complex Set MeasureTheory
open scoped ComplexConjugate

variable {s : ℝ} (g : Points s)

noncomputable def Points.complexWeight (N : ℕ) := weight s N g.u (g.rayOther g.u)
noncomputable def Points.realWeight (N : ℕ) := weight s N g.r g.realOther
noncomputable def Points.unitPhase (N : ℕ) := g.complexWeight N/(‖g.complexWeight N‖:ℂ)
noncomputable def Points.relativeReal (N : ℕ) := (g.realWeight N).re/(2*‖g.complexWeight N‖)
noncomputable def Points.upperMultiplier := multiplier s g.u (g.rayOther g.u)
noncomputable def Points.realMultiplier := multiplier s g.r g.realOther

private theorem pole_ne {v : ℝ} (hv : 0≤v) :
    1-(s:ℂ)*(g.u*(1+(v:ℂ)))≠0 := by
  intro e
  have hi := congrArg im e
  simp [Complex.mul_im,g.upper.ne',(zero_lt_one.trans g.parameter).ne',show (1+v:ℝ)≠0 by linarith] at hi

theorem Points.complexWeight_ne (N : ℕ) : g.complexWeight N≠0 := by
  have A : g.rayOther g.u g.u≠0 := by simpa using g.rayOther_ne g.upper.ne' (le_rfl : (0:ℝ)≤0)
  have p : 1-(s:ℂ)*g.u≠0 := by simpa using pole_ne g (le_rfl : (0:ℝ)≤0)
  have sc : (1:ℂ)-(s:ℂ)≠0 := by exact_mod_cast sub_ne_zero.mpr g.parameter.ne
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero g.u_ne)) (div_ne_zero A
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero))
      sc) g.u_ne) p))

theorem Points.upper_continuous : ContinuousOn g.upperMultiplier (Ioi 0) := by
  intro v hv
  have pos : 0<v := hv
  let z := fun v : ℝ => g.u*(1+(v:ℂ))
  have cz : Continuous z := by dsimp [z]; fun_prop
  obtain ⟨hr,hR,hc⟩ := ray_arguments g g.upper.ne' pos.le
  have other : ContinuousAt (g.rayOther g.u) (z v) :=
    (((radical_diff hr).continuousAt.mul (radical_diff hR).continuousAt).mul (radical_diff hc).continuousAt)
  have q : (1+(v:ℂ))*(1-(s:ℂ)*z v)≠0 :=
    mul_ne_zero (by exact_mod_cast (show 1+v≠0 by linarith)) (pole_ne g pos.le)
  apply ContinuousAt.continuousWithinAt
  have den : ContinuousAt (fun w : ℝ => (1+(w:ℂ))*(1-(s:ℂ)*z w)) v := by dsimp [z]; fun_prop
  exact (((other.comp cz.continuousAt).div_const _).mul_const _).div den q

theorem Points.realWeight_im (N : ℕ) : (g.realWeight N).im=0 := by
  have eq : conj (g.realWeight N)=g.realWeight N := by
    simp [Points.realWeight,weight,amplitude,g.realOther_fixed,map_ofNat]
  have hh := congrArg im eq
  simp at hh
  linarith

private theorem weight_reflect (N : ℕ) :
    weight s N (conj g.u) (g.rayOther (conj g.u))=conj (g.complexWeight N) := by
  have h := g.rayOther_conj g.upper.ne' (le_rfl : (0:ℝ)≤0)
  simp only [ofReal_zero,add_zero,mul_one] at h
  simp [weight,amplitude,Points.complexWeight,h,map_ofNat]

private theorem multiplier_reflect {v : ℝ} (hv : 0≤v) :
    multiplier s (conj g.u) (g.rayOther (conj g.u)) v=conj (g.upperMultiplier v) := by
  have h := g.rayOther_conj g.upper.ne' (le_rfl : (0:ℝ)≤0)
  simp only [ofReal_zero,add_zero,mul_one] at h
  simp [multiplier,Points.upperMultiplier,h,g.rayOther_conj g.upper.ne' hv]

private theorem reflected_integral (N : ℕ) :
    (∫ v in Ioi (0:ℝ), Cut.kernel N v • multiplier s (conj g.u) (g.rayOther (conj g.u)) v)=
      conj (∫ v in Ioi (0:ℝ), Cut.kernel N v • g.upperMultiplier v) := by
  rw [←integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  simp [multiplier_reflect g (show 0≤v from (show 0<v from hv).le),Complex.real_smul]

/-- Exact conjugate-pair and real-segment contributions, already in the
normalization of the beta-prime estimate. -/
theorem Points.cut_real_part (n : ℕ) :
    (B (n+1)).eval (1-s)=
      2*(g.complexWeight (n+1)*(∫ v in Ioi (0:ℝ), Cut.kernel (n+1) v • g.upperMultiplier v)).re+
      (g.realWeight (n+1)).re*(∫ v in Ioo (0:ℝ) g.endReal, Cut.kernel (n+1) v • g.realMultiplier v).re := by
  have e := g.coefficient_from_cuts n
  simp only [mul_add] at e
  rw [g.real_cut,g.complex_cut g.upper.ne',g.complex_cut (a:=conj g.u) (by simpa using g.upper.ne')] at e
  rw [weight_reflect g,reflected_integral g,←map_mul] at e
  let Z := ∫ v in Ioi (0:ℝ), Cut.kernel (n+1) v • g.upperMultiplier v
  let V := ∫ v in Ioo (0:ℝ) g.endReal, Cut.kernel (n+1) v • g.realMultiplier v
  change (↑((B (n+1)).eval (1-s)):ℂ) =
    g.realWeight (n+1)*V+g.complexWeight (n+1)*Z+conj (g.complexWeight (n+1)*Z) at e
  change _ = 2*(g.complexWeight (n+1)*Z).re+(g.realWeight (n+1)).re*V.re
  have h := congrArg Complex.re e
  simp only [ofReal_re,add_re,conj_re] at h
  rw [h,Complex.mul_re (g.realWeight (n+1)),g.realWeight_im]
  ring

theorem Points.normalizer_pos (n : ℕ) :
    0<2*‖g.complexWeight (n+1)‖*Cut.moment (n+1) 0 := by
  have hp := norm_pos_iff.mpr (g.complexWeight_ne (n+1))
  have wm := Cut.moment_pos (n+1) 0 (by norm_num) (by push_cast; linarith [Nat.cast_nonneg (α:=ℝ) n])
  positivity

/-- No contour or coefficient hypothesis is needed in this identification. -/
theorem Points.normalized_coefficient (n : ℕ) :
    (B (n+1)).eval (1-s)/(2*‖g.complexWeight (n+1)‖*Cut.moment (n+1) 0)=
    Cut.normalizedCuts (n+1) (g.unitPhase (n+1)) (g.relativeReal (n+1)) g.endReal
      g.upperMultiplier g.realMultiplier := by
  rw [g.cut_real_part]
  let N := n+1
  let A := g.complexWeight N
  let D := (g.realWeight N).re
  let W := Cut.moment N 0
  let Z := ∫ v in Ioi (0:ℝ), Cut.kernel N v • g.upperMultiplier v
  let V := (∫ v in Ioo (0:ℝ) g.endReal, Cut.kernel N v • g.realMultiplier v).re
  change (2*(A*Z).re+D*V)/(2*‖A‖*W)=(A/(‖A‖:ℂ)*(Z/(W:ℂ))).re + D/(2*‖A‖)*V/W
  have hA : 0<‖A‖ := norm_pos_iff.mpr (g.complexWeight_ne N)
  have hW : 0<W := Cut.moment_pos (n+1) 0 (by norm_num) (by push_cast; linarith [Nat.cast_nonneg (α:=ℝ) n])
  rw [div_mul_div_comm,←Complex.ofReal_mul,Complex.div_ofReal_re]
  field_simp [hA.ne',hW.ne']; ring

/-- Uniform cosine estimate for the literal polynomial under explicit
inequalities on its own radical multipliers and relative real-cut amplitude. -/
theorem Points.moving_coefficient_cosine (n : ℕ) (hn : 8≤n+1) {h E K D c : ℝ}
    (hE : 0<E) (hEh : E≤h) (hK : 0≤K) (hD : 0≤D) (hc : 0<c) (hu : 7≤((n+1:ℕ):ℝ)*E)
    (complexBound : ∀ v∈Ioi (0:ℝ), ‖g.upperMultiplier v-1‖≤K*(v/h)*(1+v/h)^2)
    (realBound : (h=E ∧ ∀ v∈Ioo (0:ℝ) g.endReal, ‖g.realMultiplier v‖≤K*(h/v)*(1+v/h)^2) ∨
      (∀ v∈Ioo (0:ℝ) g.endReal, ‖g.realMultiplier v‖≤K*(1+v/h)^2))
    (damping : |g.relativeReal (n+1)|≤D*Real.exp (-(c*(((n+1:ℕ):ℝ)*E)))) :
    |(B (n+1)).eval (1-s)/(2*‖g.complexWeight (n+1)‖*Cut.moment (n+1) 0)-
      Real.cos (g.complexWeight (n+1)).arg|≤(28*K+6*D*K/c^2)/(((n+1:ℕ):ℝ)*E) := by
  have ne := g.complexWeight_ne (n+1)
  have un : ‖g.unitPhase (n+1)‖=1 := by simp [Points.unitPhase,norm_div,(norm_ne_zero_iff.mpr ne)]
  have wave : (g.unitPhase (n+1)).re=Real.cos (g.complexWeight (n+1)).arg := by
    rw [Points.unitPhase,Complex.div_ofReal_re,Complex.cos_arg ne]
  rw [g.normalized_coefficient]
  exact Cut.moving_cut_cosine hn hE hEh hK hD hc hu _ un wave _ _ g.upper_continuous
    complexBound realBound damping

end BigDescents132.Slit
