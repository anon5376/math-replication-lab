import BigDescents132.UpperBounds

namespace BigDescents132.Slit
open Complex Set
open scoped ComplexConjugate

variable {s : ℝ} (g : Points s)

private theorem real_slope : ‖(g.r:ℂ)/(g.r-g.u)‖≤1+g.slope := by
  have δ := Complex.abs_im_le_norm ((g.r:ℂ)-g.u)
  simp [abs_of_pos g.upper] at δ
  have d := g.upper.trans_le δ
  have e := norm_add_le ((g.r:ℂ)-g.u) g.u
  rw [sub_add_cancel] at e
  rw [norm_div]
  calc
    _ ≤ (‖(g.r:ℂ)-g.u‖+‖g.u‖)/‖(g.r:ℂ)-g.u‖ := div_le_div_of_nonneg_right e d.le
    _ = 1+‖g.u‖/‖(g.r:ℂ)-g.u‖ := by rw [add_div,div_self d.ne']
    _ ≤ _ := add_le_add_left (div_le_div_of_nonneg_left (norm_nonneg _) g.upper δ) 1

private theorem realOthers_ratio {v : ℝ} (hv : v∈Ioo 0 g.endReal) :
    ‖g.realOther ((g.r:ℂ)*(1+(v:ℂ)))/g.realOther g.r‖≤1+(1+g.slope)*v := by
  let x := g.r*(1+v)
  have vp : 0<v := hv.1
  have hxr : g.r≤x := le_mul_of_one_le_right g.rpos.le (by linarith)
  have hR : x<g.R := by
    have h := hv.2
    change v<g.R/g.r-1 at h
    simpa [x,mul_comm] using (lt_div_iff₀ g.rpos).mp (show 1+v<g.R/g.r by linarith)
  have ec : (g.r:ℂ)*(1+(v:ℂ))=(x:ℂ) := by dsimp [x]; push_cast; rfl
  have rn := g.small.2.trans g.large.1
  have e (y : ℝ) (hy : y<g.R) : ‖radical g.R y‖^2=1-y/g.R := by
    rw [←norm_pow,radical_sq]
    have eq : argFactor g.R y=((1-y/g.R:ℝ):ℂ) := by unfold argFactor; push_cast; rfl
    rw [eq,Complex.norm_real,Real.norm_of_nonneg (sub_nonneg.mpr ((div_le_one g.Rpos).mpr hy.le))]
  have small : ‖rootRatio g.r g.R v‖≤1 := by
    rw [rootRatio,ec,norm_div]
    apply (div_le_one (norm_pos_iff.mpr (radical_ne (real_factor_mem g.Rpos rn)))).mpr
    have le : 1-x/g.R≤1-g.r/g.R := sub_le_sub_left (div_le_div_of_nonneg_right hxr g.Rpos.le) 1
    nlinarith [e x hR,e g.r rn,norm_nonneg (radical g.R g.r),norm_nonneg (radical g.R x)]
  have f (y : ℝ) (h : 0<y) : radical (conj g.u) y=conj (radical g.u y) := by
    simpa using radical_conj (nonreal_factor_mem g.upper.ne' h.ne')
  have cn : rootRatio g.r (conj g.u) v=conj (rootRatio g.r g.u v) := by
    rw [rootRatio,rootRatio,ec,f x (g.rpos.trans_le hxr),f g.r g.rpos,map_div₀]
  have eq : g.realOther ((g.r:ℂ)*(1+(v:ℂ)))/g.realOther g.r=
      rootRatio g.r g.R v*rootRatio g.r g.u v*rootRatio g.r (conj g.u) v := by
    simp [Points.realOther,rootRatio,div_eq_mul_inv,mul_inv]; ring
  have ne : (g.r:ℂ)≠g.u := by intro eq; exact g.upper.ne' (by rw [←eq]; rfl)
  rw [eq,cn,norm_mul,norm_mul,norm_conj,mul_assoc,←pow_two,←norm_pow,rootRatio_square g.u_ne ne]
  calc
    _ ≤ 1*‖1+(g.r:ℂ)/(g.r-g.u)*(v:ℂ)‖ := mul_le_mul_of_nonneg_right small (norm_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      apply (norm_add_le _ _).trans
      rw [norm_one,norm_mul,Complex.norm_real,Real.norm_of_nonneg vp.le]
      exact add_le_add_left (mul_le_mul_of_nonneg_right (real_slope g) vp.le) 1

noncomputable def Points.nearPole := ‖1-(s:ℂ)*g.u‖/(s*g.r)
noncomputable def Points.farPole := ‖1-(s:ℂ)*g.u‖/(s*g.r-1)

private theorem scaled_real_formula {v : ℝ} (hv : v∈Ioo 0 g.endReal) :
    ‖g.scaledRealMultiplier v‖=
    ‖g.realOther ((g.r:ℂ)*(1+(v:ℂ)))/g.realOther g.r‖ *
    (‖1-(s:ℂ)*g.u‖/((1+v)*(s*g.r*(1+v)-1))) := by
  have h := g.sr_gt
  have vp := hv.1
  have a : 1<s*g.r*(1+v) := by nlinarith [mul_pos (zero_lt_one.trans h) vp]
  have e : (1:ℂ)-(s:ℂ)*(g.r:ℂ)=((1-s*g.r:ℝ):ℂ) := by push_cast; rfl
  have f : (1:ℂ)-(s:ℂ)*((g.r:ℂ)*(1+(v:ℂ)))=((1-s*g.r*(1+v):ℝ):ℂ) := by push_cast; ring
  have E : 1+(v:ℂ)=((1+v:ℝ):ℂ) := by push_cast; rfl
  let A := g.realOther ((g.r:ℂ)*(1+(v:ℂ)))/g.realOther g.r
  change ‖g.poleScale • (A*(1-(s:ℂ)*g.r)/((1+(v:ℂ))*(1-(s:ℂ)*((g.r:ℂ)*(1+(v:ℂ))))))‖=‖A‖*_
  rw [norm_smul,Real.norm_of_nonneg g.poleScale_pos.le,norm_div,norm_mul,norm_mul,
    e,f,E,Complex.norm_real,Complex.norm_real,Complex.norm_real]
  simp only [Points.poleScale,Real.norm_eq_abs,abs_of_pos (by linarith : 0<1+v),
    abs_of_neg (sub_neg.mpr h),abs_of_neg (sub_neg.mpr a),neg_sub]
  have n1 := (sub_pos.mpr h).ne'
  have n2 := (sub_pos.mpr a).ne'
  field_simp [n1,n2,show 1+v≠0 by linarith]
  ring

/-- Real-cut bounds with and without the singular first inverse moment. -/
theorem Points.real_bounds {v : ℝ} (hv : v∈Ioo 0 g.endReal) :
    ‖g.scaledRealMultiplier v‖≤(1+(1+g.slope)*v)*(g.nearPole/v) ∧
    ‖g.scaledRealMultiplier v‖≤(1+(1+g.slope)*v)*g.farPole := by
  have vp := hv.1
  have sr := g.sr_gt
  have sr0 := zero_lt_one.trans sr
  let b := s*g.r*(1+v)-1
  have le1 : s*g.r*v≤b := by dsimp [b]; nlinarith
  have le2 : s*g.r-1≤b := by dsimp [b]; nlinarith [mul_nonneg sr0.le vp.le]
  have bp : 0<b := (sub_pos.mpr sr).trans_le le2
  have le : b≤(1+v)*b := by nlinarith [mul_nonneg vp.le bp.le]
  have pos : 0≤1+(1+g.slope)*v := by nlinarith [g.slope_ge_one,mul_nonneg (show 0≤g.slope by linarith [g.slope_ge_one]) vp.le]
  have num := norm_nonneg (1-(s:ℂ)*g.u)
  rw [scaled_real_formula g hv]
  constructor
  · apply mul_le_mul (realOthers_ratio g hv) _ (div_nonneg num (mul_nonneg (by linarith) bp.le)) pos
    rw [Points.nearPole,div_div]
    exact div_le_div_of_nonneg_left num (mul_pos sr0 vp) (le1.trans le)
  · apply mul_le_mul (realOthers_ratio g hv) _ (div_nonneg num (mul_nonneg (by linarith) bp.le)) pos
    exact div_le_div_of_nonneg_left num (sub_pos.mpr sr) (le2.trans le)

end BigDescents132.Slit
