import BigDescents132.CutMoments

namespace BigDescents132.Cut
open Complex Set MeasureTheory

/-- A square root with nonnegative real part is Lipschitz relative to its
value 1, with constant 1 in this centered estimate. -/
theorem sqrt_change {a z : ℂ} (ha : 0≤a.re) (hz : a^2=1+z) : ‖a-1‖≤‖z‖ := by
  have hone : 1≤‖a+1‖ := (show (1:ℝ)≤(a+1).re by simpa using ha).trans (Complex.re_le_norm _)
  have h : (a-1)*(a+1)=z := by linear_combination hz
  calc
    _ ≤ ‖a-1‖*‖a+1‖ := le_mul_of_one_le_right (norm_nonneg _) hone
    _ = _ := by rw [←norm_mul,h]

private theorem diff_prod (a b : ℂ) : ‖a*b-1‖≤‖a‖*‖b-1‖+‖a-1‖ := by
  rw [show a*b-1=a*(b-1)+(a-1) by ring]
  exact (norm_add_le _ _).trans_eq (by rw [norm_mul])

private theorem norm_from_diff {a : ℂ} {v : ℝ} (h : ‖a-1‖≤v) : ‖a‖≤1+v := by
  have e := norm_add_le (a-1) 1
  rw [sub_add_cancel,norm_one] at e
  linarith

set_option maxHeartbeats 600000 in
/-- Three normalized radical factors and the two rational factors occurring
in the complex-cut integral. K bounds the four slopes on the h scale. D
bounds the inverse pole factor along the ray. -/
theorem cut_multiplier_change {a b c p α β γ η : ℂ} {v h K D : ℝ}
    (hv : 0≤v) (hh : 0<h) (hh' : h≤1) (hK : 1≤K) (hD : 0≤D)
    (a₂ : a^2=1+α*(v:ℂ)) (b₂ : b^2=1+β*(v:ℂ)) (c₂ : c^2=1+γ*(v:ℂ))
    (ar : 0≤a.re) (br : 0≤b.re) (cr : 0≤c.re)
    (hα : ‖α‖≤K/h) (hβ : ‖β‖≤K/h) (hγ : ‖γ‖≤K/h) (hη : ‖η‖≤K/h)
    (hp : p*(1+η*(v:ℂ))=1) (hp' : ‖p‖≤D) :
    ‖(1+v:ℝ)⁻¹ • (p*(a*b*c))-1‖ ≤ (3*D*K^3+D*K+1)*(v/h)*(1+v/h)^2 := by
  let t := v/h
  have ht : 0≤t := div_nonneg hv hh.le
  have kt : 0≤K*t := by positivity
  have root {u u' : ℂ} (hu : u^2=1+u'*(v:ℂ)) (hre : 0≤u.re) (hs : ‖u'‖≤K/h) :
      ‖u-1‖≤K*t := by
    calc
      _ ≤ ‖u'*(v:ℂ)‖ := sqrt_change hre hu
      _ = ‖u'‖*v := by simp [Real.norm_of_nonneg hv]
      _ ≤ (K/h)*v := mul_le_mul_of_nonneg_right hs hv
      _ = _ := by dsimp [t]; ring
  have ha := root a₂ ar hα
  have hb := root b₂ br hβ
  have hc := root c₂ cr hγ
  have hab : ‖a*b-1‖≤(1+K*t)*(K*t)+K*t := by
    apply (diff_prod a b).trans
    gcongr
    exact norm_from_diff ha
  have habc : ‖a*b*c-1‖≤3*K^3*t*(1+t)^2 := by
    apply (diff_prod (a*b) c).trans
    rw [norm_mul]
    calc
      _ ≤ ((1+K*t)*(1+K*t))*(K*t) + ((1+K*t)*(K*t)+K*t) := by
        gcongr <;> first | exact norm_from_diff ha | exact norm_from_diff hb
      _ ≤ (K*(1+t))^2*(K*t) + ((K*(1+t))*(K*t)+K*t) := by
        have h : 1+K*t≤K*(1+t) := by linarith
        rw [pow_two]
        gcongr
      _ ≤ _ := by
        have h₁ : 1≤K*(1+t) := by nlinarith only [kt,hK]
        have h₂ : K*(1+t) ≤ (K*(1+t))^2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr h₁) (by linarith : 0≤K*(1+t))]
        nlinarith only [mul_nonneg (sub_nonneg.mpr h₂) kt, mul_nonneg (sub_nonneg.mpr h₁) kt]
  have hpd : ‖p-1‖≤D*K*t := by
    have ep : p-1= -(p*η*(v:ℂ)) := by linear_combination hp
    rw [ep,norm_neg,norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hv]
    calc
      _ ≤ D*(K/h)*v := by gcongr
      _ = _ := by dsimp [t]; ring
  have hfull : ‖p*(a*b*c)-1‖≤D*(3*K^3*t*(1+t)^2)+D*K*t :=
    (diff_prod p (a*b*c)).trans (add_le_add (mul_le_mul hp' habc (norm_nonneg _) hD) hpd)
  let d : ℝ := (1+v)⁻¹
  have dnonneg : 0≤d := by dsimp [d]; positivity
  have d₁ : d≤1 := (inv_le_one₀ (by linarith)).mpr (by linarith)
  have hdv : 1-d≤v := by
    dsimp [d]
    rw [← one_div]
    apply (sub_le_comm).mpr
    apply (le_div_iff₀ (by linarith : 0<1+v)).mpr
    nlinarith only [sq_nonneg v]
  have vt : v≤t := by dsimp [t]; exact (le_div_iff₀ hh).mpr (by nlinarith only [mul_nonneg hv (sub_nonneg.mpr hh')])
  have de : d • (p*(a*b*c))-1 = d • (p*(a*b*c)-1)+((d-1:ℝ):ℂ) := by
    simp [Complex.real_smul]; ring
  change ‖d • (p*(a*b*c))-1‖≤(3*D*K^3+D*K+1)*t*(1+t)^2
  rw [de]
  apply (norm_add_le _ _).trans
  rw [norm_smul,Real.norm_of_nonneg dnonneg,Complex.norm_real,Real.norm_of_nonpos (sub_nonpos.mpr d₁)]
  have sq : 1≤(1+t)^2 := by nlinarith only [ht,sq_nonneg t]
  have hdt := (mul_le_of_le_one_left (norm_nonneg (p*(a*b*c)-1)) d₁).trans hfull
  have hlast : 0≤D*K*t := by positivity
  nlinarith only [hdt,hdv,vt,mul_nonneg (sub_nonneg.mpr sq) hlast,mul_nonneg (sub_nonneg.mpr sq) ht]

end BigDescents132.Cut
