import BigDescents132.Balanced

namespace BigDescents132.Slit
open Complex Set
open scoped ComplexConjugate

noncomputable def rootRatio (a c : ℂ) (v : ℝ) := radical c (a*(1+(v:ℂ)))/radical c a

theorem rootRatio_square {a c : ℂ} (hc : c≠0) (hne : a≠c) (v : ℝ) :
    rootRatio a c v^2=1+a/(a-c)*(v:ℂ) := by
  have h : 1-a/c≠0 := sub_ne_zero.mpr (by intro e; exact hne ((div_eq_one_iff_eq hc).mp e.symm))
  rw [rootRatio,div_pow,radical_sq,radical_sq]
  unfold argFactor
  apply (div_eq_iff h).mpr
  field_simp [hc,sub_ne_zero.mpr hne]
  ring

/-- The principal square roots along the outward ray stay in the same
closed quadrant, even when the other root lies on the antipodal ray. -/
theorem rootRatio_re (a c : ℂ) {v : ℝ} (hv : 0≤v) : 0≤(rootRatio a c v).re := by
  let z := argFactor c a
  let Z := argFactor c (a*(1+(v:ℂ)))
  have re (w : ℂ) : 0≤(w^(2⁻¹:ℂ)).re := by rw [Complex.cpow_inv_two_re]; positivity
  have im : Z.im=(1+v)*z.im := by
    have e : Z=1+((1+v:ℝ):ℂ)*(z-1) := by dsimp [Z,z,argFactor]; push_cast; ring
    rw [e]; simp [Complex.mul_im]
  have hi : 0≤(Z^(2⁻¹:ℂ)).im*(z^(2⁻¹:ℂ)).im := by
    rcases le_or_gt 0 z.im with hp|hn
    · rw [Complex.cpow_inv_two_im_eq_sqrt hp,
        Complex.cpow_inv_two_im_eq_sqrt (im ▸ mul_nonneg (by linarith) hp)]
      positivity
    · rw [Complex.cpow_inv_two_im_eq_neg_sqrt hn,
        Complex.cpow_inv_two_im_eq_neg_sqrt (im ▸ mul_neg_of_pos_of_neg (by linarith) hn)]
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (Real.sqrt_nonneg _)) (neg_nonpos.mpr (Real.sqrt_nonneg _))
  change 0≤(Z^(2⁻¹:ℂ)/z^(2⁻¹:ℂ)).re
  rw [Complex.div_re]
  exact add_nonneg (div_nonneg (mul_nonneg (re _) (re _)) (Complex.normSq_nonneg _))
    (div_nonneg hi (Complex.normSq_nonneg _))

variable {s : ℝ} (g : Points s)
noncomputable def Points.slope := ‖g.u‖/g.u.im
noncomputable def Points.poleBound := ‖1-(s:ℂ)*g.u‖/(s*g.u.im)

theorem Points.slope_ge_one : 1≤g.slope := by
  rw [Points.slope,le_div_iff₀ g.upper,one_mul]
  exact (le_abs_self _).trans (Complex.abs_im_le_norm _)

theorem Points.poleBound_pos : 0<g.poleBound :=
  div_pos (norm_pos_iff.mpr g.spole_ne) (mul_pos (zero_lt_one.trans g.parameter) g.upper)

private theorem slope_real (c : ℝ) : ‖g.u/(g.u-c)‖≤g.slope := by
  have h := Complex.abs_im_le_norm (g.u-(c:ℂ))
  simp [abs_of_pos g.upper] at h
  rw [norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _) g.upper h

private theorem slope_conj : ‖g.u/(g.u-conj g.u)‖≤g.slope := by
  have h := Complex.abs_im_le_norm (g.u-conj g.u)
  simp [abs_of_pos g.upper] at h
  rw [norm_div]
  apply div_le_div_of_nonneg_left (norm_nonneg _) g.upper
  linarith [g.upper,le_abs_self (g.u.im+g.u.im)]

private theorem pole_im {v : ℝ} (hv : 0≤v) :
    s*g.u.im≤‖1-(s:ℂ)*(g.u*(1+(v:ℂ)))‖ := by
  have hs := zero_lt_one.trans g.parameter
  have e := Complex.abs_im_le_norm (1-(s:ℂ)*(g.u*(1+(v:ℂ))))
  simp only [Complex.sub_im,Complex.one_im,zero_sub,abs_neg,Complex.im_ofReal_mul,Complex.mul_im,
    Complex.add_im,Complex.ofReal_im,add_zero,mul_zero,zero_add,zero_mul,add_zero,Complex.add_re,Complex.one_re,Complex.ofReal_re] at e
  rw [abs_of_nonneg (mul_nonneg hs.le (mul_nonneg g.upper.le (by linarith)))] at e
  nlinarith only [e,mul_nonneg (mul_nonneg hs.le g.upper.le) hv]

private theorem pole_slope : ‖-((s:ℂ)*g.u)/(1-(s:ℂ)*g.u)‖≤g.slope := by
  have hs := zero_lt_one.trans g.parameter
  have h : s*g.u.im≤‖1-(s:ℂ)*g.u‖ := by simpa using pole_im g (le_rfl : (0:ℝ)≤0)
  rw [norm_div,norm_neg,norm_mul,Complex.norm_real,Real.norm_of_nonneg hs.le]
  calc
    _ ≤ (s*‖g.u‖)/(s*g.u.im) := div_le_div_of_nonneg_left (by positivity) (mul_pos hs g.upper) h
    _ = _ := by unfold Points.slope; field_simp [hs.ne',g.upper.ne']; ring

/-- Concrete complex-cut estimate. On the scale h it suffices to bound
h times |u|/Im(u) and the single pole ratio at v=0. -/
theorem Points.upper_bound {h K v : ℝ} (hh : 0<h) (h1 : h≤1) (hk : 1≤K) (hslope : g.slope≤K/h)
    (hv : 0≤v) :
    ‖g.upperMultiplier v-1‖≤(3*g.poleBound*K^3+g.poleBound*K+1)*(v/h)*(1+v/h)^2 := by
  let u := g.u
  let a := rootRatio u g.r v
  let b := rootRatio u g.R v
  let c := rootRatio u (conj u) v
  let p := (1-(s:ℂ)*u)/(1-(s:ℂ)*(u*(1+(v:ℂ))))
  let η := -((s:ℂ)*u)/(1-(s:ℂ)*u)
  have hs := zero_lt_one.trans g.parameter
  have nu (x : ℝ) : u≠(x:ℂ) := by intro e; have h := congrArg im e; exact g.upper.ne' (by simpa [u] using h)
  have nc : u≠conj u := by intro e; have h := congrArg im e; simp [u] at h; linarith [g.upper]
  have P := pole_im g hv
  have q : 1-(s:ℂ)*(u*(1+(v:ℂ)))≠0 := norm_pos_iff.mp ((mul_pos hs g.upper).trans_le P)
  have inv : p*(1+η*(v:ℂ))=1 := by
    have H : 1-(s:ℂ)*u≠0 := g.spole_ne
    have e : 1+η*(v:ℂ)=(1-(s:ℂ)*(u*(1+(v:ℂ))))/(1-(s:ℂ)*u) := by
      apply (eq_div_iff H).mpr
      dsimp only [η]
      field_simp [H]; ring
    rw [e]; dsimp only [p]; field_simp [H,q]
  have mag : ‖p‖≤g.poleBound := by
    dsimp only [p]; rw [norm_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hs g.upper) P
  have prod : g.upperMultiplier v=(1+v:ℝ)⁻¹ • (p*(a*b*c)) := by
    dsimp [Points.upperMultiplier,multiplier,Points.rayOther,p,a,b,c,u,rootRatio]
    simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_add,Complex.ofReal_one,div_eq_mul_inv,mul_inv]
    ring
  rw [prod]
  exact Cut.cut_multiplier_change hv hh h1 hk g.poleBound_pos.le
    (rootRatio_square (ofReal_ne_zero.mpr g.rpos.ne') (nu _) v)
    (rootRatio_square (ofReal_ne_zero.mpr g.Rpos.ne') (nu _) v)
    (rootRatio_square g.cu_ne nc v)
    (rootRatio_re _ _ hv) (rootRatio_re _ _ hv) (rootRatio_re _ _ hv)
    ((slope_real g _).trans hslope) ((slope_real g _).trans hslope) ((slope_conj g).trans hslope)
    ((pole_slope g).trans hslope) inv mag

end BigDescents132.Slit
