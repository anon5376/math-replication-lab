import BigDescents132.AllRankAlgebra

namespace BigDescents132.AllRanks
open Complex Set Slit
open scoped ComplexConjugate
variable {s : ℝ} (g : Slit.Points s)

private theorem slope_real (c : ℝ) : ‖g.u/(g.u-c)‖≤g.slope := by
  have h := Complex.abs_im_le_norm (g.u-(c:ℂ))
  simp [abs_of_pos g.upper] at h
  rw [norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _) g.upper h

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


theorem sharp_upper {v : ℝ} (hv : 0≤v) :
    ‖g.upperMultiplier v-1‖≤(1+7/2*g.poleBound*g.slope)*v+
      2*g.poleBound*g.slope^2*v^2+g.poleBound/2*g.slope^3*v^3 := by
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
  have bound (e : ℂ) (e0 : e≠0) (de : u≠e) :
      ‖rootRatio u e v-1‖≤‖u/(u-e)‖*v := by
    have t := Cut.sqrt_change (rootRatio_re u e hv) (rootRatio_square e0 de v)
    simpa only [norm_mul,Complex.norm_real,Real.norm_of_nonneg hv] using t
  have sc : ‖u/(u-conj u)‖=g.slope/2 := by
    rw [norm_div,Complex.sub_conj,norm_mul,norm_I,mul_one,Complex.norm_real,Real.norm_of_nonneg (by dsimp [u]; linarith [g.upper])]
    unfold Points.slope
    dsimp [u]; ring
  have pq : p-1= -p*η*(v:ℂ) := by linear_combination inv
  refine sharp_change hv (zero_le_one.trans g.slope_ge_one) g.poleBound_pos.le ?_ ?_ ?_ mag ?_
  · exact (bound _ (ofReal_ne_zero.mpr g.rpos.ne') (nu _)).trans (mul_le_mul_of_nonneg_right (slope_real g _) hv)
  · exact (bound _ (ofReal_ne_zero.mpr g.Rpos.ne') (nu _)).trans (mul_le_mul_of_nonneg_right (slope_real g _) hv)
  · calc
      _ ≤ ‖u/(u-conj u)‖*v := bound _ g.cu_ne nc
      _ = _ := by rw [sc]; ring
  · rw [pq,norm_mul,norm_mul,norm_neg,Complex.norm_real,Real.norm_of_nonneg hv]
    exact mul_le_mul_of_nonneg_right (mul_le_mul mag (pole_slope g) (norm_nonneg _) g.poleBound_pos.le) hv

end BigDescents132.AllRanks

namespace BigDescents132.AllRanks
open MeasureTheory Set Cut
private theorem natural_moment {n j : ℕ} (hn : 8 ≤ n) (hj : j ≤ 3) :
    IntegrableOn (fun v : ℝ => kernel n v * v^j) (Ioi 0) ∧
      ∫ v in Ioi (0:ℝ), kernel n v * v^j = moment n j := by
  have hn' : (8:ℝ) ≤ n := by exact_mod_cast hn
  have hj' : (j:ℝ) ≤ 3 := by exact_mod_cast hj
  simpa only [Real.rpow_natCast] using moment_integral n j (by positivity) (by linarith)


theorem sharp_complex_integral {n : ℕ} (hn : 8≤n) (U : ℝ → ℂ) (hc : ContinuousOn U (Ioi 0))
    {A B C : ℝ} (pointwise : ∀ v ∈ Ioi (0:ℝ), ‖U v-1‖≤A*v+B*v^2+C*v^3) :
    ‖(∫ v in Ioi (0:ℝ), kernel n v • U v)-(moment n 0:ℂ)‖ ≤
      A*moment n 1+B*moment n 2+C*moment n 3 := by
  obtain ⟨hi₁, he₁⟩ := natural_moment (j:=1) hn (by decide)
  obtain ⟨hi₂, he₂⟩ := natural_moment (j:=2) hn (by decide)
  obtain ⟨hi₃, he₃⟩ := natural_moment (j:=3) hn (by decide)
  have i₀ : IntegrableOn (kernel n) (Ioi 0) := by simpa using (natural_moment (j:=0) hn (by decide)).1
  have e₀ : ∫ v in Ioi (0:ℝ), kernel n v = moment n 0 := by
    simpa using (natural_moment (j:=0) hn (by decide)).2
  let D := fun v => (A)*(kernel n v*v^1) + (B)*(kernel n v*v^2) + (C)*(kernel n v*v^3)
  have hD : IntegrableOn D (Ioi 0) :=
    ((hi₁.const_mul _).add (hi₂.const_mul _)).add (hi₃.const_mul _)
  have bound : ∀ᵐ v ∂volume.restrict (Ioi 0), ‖kernel n v • (U v-1)‖ ≤ D v := by
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with v hv
    have hv' : 0<v := hv
    have hk : 0≤kernel n v := by unfold kernel; positivity
    rw [norm_smul, Real.norm_of_nonneg hk]
    calc
      _ ≤ kernel n v * (A*v+B*v^2+C*v^3) := mul_le_mul_of_nonneg_left (pointwise v hv) hk
      _ = D v := by dsimp [D]; ring
  have hdiff : IntegrableOn (fun v => kernel n v • (U v - 1)) (Ioi 0) :=
    hD.mono' (i₀.aestronglyMeasurable.smul ((hc.aestronglyMeasurable measurableSet_Ioi).sub
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
    _ = A * moment n 1 + B * moment n 2 + C * moment n 3 := by
      dsimp [D]
      erw [integral_add ((hi₁.const_mul (A)).add (hi₂.const_mul (B))) (hi₃.const_mul (C)),
        integral_add (hi₁.const_mul (A)) (hi₂.const_mul (B))]
      simp only [integral_const_mul, he₁, he₂, he₃, Nat.cast_one, Nat.cast_ofNat]


theorem actual_complex_integral {s : ℝ} (g : Slit.Points s) {n : ℕ} (hn : 8≤n) :
    ‖(∫ v in Ioi (0:ℝ), kernel n v • g.upperMultiplier v)-(moment n 0:ℂ)‖ ≤
    (1+7/2*g.poleBound*g.slope)*moment n 1+(2*g.poleBound*g.slope^2)*moment n 2+
      (g.poleBound/2*g.slope^3)*moment n 3 :=
  sharp_complex_integral hn _ g.upper_continuous (fun _ hv => sharp_upper g (le_of_lt hv))

end BigDescents132.AllRanks

namespace BigDescents132.AllRanks
open MeasureTheory Set Cut Slit

/-- Integrate a positive Laurent-polynomial majorant on the finite real cut. -/
theorem sharp_real_integral {n : ℕ} (hn : 8≤n) {T A B C : ℝ}
    (hA : 0≤A) (hB : 0≤B) (hC : 0≤C) (V : ℝ → ℂ)
    (bd : ∀ v∈Ioo (0:ℝ) T, ‖V v‖≤A/v+B+C*v) :
    ‖∫ v in Ioo (0:ℝ) T,kernel n v • V v‖ ≤ A*moment n (-1)+B*moment n 0+C*moment n 1 := by
  have nn : (8:ℝ)≤n := by exact_mod_cast hn
  have hm := moment_integral n (-1) (by norm_num) (by linarith)
  have hz := moment_integral n 0 (by norm_num) (by linarith)
  have hp := moment_integral n 1 (by norm_num) (by linarith)
  simp only [Real.rpow_neg_one,Real.rpow_zero,Real.rpow_one,mul_one] at hm hz hp
  let H := fun v => A*(kernel n v*v⁻¹)+B*kernel n v+C*(kernel n v*v)
  have hi : IntegrableOn H (Ioi 0) :=
    ((hm.1.const_mul A).add (hz.1.const_mul B)).add (hp.1.const_mul C)
  have hk (v : ℝ) (hv : 0<v) : 0≤kernel n v := by unfold kernel; positivity
  have point : ∀ᵐ v ∂volume.restrict (Ioo 0 T), ‖kernel n v • V v‖≤H v := by
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioo] with v hv
    rw [norm_smul,Real.norm_of_nonneg (hk _ hv.1)]
    exact (mul_le_mul_of_nonneg_left (bd _ hv) (hk _ hv.1)).trans_eq (by dsimp [H]; ring)
  have posH : ∀ᵐ v ∂volume.restrict (Ioi 0), 0≤H v := by
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with v hv
    have vp : 0<v := hv
    have kn := hk _ vp
    dsimp [H]; positivity
  calc
    _ ≤ ∫ v in Ioo (0:ℝ) T,H v := norm_integral_le_of_norm_le (hi.mono_set Ioo_subset_Ioi_self) point
    _ ≤ ∫ v in Ioi (0:ℝ),H v := setIntegral_mono_set hi posH (Filter.Eventually.of_forall fun _ hv => hv.1)
    _ = _ := by
      dsimp [H]
      erw [integral_add ((hm.1.const_mul A).add (hz.1.const_mul B)) (hp.1.const_mul C),
        integral_add (hm.1.const_mul A) (hz.1.const_mul B)]
      simp only [integral_const_mul,hm.2,hz.2,hp.2]

theorem actual_real_integrals {s : ℝ} (g : Slit.Points s) {n : ℕ} (hn : 8≤n) :
    let m := Cut.moment n
    let R := ‖∫ v in Ioo (0:ℝ) g.endReal, Cut.kernel n v • g.scaledRealMultiplier v‖
    R≤g.nearPole*((2*n:ℝ)+g.slope)*m 0 ∧
    R≤g.farPole*(m 0+(1+g.slope)*m 1) := by
  have sp := zero_lt_one.trans g.parameter
  have np : 0≤g.nearPole := div_nonneg (norm_nonneg _) (mul_pos sp g.rpos).le
  have fp : 0≤g.farPole := div_nonneg (norm_nonneg _) (sub_pos.mpr g.sr_gt).le
  have sl := zero_le_one.trans g.slope_ge_one
  constructor
  · apply (sharp_real_integral hn np (mul_nonneg np (by linarith : 0≤1+g.slope)) le_rfl _
      (fun v hv => (g.real_bounds hv).1.trans_eq (by field_simp [hv.1.ne']; ring))).trans_eq
    rw [inverse_moment (by omega)]
    ring
  · apply (sharp_real_integral hn (le_refl (0:ℝ)) fp (mul_nonneg fp (by linarith : 0≤1+g.slope)) _
      (fun v hv => (g.real_bounds hv).2.trans_eq (by ring))).trans_eq
    ring

end BigDescents132.AllRanks

namespace BigDescents132.AllRanks
open Complex MeasureTheory Set Slit Cut

/-- Fully explicit moment bound for the physical permutation polynomial. -/
theorem contour_error {s : ℝ} (g : Slit.Points s) (n : ℕ) (hn : 8≤n+1) :
    let N := n+1
    let S := g.slope
    let P := g.poleBound
    let M := moment N
    |(B N).eval (1-s)/(2*‖g.complexWeight N‖*M 0)-Real.cos (g.complexWeight N).arg| ≤
      ((1+7/2*P*S)*M 1+2*P*S^2*M 2+P/2*S^3*M 3)/M 0+
      (g.amplitudeRatio*(‖g.u‖/g.r)^(N+1))*
        min (g.nearPole*((2*N:ℝ)+S)) (g.farPole*(1+(1+S)*(M 1/M 0))) := by
  let N := n+1
  let M := moment N
  let q := g.unitPhase N
  let Z := ∫ v in Ioi (0:ℝ), kernel N v • g.upperMultiplier v
  let R := ∫ v in Ioo (0:ℝ) g.endReal, kernel N v • g.scaledRealMultiplier v
  have nn : (8:ℝ)≤N := by exact_mod_cast hn
  have W : 0<M 0 := moment_pos N 0 (by norm_num) (by linarith)
  have wn := Complex.ofReal_ne_zero.mpr W.ne'
  have ne := g.complexWeight_ne N
  have qn : ‖q‖=1 := by simp [q,Points.unitPhase,norm_div,(norm_ne_zero_iff.mpr ne)]
  have qc : q.re=Real.cos (g.complexWeight N).arg := by dsimp only [q]; rw [Points.unitPhase,Complex.div_ofReal_re,Complex.cos_arg ne]
  have C := actual_complex_integral g hn
  have er : |(q*(Z/(M 0:ℂ))).re-Real.cos (g.complexWeight N).arg|≤
      ((1+7/2*g.poleBound*g.slope)*M 1+2*g.poleBound*g.slope^2*M 2+g.poleBound/2*g.slope^3*M 3)/M 0 := by
    rw [←qc,←Complex.sub_re,show q*(Z/(M 0:ℂ))-q=q*((Z-(M 0:ℂ))/(M 0:ℂ)) by field_simp; ring]
    apply (Complex.abs_re_le_norm _).trans
    rw [norm_mul,qn,one_mul,norm_div,Complex.norm_real,Real.norm_of_nonneg W.le]
    exact div_le_div_of_nonneg_right C W.le
  obtain ⟨RN,RF⟩ := actual_real_integrals g hn
  have rr : ‖R‖/M 0≤min (g.nearPole*((2*N:ℝ)+g.slope)) (g.farPole*(1+(1+g.slope)*(M 1/M 0))) := by
    apply le_min ((div_le_iff₀ W).mpr RN)
    refine (div_le_iff₀ W).mpr (RF.trans_eq ?_)
    change g.farPole*(M 0+(1+g.slope)*M 1)=_
    field_simp [W.ne']
  have term := mul_le_mul_of_nonneg_left ((div_le_div_of_nonneg_right (Complex.abs_re_le_norm R) W.le).trans rr)
    (abs_nonneg (g.scaledReal N))
  change |(B (n+1)).eval (1-s)/_ - _|≤_
  rw [g.scaled_coefficient n]
  change |(q*(Z/(M 0:ℂ))).re+g.scaledReal N*R.re/M 0-Real.cos (g.complexWeight N).arg|≤_
  rw [add_sub_right_comm]
  apply (abs_add_le _ _).trans (add_le_add er ?_)
  rw [abs_div,abs_mul,abs_of_pos W,mul_div_assoc]
  simpa [N,M,Points.scaled_real_size,Points.amplitudeRatio] using term

end BigDescents132.AllRanks
