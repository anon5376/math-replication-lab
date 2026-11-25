import BigDescents132.PeakWeight

namespace BigDescents132.Peak
open Real Set MeasureTheory Filter
open scoped Topology

noncomputable def errWeight (q u : ℝ) := remainderDensity u*Real.exp (-(q/2)*u)

theorem real_lap_integrable {q r : ℝ} (qp : 0<q) (rr : -1<r) :
    IntegrableOn (fun u : ℝ => u^r*Real.exp (-q*u)) (Ioi 0) := by
  simpa using integrableOn_rpow_mul_exp_neg_mul_rpow rr (le_refl (1:ℝ)) qp

private theorem singular_integrable {a : ℝ} (ha' : a<1) :
    IntegrableOn (fun u : ℝ => (1-u)^(-1/2:ℝ)) (Ioo a 1) := by
  apply reflected_integrable (fun u : ℝ => u^(-1/2:ℝ)) ha'.le
  rw [sub_self]
  exact (intervalIntegral.integrableOn_Ioo_rpow_iff (sub_pos.mpr ha')).mpr (by norm_num)

theorem err_integrable {q : ℝ} (qp : 0<q) : IntegrableOn (errWeight q) (Ioo 0 1) := by
  apply ((singular_integrable zero_lt_one).const_mul (1/Real.sqrt 3)).mono'
    (by apply Measurable.aestronglyMeasurable; unfold errWeight remainderDensity correction; fun_prop)
  refine ae_restrict_of_forall_mem measurableSet_Ioo fun u hu => ?_
  have le1 : Real.exp (-(q/2)*u)≤1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_pos qp hu.1])
  rw [errWeight,Real.norm_of_nonneg (mul_nonneg (remainder_nonneg hu) (Real.exp_pos _).le)]
  exact (mul_le_of_le_one_right (remainder_nonneg hu) le1).trans (remainder_large hu)

private theorem small_integral {q : ℝ} (qp : 0<q) :
    (∫ u in Ioo (0:ℝ) (1/2),errWeight q u)≤
      (1/3)*(2/q)^(7/2:ℝ)*Real.Gamma (7/2) := by
  let h := fun u : ℝ => u^(5/2:ℝ)*Real.exp (-(q/2)*u)
  have I := real_lap_integrable (half_pos qp) (by norm_num : (-1:ℝ)<5/2)
  have sub : Ioo (0:ℝ) (1/2)⊆Ioi 0 := fun _ hx => hx.1
  have comp : (∫ u in Ioo (0:ℝ) (1/2),errWeight q u)≤∫ u in Ioo (0:ℝ) (1/2),(1/3)*h u := by
    refine setIntegral_mono_on ((err_integrable qp).mono_set (Ioo_subset_Ioo le_rfl (by norm_num))) ((I.mono_set sub).const_mul _) measurableSet_Ioo ?_
    intro u hu
    change remainderDensity u*_≤1/3*(u^(5/2:ℝ)*_)
    have hh := mul_le_mul_of_nonneg_right (remainder_small hu) (Real.exp_pos (-(q/2)*u)).le
    linarith only [hh]
  have pos : 0≤ᵐ[volume.restrict (Ioi (0:ℝ))] h := ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_pos _).le)
  have z := setIntegral_mono_set I pos (ae_of_all _ sub)
  have val := Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0:ℝ)<7/2) (half_pos qp)
  rw [show (7/2:ℝ)-1=5/2 by norm_num,show 1/(q/2)=2/q by ring] at val
  rw [integral_const_mul] at comp
  apply comp.trans
  calc
    (1/3:ℝ)*(∫ x in Ioo (0:ℝ) (1/2),h x) ≤ (1/3:ℝ)*(∫ x in Ioi (0:ℝ),h x) := mul_le_mul_of_nonneg_left z (by norm_num)
    _ = _ := by dsimp [h]; simp only [neg_mul]; rw [val]; ring

private theorem large_integral {q : ℝ} (qp : 0<q) :
    (∫ u in Ioo (1/2:ℝ) 1,errWeight q u)≤
      (2*Real.sqrt (1/2)/Real.sqrt 3)*Real.exp (-q/4) := by
  let factor := Real.exp (-q/4)/Real.sqrt 3
  have I := singular_integrable (by norm_num : (1/2:ℝ)<1)
  have bnd : (∫ u in Ioo (1/2:ℝ) 1,errWeight q u)≤∫ u in Ioo (1/2:ℝ) 1,factor*(1-u)^(-1/2:ℝ) := by
    apply setIntegral_mono_on ((err_integrable qp).mono_set (Ioo_subset_Ioo (by norm_num) le_rfl)) (I.const_mul factor) measurableSet_Ioo
    intro u hu
    have u0 := (by norm_num : (0:ℝ)<1/2).trans hu.1
    have y := sub_pos.mpr hu.2
    have a := remainder_large ⟨u0,hu.2⟩
    have e : Real.exp (-(q/2)*u)≤Real.exp (-q/4) := Real.exp_le_exp.mpr (by nlinarith [mul_nonneg qp.le (sub_nonneg.mpr hu.1.le)])
    calc
      _ ≤ (1/Real.sqrt 3*(1-u)^(-1/2:ℝ))*Real.exp (-q/4) := mul_le_mul a e (Real.exp_pos _).le (by positivity)
      _ = _ := by dsimp [factor]; ring
  rw [integral_const_mul,singular_mass] at bnd
  exact bnd.trans_eq (by dsimp [factor]; ring)

noncomputable def innerErr (q : ℝ) :=
  (1/3)*(2/q)^(7/2:ℝ)*Real.Gamma (7/2)+(2*Real.sqrt (1/2)/Real.sqrt 3)*Real.exp (-q/4)

theorem err_integral {q : ℝ} (qp : 0<q) : (∫ u in Ioo (0:ℝ) 1,errWeight q u)≤ innerErr q := by
  rw [split_unit (err_integrable qp)]
  exact add_le_add (small_integral qp) (large_integral qp)

theorem positive_tail {p : ℝ} (pp : 0<p) :
    (∫ x in Ioi (1:ℝ),x*Real.exp (-p*x))=(1/p+1/p^2)*Real.exp (-p) := by
  let j := fun x : ℝ => -(x/p+1/p^2)*Real.exp (-p*x)
  have J (x : ℝ) : HasDerivAt j (x*Real.exp (-p*x)) x := by
    have e := (((hasDerivAt_id x).const_mul (-p)).exp)
    have a := (((hasDerivAt_id x).div_const p).add_const (1/p^2)).neg
    convert a.mul e using 1
    dsimp; field_simp [pp.ne']; ring
  have G := (real_lap_integrable pp (by norm_num : (-1:ℝ)<1)).mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))
  simp only [Real.rpow_one] at G
  have L₁ := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) p pp
  have L₂ := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0:ℝ) p pp
  simp only [Real.rpow_one,Real.rpow_zero,one_mul] at L₁ L₂
  have L : Tendsto j atTop (𝓝 0) := by
    have v := ((L₁.div_const p).add (L₂.div_const (p^2))).neg
    simp at v
    exact v.congr' (Eventually.of_forall fun x => by dsimp [j]; rw [←neg_mul]; ring)
  have eq := integral_Ioi_of_hasDerivAt_of_tendsto (J 1).continuousAt.continuousWithinAt (fun x _ => J x) G L
  rw [eq]; dsimp [j]; simp only [mul_one,zero_sub]; ring

noncomputable def tailErr (q : ℝ) := (2/q+4/q^2)*Real.exp (-q/2)

theorem sqrt_tail {q : ℝ} (qp : 0<q) :
    (∫ u in Ioi (1:ℝ),Real.sqrt u*Real.exp (-(q/2)*u))≤tailErr q := by
  have p := half_pos qp
  have t := Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1)
  have h := (real_lap_integrable p (by norm_num : (-1:ℝ)<1/2)).mono_set t
  have j := (real_lap_integrable p (by norm_num : (-1:ℝ)<1)).mono_set t
  simp only [Real.rpow_one] at j
  simp only [←Real.sqrt_eq_rpow] at h
  have H (x : ℝ) (hx : x∈Ioi (1:ℝ)) : Real.sqrt x≤x := by
    have hn : 0≤x := zero_le_one.trans hx.le
    exact Real.sqrt_le_iff.mpr ⟨hn,by nlinarith [mul_nonneg (sub_nonneg.mpr hx.le) hn]⟩
  apply (setIntegral_mono_on h j measurableSet_Ioi (fun x hx => mul_le_mul_of_nonneg_right (H x hx) (Real.exp_pos _).le)).trans
  rw [positive_tail p,tailErr]
  apply le_of_eq
  congr 1 <;> ring

theorem decaying_integral {q : ℝ} (qp : 0<q) :
    (∫ v in Ioo (0:ℝ) 1,density v*Real.exp (-q*v))≤Real.sqrt Real.pi/Real.sqrt q := by
  have I := real_lap_integrable qp (by norm_num : (-1:ℝ)< -1/2)
  have s : Ioo (0:ℝ) 1⊆Ioi 0 := fun _ h => h.1
  have comp : ∀ v∈Ioo (0:ℝ) 1,density v*Real.exp (-q*v)≤v^(-1/2:ℝ)*Real.exp (-q*v) :=
    fun v hv => mul_le_mul_of_nonneg_right (density_le hv) (Real.exp_pos _).le
  have Int : IntegrableOn (fun v : ℝ => density v*Real.exp (-q*v)) (Ioo 0 1) := by
    apply (I.mono_set s).mono' (by apply Measurable.aestronglyMeasurable; unfold density; fun_prop)
    exact ae_restrict_of_forall_mem measurableSet_Ioo fun v hv => by rw [Real.norm_of_nonneg (mul_nonneg (density_nonneg hv.1.le) (Real.exp_pos _).le)]; exact comp v hv
  have mx := setIntegral_mono_set I (ae_restrict_of_forall_mem measurableSet_Ioi (fun v hv => mul_nonneg (Real.rpow_nonneg hv.le _) (Real.exp_pos _).le)) (ae_of_all _ s)
  have V := Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0:ℝ)<1/2) qp
  rw [show (1/2:ℝ)-1= -1/2 by norm_num,←Real.sqrt_eq_rpow,Real.sqrt_div (by norm_num),Real.sqrt_one,Real.Gamma_one_half_eq] at V
  have bound := (setIntegral_mono_on Int (I.mono_set s) measurableSet_Ioo comp).trans mx
  calc
    _ ≤ _ := bound
    _ = _ := by simp only [neg_mul]; rw [V]; ring

end BigDescents132.Peak
