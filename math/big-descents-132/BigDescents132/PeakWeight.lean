import BigDescents132.PeakLaplace

namespace BigDescents132.Peak
open Real Set MeasureTheory Filter
open scoped Topology

noncomputable def correction (u : ℝ) := Real.sqrt (1+u^2/(3*(1-u)))
noncomputable def remainderDensity (u : ℝ) := Real.sqrt u*(correction u-1)

theorem corr_nonneg {u : ℝ} (hu : u<1) : 1≤correction u := by
  unfold correction
  rw [Real.one_le_sqrt]
  exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (by linarith))

theorem reflected_density {u : ℝ} (hu : u∈Ioo 0 1) :
    density (1-u)=Real.sqrt 3*(Real.sqrt u*correction u) := by
  have p := hu.1
  have y := sub_pos.mpr hu.2
  have rem : 0≤1-(1-u)^3 := sub_nonneg.mpr (pow_le_one₀ y.le (by linarith))
  have hp : 0≤1+u^2/(3*(1-u)) := by positivity
  rw [density,show (-1/2:ℝ)= -(1/2) by norm_num,Real.rpow_neg y.le,←Real.sqrt_eq_rpow]
  have h₁ := Real.sq_sqrt rem
  have h₂ := Real.sq_sqrt y.le
  have h₃ := Real.sq_sqrt p.le
  have h₄ := Real.sq_sqrt hp
  have h₅ := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  unfold correction
  rw [inv_mul_eq_div,div_eq_iff (Real.sqrt_pos_of_pos y).ne']
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  simp only [mul_pow,h₁,h₂,h₃,h₄,h₅]
  field_simp [(sub_pos.mpr hu.2).ne']; ring

theorem remainder_nonneg {u : ℝ} (hu : u∈Ioo 0 1) : 0≤remainderDensity u :=
  mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr (corr_nonneg hu.2))

theorem remainder_small {u : ℝ} (hu : u∈Ioo 0 (1/2)) :
    remainderDensity u ≤ u^(5/2:ℝ)/3 := by
  have p := hu.1
  have u1 := hu.2.trans (by norm_num : (1/2:ℝ)<1)
  have d : 0<3*(1-u) := by linarith
  have corr := corr_nonneg u1
  have z := Real.sq_sqrt (show 0≤1+u^2/(3*(1-u)) by positivity)
  change (correction u)^2=_ at z
  have k : u^2/(3*(1-u))≤2*u^2/3 := by
    apply (div_le_iff₀ d).mpr
    nlinarith [mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu.2.le)]
  have b : correction u-1≤u^2/3 := by nlinarith [sq_nonneg (correction u-1)]
  have e : u^(5/2:ℝ)=Real.sqrt u*u^2 := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_natCast u 2,←Real.rpow_add p]; norm_num
  rw [remainderDensity,e,mul_div_assoc]
  exact mul_le_mul_of_nonneg_left b (Real.sqrt_nonneg _)

theorem remainder_large {u : ℝ} (hu : u∈Ioo 0 1) :
    remainderDensity u ≤ (1/Real.sqrt 3)*(1-u)^(-1/2:ℝ) := by
  have p := hu.1
  have y := sub_pos.mpr hu.2
  have E : 0≤u^2/(3*(1-u)) := by positivity
  have d : Real.sqrt (1+u^2/(3*(1-u)))-1≤Real.sqrt (u^2/(3*(1-u))) := by
    have V : 0≤1+Real.sqrt (u^2/(3*(1-u))) := by positivity
    have H : Real.sqrt (1+u^2/(3*(1-u)))≤1+Real.sqrt (u^2/(3*(1-u))) := (Real.sqrt_le_iff).mpr ⟨V,by nlinarith [Real.sq_sqrt E,Real.sqrt_nonneg (u^2/(3*(1-u)))]⟩
    linarith only [H]
  have h : correction u-1≤u/(Real.sqrt 3*Real.sqrt (1-u)) := by
    simpa [correction,Real.sqrt_div (sq_nonneg u),Real.sqrt_mul (by norm_num : (0:ℝ)≤3),Real.sqrt_sq p.le] using d
  have v : Real.sqrt u*u≤1 := mul_le_one₀ ((Real.sqrt_le_one).mpr hu.2.le) p.le hu.2.le
  rw [show (-1/2:ℝ)= -(1/2) by norm_num,Real.rpow_neg y.le,←Real.sqrt_eq_rpow]
  calc
    _ ≤ Real.sqrt u*(u/(Real.sqrt 3*Real.sqrt (1-u))) := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
    _ = Real.sqrt u*u/(Real.sqrt 3*Real.sqrt (1-u)) := by ring
    _ ≤ 1/(Real.sqrt 3*Real.sqrt (1-u)) := div_le_div_of_nonneg_right v (by positivity)
    _ = _ := by ring

theorem reflect_Ioo {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) {a b : ℝ}
    (ab : a≤b) : (∫ x in Ioo a b, f (1-x))=∫ x in Ioo (1-b) (1-a), f x := by
  rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le ab,
    intervalIntegral.integral_comp_sub_left,intervalIntegral.integral_of_le (sub_le_sub_left ab 1),integral_Ioc_eq_integral_Ioo]

theorem reflected_integrable {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) {a b : ℝ} (ab : a≤b)
    (h : IntegrableOn f (Ioo (1-b) (1-a))) : IntegrableOn (fun x => f (1-x)) (Ioo a b) := by
  have j := (intervalIntegrable_iff_integrableOn_Ioo_of_le (sub_le_sub_left ab 1)).mpr h
  have v := j.comp_sub_left 1
  simpa [intervalIntegrable_iff_integrableOn_Ioo_of_le ab,sub_sub_cancel] using v.symm

theorem singular_mass :
    (∫ x in Ioo (1/2:ℝ) 1, (1-x)^(-1/2:ℝ))=2*Real.sqrt (1/2) := by
  rw [reflect_Ioo (fun x : ℝ => x^(-1/2:ℝ)) (by norm_num)]
  norm_num only [sub_self,show (1:ℝ)-1/2=1/2 by norm_num]
  rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le (by norm_num),
    integral_rpow (Or.inl (by norm_num))]
  norm_num [show -1/2+(1:ℝ)=1/2 by norm_num,Real.sqrt_eq_rpow]
  ring

theorem split_oi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (hf : IntegrableOn f (Ioi 0)) :
    (∫ x in Ioi (0:ℝ), f x)=(∫ x in Ioo (0:ℝ) 1, f x)+(∫ x in Ioi (1:ℝ), f x) := by
  have u : Ioc (0:ℝ) 1 ∪ Ioi 1=Ioi 0 := by ext x; simp
  rw [←integral_Ioc_eq_integral_Ioo,←setIntegral_union (s:=Ioc (0:ℝ) 1) (t:=Ioi (1:ℝ)) (Set.disjoint_left.mpr (fun _ h₁ h₂ => (not_lt.mpr h₁.2) h₂))
    measurableSet_Ioi (hf.mono_set (fun _ h => h.1)) (hf.mono_set (fun _ h => (by norm_num : (0:ℝ)<1).trans h)),u]

theorem split_unit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (hf : IntegrableOn f (Ioo 0 1)) :
    (∫ x in Ioo (0:ℝ) 1, f x)=(∫ x in Ioo (0:ℝ) (1/2), f x)+(∫ x in Ioo (1/2:ℝ) 1, f x) := by
  have ab : (0:ℝ)≤1/2 := by norm_num
  have bc : (1/2:ℝ)≤1 := by norm_num
  have c := (intervalIntegrable_iff_integrableOn_Ioo_of_le (ab.trans bc)).mpr hf
  have a := (intervalIntegrable_iff_integrableOn_Ioo_of_le ab).mpr (hf.mono_set (Ioo_subset_Ioo le_rfl bc))
  have b := (intervalIntegrable_iff_integrableOn_Ioo_of_le bc).mpr (hf.mono_set (Ioo_subset_Ioo ab le_rfl))
  rw [←integral_Ioc_eq_integral_Ioo,←integral_Ioc_eq_integral_Ioo (x:=(0:ℝ)) (y:=(1/2:ℝ)),
    ←integral_Ioc_eq_integral_Ioo (x:=(1/2:ℝ)) (y:=(1:ℝ)),←intervalIntegral.integral_of_le (ab.trans bc),
    ←intervalIntegral.integral_of_le ab,←intervalIntegral.integral_of_le bc,intervalIntegral.integral_add_adjacent_intervals a b]

end BigDescents132.Peak
