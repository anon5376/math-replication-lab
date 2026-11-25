import BigDescents132.PeakEstimate

namespace BigDescents132.Peak
open Real Complex Set MeasureTheory Filter
open scoped Topology ComplexConjugate

noncomputable def peakRay (q : ℝ) := (q:ℂ)*ray
noncomputable def oscillatory (q : ℝ) := ∫ v in Ioo (0:ℝ) 1, (density v:ℂ)*Complex.exp (peakRay q*(v:ℂ))
noncomputable def mainIntegral (q : ℝ) :=
  ((Real.sqrt 3:ℝ):ℂ)*Complex.exp (peakRay q)*(∫ u in Ioi (0:ℝ),lap (peakRay q) (1/2) u)

theorem peakRay_re (q : ℝ) : (peakRay q).re=q/2 := by rw [peakRay,Complex.re_ofReal_mul,ray_re]; ring
theorem peakRay_im (q : ℝ) : (peakRay q).im=Real.sqrt 3*q/2 := by rw [peakRay,Complex.im_ofReal_mul,ray_im]; ring

private theorem cErr {q : ℝ} (qp : 0<q) :
    ‖oscillatory q-mainIntegral q‖≤Real.sqrt 3*Real.exp (q/2)*(innerErr q+tailErr q) := by
  let b := peakRay q
  have br : b.re=q/2 := peakRay_re q
  have bp : 0<b.re := br ▸ half_pos qp
  let R := fun u : ℝ => (remainderDensity u:ℂ)*Complex.exp (-b*(u:ℂ))
  have eR (u : ℝ) (hu : u∈Ioo 0 1) : ‖R u‖=errWeight q u := by
    simp [R,errWeight,norm_mul,Complex.norm_exp,Complex.mul_re,Real.norm_of_nonneg (remainder_nonneg hu),br]
  have RI : IntegrableOn R (Ioo 0 1) := by
    apply (err_integrable qp).mono' (by apply Measurable.aestronglyMeasurable; dsimp [R,remainderDensity,correction]; fun_prop)
    exact ae_restrict_of_forall_mem measurableSet_Ioo fun u hu => (eR u hu).le
  have GI := lap_integrable bp (by norm_num : (-1:ℝ)<1/2)
  have q0 : Ioo (0:ℝ) 1⊆Ioi 0 := fun _ h => h.1
  let G := lap b (1/2)
  let H := ((Real.sqrt 3:ℝ):ℂ)*Complex.exp b
  have e (u : ℝ) (hu : u∈Ioo 0 1) :
      (density (1-u):ℂ)*Complex.exp (b*((1-u:ℝ):ℂ))=H*(G u+R u) := by
    rw [reflected_density hu,Complex.ofReal_sub,Complex.ofReal_one,
      show b*(1-(u:ℂ))=b+(-b*(u:ℂ)) by ring,Complex.exp_add]
    dsimp [H,G,lap,R,remainderDensity]
    rw [←Real.sqrt_eq_rpow]
    push_cast; ring
  have eq : oscillatory q =H*((∫ u in Ioo (0:ℝ) 1,G u)+(∫ u in Ioo (0:ℝ) 1,R u)) := by
    have ch := reflect_Ioo (fun v : ℝ => (density v:ℂ)*Complex.exp (b*(v:ℂ))) (by norm_num : (0:ℝ)≤1)
    simp only [sub_self,sub_zero] at ch
    rw [oscillatory,←ch,setIntegral_congr_fun measurableSet_Ioo e,integral_const_mul,integral_add (GI.mono_set q0) RI]
  have diff : oscillatory q-mainIntegral q=H*((∫ u in Ioo (0:ℝ) 1,R u)-(∫ u in Ioi (1:ℝ),G u)) := by
    rw [eq,mainIntegral,split_oi GI]; dsimp [H,G,b]; ring
  have ER : ‖∫ u in Ioo (0:ℝ) 1,R u‖≤ innerErr q := by
    apply norm_integral_le_integral_norm _ |>.trans
    rw [setIntegral_congr_fun measurableSet_Ioo eR]
    exact err_integral qp
  have ET : ‖∫ u in Ioi (1:ℝ),G u‖≤tailErr q := by
    apply norm_integral_le_integral_norm _ |>.trans
    have f (u : ℝ) (hu : u∈Ioi (1:ℝ)) : ‖G u‖=Real.sqrt u*Real.exp (-(q/2)*u) := by
      change ‖lap b (1/2) u‖=_
      rw [norm_lap (zero_le_one.trans hu.le),←Real.sqrt_eq_rpow,br]
    rw [setIntegral_congr_fun measurableSet_Ioi f]; exact sqrt_tail qp
  rw [diff,norm_mul,show ‖H‖=Real.sqrt 3*Real.exp (q/2) by simp [H,norm_mul,Complex.norm_exp,br,Real.norm_of_nonneg (Real.sqrt_nonneg _)]]
  exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add ER ET)) (by positivity)

noncomputable def rot (a : ℝ) := Complex.exp ((a:ℂ)*I)
private theorem rot_add (a b : ℝ) : rot (a+b)=rot a*rot b := by simp [rot,add_mul,Complex.exp_add]
private theorem rotated (q a : ℝ) : (rot a*Complex.exp (peakRay q)).re=
    Real.exp (q/2)*Real.cos (Real.sqrt 3*q/2+a) := by
  rw [rot,←Complex.exp_add,Complex.exp_re]
  simp [peakRay_re,peakRay_im,add_comm]
private theorem rot_norm (a : ℝ) : ‖rot a‖=1 := by simp [rot,Complex.norm_exp]

noncomputable def envelope (q : ℝ) := 2*Real.sqrt 3*Real.exp (q/2)*gammaHalf/(q*Real.sqrt q)

private theorem leading {q : ℝ} (qp : 0<q) :
    2*(rot (-Real.pi/3)*mainIntegral q).re=envelope q*Real.cos (Real.sqrt 3*q/2-5*Real.pi/6) := by
  have irot : rot (-Real.pi/2)= -I := by
    rw [rot,Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin,show -Real.pi/2= -(Real.pi/2) by ring]
    simp
  have eq : rot (-Real.pi/3)*mainIntegral q=
      ((Real.sqrt 3*(gammaHalf/(q*Real.sqrt q)):ℝ):ℂ)*(rot (-5*Real.pi/6)*Complex.exp (peakRay q)) := by
    rw [mainIntegral,show (∫ u in Ioi (0:ℝ),lap (peakRay q) (1/2) u)=_ from ray_lap qp,←irot,
      show -5*Real.pi/6= -Real.pi/3+ -Real.pi/2 by ring,rot_add]
    push_cast; ring
  rw [eq,Complex.re_ofReal_mul,rotated]
  unfold envelope
  rw [show Real.sqrt 3*q/2+-5*Real.pi/6=Real.sqrt 3*q/2-5*Real.pi/6 by ring]
  ring

private theorem oscillatory_integrable {q : ℝ} (qp : 0<q) :
    IntegrableOn (fun v : ℝ => (density v:ℂ)*Complex.exp (peakRay q*(v:ℂ))) (Ioo 0 1) := by
  apply (density_integrable.const_mul (Real.exp (q/2))).mono'
    (by apply Measurable.aestronglyMeasurable; unfold density; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (density_nonneg hv.1.le),Complex.norm_exp,show (peakRay q*(v:ℂ)).re=q/2*v by simp [Complex.mul_re,peakRay_re],mul_comm (Real.exp _) (density v)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_of_le_one_right (half_pos qp).le hv.2.le)) (density_nonneg hv.1.le)

private theorem decay_integrable {q : ℝ} (qp : 0<q) :
    IntegrableOn (fun v : ℝ => density v*Real.exp (-q*v)) (Ioo 0 1) := by
  apply density_integrable.mono' (by apply Measurable.aestronglyMeasurable; unfold density; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
  rw [Real.norm_of_nonneg (mul_nonneg (density_nonneg hv.1.le) (Real.exp_pos _).le)]
  exact mul_le_of_le_one_right (density_nonneg hv.1.le) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr qp.le) hv.1.le))

theorem peak_approx {q : ℝ} (qp : 0<q) :
    |(∫ v in Ioo (0:ℝ) 1,density v*osc (q*v))-envelope q*Real.cos (Real.sqrt 3*q/2-5*Real.pi/6)|≤
      2*Real.sqrt 3*Real.exp (q/2)*(innerErr q+tailErr q)+Real.sqrt Real.pi/Real.sqrt q := by
  let W := rot (-Real.pi/3)
  let J := fun v : ℝ => (density v:ℂ)*Complex.exp (peakRay q*(v:ℂ))
  let D := ∫ v in Ioo (0:ℝ) 1,density v*Real.exp (-q*v)
  have Re (v : ℝ) : density v*osc (q*v)=2*(W*J v).re-density v*Real.exp (-q*v) := by
    change _=2*(rot (-Real.pi/3)*((density v:ℂ)*Complex.exp (peakRay q*(v:ℂ)))).re-_
    rw [show rot (-Real.pi/3)*((density v:ℂ)*Complex.exp (peakRay q*(v:ℂ)))=
      (density v:ℂ)*(rot (-Real.pi/3)*Complex.exp (peakRay (q*v))) by dsimp [peakRay]; push_cast; ring,
      Complex.re_ofReal_mul,rotated]
    unfold osc; rw [show Real.sqrt 3*(q*v)/2+-Real.pi/3=Real.sqrt 3*(q*v)/2-Real.pi/3 by ring]; ring
  have hJ := (oscillatory_integrable qp).const_mul W
  have E : (∫ v in Ioo (0:ℝ) 1,density v*osc (q*v))=2*(W*oscillatory q).re-D := by
    have ii : IntegrableOn (fun v => 2*(W*J v).re) (Ioo (0:ℝ) 1) := hJ.re.const_mul _
    rw [setIntegral_congr_fun measurableSet_Ioo (fun v _ => Re v),integral_sub ii (decay_integrable qp),integral_const_mul]
    have h : (∫ v in Ioo (0:ℝ) 1,(W*J v).re)=(∫ v in Ioo (0:ℝ) 1,W*J v).re := integral_re hJ
    rw [h,integral_const_mul]; rfl
  have DN : 0≤D := setIntegral_nonneg measurableSet_Ioo fun v hv => mul_nonneg (density_nonneg hv.1.le) (Real.exp_pos _).le
  have e := cErr qp
  have R : |(W*(oscillatory q-mainIntegral q)).re|≤Real.sqrt 3*Real.exp (q/2)*(innerErr q+tailErr q) := by
    apply (Complex.abs_re_le_norm _).trans
    simpa [norm_mul,W,rot_norm] using e
  rw [E,←leading qp,show 2*(W*oscillatory q).re-D-2*(rot (-Real.pi/3)*mainIntegral q).re=
    2*(W*(oscillatory q-mainIntegral q)).re-D by rw [mul_sub,Complex.sub_re]; dsimp [W]; ring]
  calc
    _ ≤ |2*(W*(oscillatory q-mainIntegral q)).re|+|D| := abs_sub _ _
    _ = 2*|(W*(oscillatory q-mainIntegral q)).re|+D := by rw [abs_mul,abs_of_nonneg DN,abs_of_pos (by norm_num : (0:ℝ)<2)]
    _ ≤ _ := by linarith only [R,decaying_integral qp]

end BigDescents132.Peak
