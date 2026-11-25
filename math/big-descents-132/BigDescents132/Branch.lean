import BigDescents132.Quartic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

namespace BigDescents132.Branch
open Complex Filter
open scoped Topology

private noncomputable def triangle (a b : ℂ) (hb : b≠0) :
    (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) where
  toFun p := (p.1,a*p.1+b*p.2)
  invFun p := (p.1,(p.2-a*p.1)/b)
  left_inv p := by ext <;> simp [mul_div_cancel_left₀, hb]
  right_inv p := by ext <;> simp [mul_div_cancel₀, hb]
  map_add' p q := by
    ext <;> simp
    all_goals ring
  map_smul' c p := by
    ext <;> simp
    all_goals ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem implicit_branch (q : ℂ × ℂ → ℂ) (w a b : ℂ) (hb : b≠0)
    (hq : q (0,w) = 0)
    (hd : HasStrictFDerivAt q
      (a • ContinuousLinearMap.fst ℂ ℂ ℂ + b • ContinuousLinearMap.snd ℂ ℂ ℂ) (0,w)) :
    ∃ f : ℂ → ℂ, f 0 = w ∧ HasDerivAt f (-a/b) 0 ∧
      (∀ᶠ z in 𝓝 (0:ℂ), q (z,f z) = 0) ∧
      ∀ᶠ p in 𝓝 ((0:ℂ),w), q p = 0 → p.2 = f p.1 := by
  let F := fun p : ℂ × ℂ => (p.1, q p)
  have hf : HasStrictFDerivAt F (triangle a b hb : _ →L[ℂ] _) (0,w) := by
    convert (hasStrictFDerivAt_fst (𝕜:=ℂ)).prodMk hd using 1
  have hzero : F (0,w) = (0,0) := by simp [F,hq]
  let g := hf.localInverse F (triangle a b hb) (0,w)
  let i := fun z : ℂ => (z,(0:ℂ))
  have hi : HasDerivAt i (1,0) 0 := (hasDerivAt_id (0:ℂ)).prodMk (hasDerivAt_const 0 (0:ℂ))
  have hinv := hf.localInverse_apply_image
  have hg := hf.to_localInverse.hasFDerivAt
  have he := hf.eventually_right_inverse
  rw [hzero] at hinv hg he
  refine ⟨fun z => (g (i z)).2, congrArg Prod.snd hinv, ?_, ?_, ?_⟩
  · have H : HasFDerivAt g ((triangle a b hb).symm : _ →L[ℂ] _) (i 0) := hg
    have comp : HasDerivAt (g ∘ i) ((triangle a b hb).symm (1,0)) 0 := H.comp_hasDerivAt 0 hi
    have h := (ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt.comp_hasDerivAt (0:ℂ)
      comp
    change HasDerivAt (fun z => (g (i z)).2) ((0-a*1)/b) 0 at h
    simpa using h
  · filter_upwards [hi.continuousAt.tendsto.eventually he] with z hz
    have h₁ : (g (i z)).1 = z := congrArg Prod.fst hz
    have h₂ : q ((g (i z)).1,(g (i z)).2) = 0 := congrArg Prod.snd hz
    rwa [h₁] at h₂
  · filter_upwards [hf.eventually_left_inverse] with p hp hqp
    have hp' : F p = i p.1 := Prod.ext rfl hqp
    rw [hp'] at hp
    exact (congrArg Prod.snd hp).symm

/-- The quartic after substituting s = ε⁻³ and z = ε²w. -/
noncomputable def farQuartic (e w : ℂ) : ℂ :=
  1-4*w^3+6*e*w^2+e^2*(w^4-4*w)

theorem far_regrading {e : ℂ} (he : e≠0) (w : ℂ) :
    (radicand (e⁻¹^3)).eval (e^2*w) = farQuartic e w := by
  simp [radicand,farQuartic]
  field_simp
  ring

private theorem far_differential (w : ℂ) : HasStrictFDerivAt
    (fun p : ℂ × ℂ => farQuartic p.1 p.2)
    ((6*w^2) • ContinuousLinearMap.fst ℂ ℂ ℂ + (-12*w^2) • ContinuousLinearMap.snd ℂ ℂ ℂ)
    (0,w) := by
  have hf := hasStrictFDerivAt_fst (𝕜:=ℂ) (p:=((0:ℂ),w))
  have hs := hasStrictFDerivAt_snd (𝕜:=ℂ) (p:=((0:ℂ),w))
  have h₁ := hasStrictFDerivAt_const (𝕜:=ℂ) (1:ℂ) ((0:ℂ),w)
  have h₂ := hs.mul hs
  have h₃ := h₂.mul hs
  have h₄ := h₂.mul h₂
  have h := ((h₁.sub (h₃.const_mul 4)).add ((hf.const_mul 6).mul h₂)).add
    ((hf.mul hf).mul (h₄.sub (hs.const_mul 4)))
  convert h using 1
  · funext p
    simp [farQuartic]
    ring
  · apply ContinuousLinearMap.ext
    intro p
    simp [ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply]
    ring

/-- Each of the three finite limiting roots lifts to an actual branch of the
quartic with derivative 1/2 with respect to ε. -/
theorem far_branch {w : ℂ} (hw : 4*w^3=1) :
    ∃ f : ℂ → ℂ, f 0 = w ∧ HasDerivAt f (1/2) 0 ∧
      ∀ᶠ e in 𝓝 (0:ℂ), e≠0 → (radicand (e⁻¹^3)).IsRoot (e^2*f e) := by
  have hn : w≠0 := by rintro rfl; norm_num at hw
  obtain ⟨f,hf,hd,hr,_⟩ := implicit_branch (fun p => farQuartic p.1 p.2) w
    (6*w^2) (-12*w^2) (by simp [hn]) (by simp [farQuartic,hw]) (far_differential w)
  refine ⟨f,hf,?_,?_⟩
  · convert hd using 1
    field_simp
    ring
  · filter_upwards [hr] with e he hn'
    exact (far_regrading hn' (f e)).trans he

/-- The normalized quartic at the endpoint s=1+δ³. -/
noncomputable def smallQuartic (d w : ℂ) : ℂ :=
  (1+d^3)^2*w^4-6*(1+d^3)*d*w^2-(4+8*d^3)*w-3*d^2

theorem small_regrading (d w : ℂ) :
    (radicand (1+d^3)).eval (1+d*w) = d^4*smallQuartic d w := by
  simp [radicand,smallQuartic]
  ring

private theorem small_differential (w : ℂ) : HasStrictFDerivAt
    (fun p : ℂ × ℂ => smallQuartic p.1 p.2)
    ((-6*w^2) • ContinuousLinearMap.fst ℂ ℂ ℂ + (4*w^3-4) • ContinuousLinearMap.snd ℂ ℂ ℂ)
    (0,w) := by
  have D := hasStrictFDerivAt_fst (𝕜:=ℂ) (p:=((0:ℂ),w))
  have W := hasStrictFDerivAt_snd (𝕜:=ℂ) (p:=((0:ℂ),w))
  have D₂ := D.mul D
  have D₃ := D₂.mul D
  have S := (hasStrictFDerivAt_const (𝕜:=ℂ) (1:ℂ) ((0:ℂ),w)).add D₃
  have W₂ := W.mul W
  have h := ((((S.mul S).mul (W₂.mul W₂)).sub (((S.const_mul 6).mul D).mul W₂)).sub
    (((hasStrictFDerivAt_const (𝕜:=ℂ) (4:ℂ) ((0:ℂ),w)).add (D₃.const_mul 8)).mul W)).sub
    (D₂.const_mul 3)
  convert h using 1
  · funext p
    simp [smallQuartic]
    ring
  · apply ContinuousLinearMap.ext
    intro p
    simp [ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply]
    ring

/-- For every one of the four limiting roots the physical branch at δ=0
has derivative w. The conclusion concerns zeros of the unnormalized quartic. -/
theorem small_branch {w : ℂ} (hw : w=0 ∨ w^3=4) :
    ∃ f : ℂ → ℂ, f 0=1 ∧ HasDerivAt f w 0 ∧
      ∀ᶠ d in 𝓝 (0:ℂ), (radicand (1+d^3)).IsRoot (f d) := by
  have hzero : smallQuartic 0 w = 0 := by
    rcases hw with rfl|h
    · norm_num [smallQuartic]
    · simp [smallQuartic, show w^4=w^3*w by ring,h]
  have hn : 4*w^3-4≠0 := by rcases hw with rfl|h <;> norm_num [*]
  obtain ⟨g,hg,hd,hr,_⟩ := implicit_branch (fun p => smallQuartic p.1 p.2) w
    (-6*w^2) (4*w^3-4) hn hzero (small_differential w)
  refine ⟨fun d => 1+d*g d, by simp, ?_, ?_⟩
  · simpa [hg] using (hasDerivAt_const (0:ℂ) (1:ℂ)).add ((hasDerivAt_id (0:ℂ)).mul hd)
  · filter_upwards [hr] with d h
    change (radicand _).eval _ = 0
    rw [small_regrading, h, mul_zero]

/-- Upper nonreal cube root of unity. -/
noncomputable def omega3 : ℂ := Complex.exp (((2*Real.pi/3:ℝ):ℂ)*I)

theorem omega_cube : omega3^3=1 := by
  unfold omega3
  rw [← Complex.exp_nat_mul, ← Complex.exp_two_pi_mul_I]
  congr 1
  push_cast
  ring

theorem omega_re : omega3.re= -1/2 := by
  rw [omega3,Complex.exp_re]
  simp only [Complex.mul_I_re, Complex.ofReal_im, neg_zero, Real.exp_zero, Complex.mul_I_im,
    Complex.ofReal_re, one_mul]
  rw [show 2*Real.pi/3 = Real.pi-Real.pi/3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
  ring

theorem omega_im : omega3.im=Real.sqrt 3/2 := by
  rw [omega3,Complex.exp_im]
  simp only [Complex.mul_I_re, Complex.ofReal_im, neg_zero, Real.exp_zero, Complex.mul_I_im,
    Complex.ofReal_re, one_mul]
  rw [show 2*Real.pi/3 = Real.pi-Real.pi/3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]

theorem omega_norm : ‖omega3‖=1 := by simp [omega3,Complex.norm_exp]

private theorem omega_arg : omega3.arg=2*Real.pi/3 := by
  rw [omega3,Complex.exp_mul_I]
  exact Complex.arg_cos_add_sin_mul_I ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩

theorem log_phase {f : ℂ → ℂ} {w w' : ℂ} (hf : f 0=w)
    (hd : HasDerivAt f w' 0) (hw : w∈Complex.slitPlane) :
    HasDerivAt (fun x : ℝ => (f x).arg) (w'/w).im 0 ∧
    HasDerivAt (fun x : ℝ => Real.log ‖f x‖) (w'/w).re 0 := by
  have h := hd.clog (hf.symm ▸ hw)
  rw [hf] at h
  have h' : HasDerivAt (fun z : ℝ => Complex.log (f z)) (w'/w) 0 := by
    simpa using (show HasDerivAt (fun z => Complex.log (f z)) (w'/w) ((0:ℝ):ℂ) from by simpa using h).comp_ofReal
  constructor
  · simpa only [Function.comp_def,Complex.imCLM_apply,Complex.log_im] using
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 h'
  · simpa only [Function.comp_def,Complex.reCLM_apply,Complex.log_re] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 h'

/-- The normalized conjugate and positive limiting roots near infinity have
the angle and logarithmic modulus-gap slopes used in the phase estimate. -/
theorem far_phase_geometry_with_branches {c : ℝ} (hc : 0<c) (hcube : 4*c^3=1) :
    ∃ r z : ℂ → ℂ, r 0=(c:ℂ) ∧ z 0=(c:ℂ)*omega3 ∧
      HasDerivAt r (1/2:ℂ) 0 ∧ HasDerivAt z (1/2:ℂ) 0 ∧
      (∀ᶠ e in 𝓝 (0:ℂ), e≠0 →
        (radicand (e⁻¹^3)).IsRoot (e^2*r e) ∧ (radicand (e⁻¹^3)).IsRoot (e^2*z e)) ∧
      (z 0).arg=2*Real.pi/3 ∧
      HasDerivAt (fun x : ℝ => 2*Real.pi/3-(z x).arg) (Real.sqrt 3/(4*c)) 0 ∧
      HasDerivAt (fun x : ℝ => Real.log ‖r x‖-Real.log ‖z x‖) (3/(4*c)) 0 := by
  have hcube' : 4*(c:ℂ)^3=1 := by exact_mod_cast hcube
  obtain ⟨r,hr,dr,er⟩ := far_branch hcube'
  have hz3 : 4*((c:ℂ)*omega3)^3=1 := by rw [mul_pow,omega_cube,mul_one,hcube']
  obtain ⟨z,hz,dz,ez⟩ := far_branch hz3
  have hω : (c:ℂ)*omega3 ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    rw [Complex.im_ofReal_mul, omega_im]
    positivity
  have hC : (c:ℂ) ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hc)
  obtain ⟨_,lr⟩ := log_phase hr dr hC
  obtain ⟨az,lz⟩ := log_phase hz dz hω
  have hh : Complex.normSq ((c:ℂ)*omega3) = c^2 := by
    rw [← Complex.sq_norm, norm_mul, omega_norm, mul_one, Complex.norm_real,Real.norm_of_nonneg hc.le]
  have him : ((1/2:ℂ)/((c:ℂ)*omega3)).im = -(Real.sqrt 3/(4*c)) := by
    rw [Complex.div_im,hh,Complex.re_ofReal_mul,Complex.im_ofReal_mul,omega_re,omega_im]
    norm_num
    field_simp; ring
  have hre : ((1/2:ℂ)/((c:ℂ)*omega3)).re = -(1/(4*c)) := by
    rw [Complex.div_re,hh,Complex.re_ofReal_mul,Complex.im_ofReal_mul,omega_re,omega_im]
    norm_num
    field_simp; ring
  refine ⟨r,z,hr,hz,dr,dz,er.and ez |>.mono (fun _ h hn => ⟨h.1 hn,h.2 hn⟩),?_,?_,?_⟩
  · rw [hz, Complex.arg_real_mul _ hc, omega_arg]
  · rw [him] at az
    simpa only [neg_neg] using az.const_sub (2*Real.pi/3)
  · convert lr.sub lz using 1
    rw [hre,Complex.div_ofReal_re]
    norm_num
    field_simp
    ring

theorem far_phase_geometry {c : ℝ} (hc : 0<c) (hcube : 4*c^3=1) :
    ∃ r z : ℂ → ℂ, r 0=(c:ℂ) ∧ z 0=(c:ℂ)*omega3 ∧
      (∀ᶠ e in 𝓝 (0:ℂ), e≠0 →
        (radicand (e⁻¹^3)).IsRoot (e^2*r e) ∧ (radicand (e⁻¹^3)).IsRoot (e^2*z e)) ∧
      (z 0).arg=2*Real.pi/3 ∧
      HasDerivAt (fun x : ℝ => 2*Real.pi/3-(z x).arg) (Real.sqrt 3/(4*c)) 0 ∧
      HasDerivAt (fun x : ℝ => Real.log ‖r x‖-Real.log ‖z x‖) (3/(4*c)) 0 := by
  obtain ⟨r,z,hr,hz,_,_,rest⟩ := far_phase_geometry_with_branches hc hcube
  exact ⟨r,z,hr,hz,rest⟩

/-- The two actual branches meeting at z=1 have the required small-end phase
and logarithmic modulus-gap derivatives in the coordinate δ. -/
theorem small_phase_geometry {c : ℝ} (hcube : c^3=4) :
    ∃ r z : ℂ → ℂ, r 0=1 ∧ z 0=1 ∧
      (∀ᶠ d in 𝓝 (0:ℂ), (radicand (1+d^3)).IsRoot (r d) ∧
        (radicand (1+d^3)).IsRoot (z d)) ∧
      HasDerivAt (fun x : ℝ => (z x).arg) (Real.sqrt 3*c/2) 0 ∧
      HasDerivAt (fun x : ℝ => Real.log ‖r x‖-Real.log ‖z x‖) (c/2) 0 := by
  have hc : (c:ℂ)^3=4 := by exact_mod_cast hcube
  obtain ⟨r,hr,dr,er⟩ := small_branch (w:=0) (Or.inl rfl)
  obtain ⟨z,hz,dz,ez⟩ := small_branch (w:=(c:ℂ)*omega3)
    (Or.inr (by rw [mul_pow,hc,omega_cube]; ring))
  have ho : (1:ℂ)∈Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl (by norm_num))
  obtain ⟨_,lr⟩ := log_phase hr dr ho
  obtain ⟨az,lz⟩ := log_phase hz dz ho
  refine ⟨r,z,hr,hz,er.and ez,?_,?_⟩
  · simpa [Complex.im_ofReal_mul,omega_im,mul_comm,mul_div_assoc] using az
  · convert lr.sub lz using 1
    simp [Complex.re_ofReal_mul,omega_re]
    ring

end BigDescents132.Branch
