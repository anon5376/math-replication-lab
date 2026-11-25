import BigDescents132.SmallGeometry

namespace BigDescents132.Slit
open Complex Filter Set
open scoped Topology ComplexConjugate

/-- First-order angle and modulus separation, and rescaled roots, at the
unbounded negative endpoint for the branch points in the integral formula. -/
theorem far_geometry {c : ℝ} (hc : 0<c) (cube : 4*c^3=1) :
    let g := fun e => pointsAt (farParam e)
    let w := (c:ℂ)*Branch.omega3
    Tendsto (fun e : ℝ => (g e).u/(e:ℂ)^2) (𝓝[>] 0) (𝓝 w) ∧
    Tendsto (fun e : ℝ => (g e).r/e^2) (𝓝[>] 0) (𝓝 c) ∧
    Tendsto (fun e : ℝ => (2*Real.pi/3-(g e).u.arg)/e) (𝓝[>] 0) (𝓝 (Real.sqrt 3/(4*c))) ∧
    Tendsto (fun e : ℝ => (g e).logGap/e) (𝓝[>] 0) (𝓝 (3/(4*c))) := by
  obtain ⟨f,z,hf,hz,df,dz,roots,ang,da,dg⟩ := Branch.far_phase_geometry_with_branches hc cube
  let w := (c:ℂ)*Branch.omega3
  have wi : 0<w.im := upperRoot c hc
  have cast : Tendsto (fun e : ℝ => (e:ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Complex.continuous_ofReal.continuousAt (x:=0)).continuousWithinAt (s:=Ioi 0) |>.tendsto
  have tf : Tendsto (fun e : ℝ => f (e:ℂ)) (𝓝[>] 0) (𝓝 (c:ℂ)) := hf ▸ df.continuousAt.tendsto.comp cast
  have tz : Tendsto (fun e : ℝ => z (e:ℂ)) (𝓝[>] 0) (𝓝 w) := by
    simpa only [Function.comp_def,hz,w] using dz.continuousAt.tendsto.comp cast
  have iz := (Complex.continuous_im.tendsto _).comp tz
  have ifr := (Complex.continuous_im.tendsto _).comp tf
  have il : Tendsto (fun e : ℝ => e) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have small : Tendsto (fun e : ℝ => (e:ℂ)^2*f e) (𝓝[>] 0) (𝓝 0) := by
    simpa using (cast.pow 2).mul tf
  have eq : ∀ᶠ e : ℝ in 𝓝[>] 0,
      let g := pointsAt (farParam e)
      g.u=(e:ℂ)^2*z e ∧ (g.r:ℂ)=(e:ℂ)^2*f e := by
    filter_upwards [self_mem_nhdsWithin,il.eventually_lt_const (by norm_num : (0:ℝ)<1),
      cast.eventually roots, iz.eventually_const_lt wi, ifr.eventually_lt iz (by simpa using wi),
      iz.neg.eventually_lt ifr (by simpa using wi), ((Complex.continuous_re.tendsto _).comp small).eventually_lt_const
        (by norm_num : (0:ℂ).re<1)] with e he h1 rt hzpos ihi ilo x1
    have ep : 0<e := he
    have e2 := pow_pos ep 2
    have eC := ofReal_ne_zero.mpr ep.ne'
    let g := pointsAt (farParam e)
    have pe := farParam_val ⟨ep,h1⟩
    obtain ⟨fr,zr⟩ := rt eC
    have pf : (radicand ((farParam e).val:ℂ)).IsRoot ((e:ℂ)^2*f e) := by simpa [pe] using fr
    have pz : (radicand ((farParam e).val:ℂ)).IsRoot ((e:ℂ)^2*z e) := by simpa [pe] using zr
    have zu : (e:ℂ)^2*z e=g.u := g.unique_upper pz (by
      rw [←Complex.ofReal_pow,Complex.im_ofReal_mul]; exact mul_pos e2 hzpos)
    refine ⟨zu.symm,?_⟩
    rcases (g.root_cases _).mp pf with t|t|t|t
    · exact t.symm
    · change ((e:ℂ)^2*f e).re<1 at x1
      rw [t] at x1
      exact (not_lt_of_ge g.large.1.le x1).elim
    · rw [←zu] at t
      have h := congrArg Complex.im (mul_left_cancel₀ (pow_ne_zero 2 eC) t)
      exact (ne_of_lt ihi h).elim
    · rw [←zu,map_mul,map_pow,Complex.conj_ofReal] at t
      have h := congrArg Complex.im (mul_left_cancel₀ (pow_ne_zero 2 eC) t)
      change (f (e:ℂ)).im= -(z (e:ℂ)).im at h
      exact (ne_of_gt ilo h).elim
  have limSlope {k : ℝ} {j : ℝ → ℝ} (h : HasDerivAt j k 0) :
      Tendsto (fun e => (j e-j 0)/e) (𝓝[>] 0) (𝓝 k) := by
    have sub : Ioi (0:ℝ)⊆{0}ᶜ := fun _ a => ne_of_gt a
    simpa [smul_eq_mul,div_eq_mul_inv,mul_comm] using h.tendsto_slope_zero.mono_left (nhdsWithin_mono _ sub)
  have aa := limSlope da
  have gg := limSlope dg
  simp only [Complex.ofReal_zero,ang,sub_self,sub_zero] at aa
  simp only [Complex.ofReal_zero,hf,hz,norm_mul,Branch.omega_norm,mul_one,sub_self,sub_zero] at gg
  refine ⟨tz.congr' ?_,((Complex.continuous_re.tendsto _).comp tf).congr' ?_,aa.congr' ?_,gg.congr' ?_⟩
  · filter_upwards [eq,self_mem_nhdsWithin] with e h he
    have eC := ofReal_ne_zero.mpr (ne_of_gt (show 0<e from he))
    rw [h.1]; field_simp
  · filter_upwards [eq,self_mem_nhdsWithin] with e h he
    have e0 := ne_of_gt (show 0<e from he)
    have k := congrArg Complex.re h.2
    rw [←Complex.ofReal_pow,Complex.re_ofReal_mul,Complex.ofReal_re] at k
    dsimp [Function.comp_def]
    rw [k]; field_simp
  · filter_upwards [eq,self_mem_nhdsWithin] with e h he
    have ep : 0<e := he
    rw [h.1,←Complex.ofReal_pow,Complex.arg_real_mul _ (pow_pos ep 2)]
  · filter_upwards [eq,self_mem_nhdsWithin] with e h he
    have ep : 0<e := he
    let g := pointsAt (farParam e)
    have e2 := pow_pos ep 2
    have rc := congrArg norm h.2
    have uc := congrArg norm h.1
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg g.rpos.le,Complex.norm_real,Real.norm_of_nonneg ep.le] at rc
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg ep.le] at uc
    have f0 : 0<‖f (e:ℂ)‖ := (mul_pos_iff_of_pos_left e2).mp (rc ▸ g.rpos)
    have z0 : 0<‖z (e:ℂ)‖ := (mul_pos_iff_of_pos_left e2).mp (uc ▸ norm_pos_iff.mpr g.u_ne)
    change _ = Real.log (g.r/‖g.u‖)/e
    rw [rc,uc,mul_div_mul_left _ _ e2.ne',Real.log_div f0.ne' z0.ne']

end BigDescents132.Slit
