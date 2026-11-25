import BigDescents132.CompactInterior

namespace BigDescents132.Slit
open Complex Filter Set
open scoped Topology ComplexConjugate

/-- A total parameter map for stating right-hand endpoint limits; all positive
near-end coordinates and all sufficiently small positive far-end coordinates
map to their exact prescribed parameters. -/
noncomputable def parameter (x : ℝ) : Param := if h : 1<x then ⟨x,h⟩ else ⟨2,by norm_num⟩

noncomputable def nearParam (d : ℝ) := parameter (1+d^3)
noncomputable def farParam (e : ℝ) := parameter (e⁻¹^3)

theorem nearParam_val {d : ℝ} (hd : 0<d) : (nearParam d).val=1+d^3 := by
  have h : 1<1+d^3 := lt_add_of_pos_right _ (pow_pos hd _)
  simp only [nearParam,parameter,dif_pos h]

theorem farParam_val {e : ℝ} (he : e∈Ioo 0 1) : (farParam e).val=e⁻¹^3 := by
  have hi : 1<e⁻¹ := (one_lt_inv₀ he.1).mpr he.2
  simp only [farParam,parameter,dif_pos (show 1<e⁻¹^3 from one_lt_pow₀ hi (by decide))]

theorem upperRoot (c : ℝ) (hc : 0<c) : 0<((c:ℂ)*Branch.omega3).im := by
  rw [Complex.im_ofReal_mul,Branch.omega_im]; positivity

private theorem real_slope {f : ℝ → ℝ} {k : ℝ} (h : HasDerivAt f k 0) :
    Tendsto (fun d : ℝ => (f d-f 0)/d) (𝓝[>] 0) (𝓝 k) := by
  have sub : Ioi (0:ℝ)⊆{0}ᶜ := fun _ hx => ne_of_gt hx
  simpa [smul_eq_mul,div_eq_mul_inv,mul_comm] using h.tendsto_slope_zero.mono_left (nhdsWithin_mono _ sub)

private theorem cslope {f : ℂ → ℂ} {k : ℂ} (h : HasDerivAt f k 0) :
    Tendsto (fun d : ℝ => (f d-f 0)/(d:ℂ)) (𝓝[>] 0) (𝓝 k) := by
  have d : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨by simpa using (Complex.continuous_ofReal.continuousAt (x:=0)).continuousWithinAt (s:=Ioi 0) |>.tendsto,?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact ofReal_ne_zero.mpr (ne_of_gt hx)
  simpa [smul_eq_mul,div_eq_mul_inv,mul_comm,Function.comp_def] using h.tendsto_slope_zero.comp d

private theorem im_div_real (z : ℂ) {d : ℝ} (hd : d≠0) :
    (z/(d:ℂ)).im=z.im/d := by
  simp [Complex.div_im,hd]; field_simp; ring

/-- Actual upper root, its angle, and its log modulus in the small-end
coordinate. The root is selected by positive imaginary part. -/
theorem small_upper {c : ℝ} (hc : 0<c) (cube : c^3=4) :
    let u := fun d => (pointsAt (nearParam d)).u
    let w := (c:ℂ)*Branch.omega3
    Tendsto (fun d : ℝ => (u d-1)/(d:ℂ)) (𝓝[>] 0) (𝓝 w) ∧
    Tendsto u (𝓝[>] 0) (𝓝 1) ∧
    Tendsto (fun d : ℝ => (u d).arg/d) (𝓝[>] 0) (𝓝 w.im) ∧
    Tendsto (fun d : ℝ => Real.log ‖u d‖/d) (𝓝[>] 0) (𝓝 w.re) := by
  let w := (c:ℂ)*Branch.omega3
  have W : w^3=4 := by dsimp [w]; rw [mul_pow,Branch.omega_cube,mul_one]; exact_mod_cast cube
  obtain ⟨f,f0,hf,roots⟩ := Branch.small_branch (w:=w) (Or.inr W)
  have Dz := cslope hf
  rw [f0] at Dz
  have Im := (Complex.continuous_im.tendsto _).comp Dz
  have pos := Im.eventually_const_lt (upperRoot c hc)
  have cf := Complex.continuous_ofReal.continuousAt (x:=0)
  have cast : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using cf.continuousWithinAt (s:=Ioi 0) |>.tendsto
  have eql : ∀ᶠ d : ℝ in 𝓝[>] 0, (pointsAt (nearParam d)).u=f (d:ℂ) := by
    filter_upwards [self_mem_nhdsWithin,cast.eventually roots,pos] with d hd root h
    have p : 0<d := hd
    have HH : 0<(f (d:ℂ)).im/d := by simpa [Function.comp_def,im_div_real _ p.ne'] using h
    symm
    apply (pointsAt (nearParam d)).unique_upper _ ((div_pos_iff_of_pos_right p).mp HH)
    change (radicand ((nearParam d).val:ℂ)).IsRoot _
    simpa [nearParam_val p] using root
  obtain ⟨a,l⟩ := Branch.log_phase f0 hf (Complex.mem_slitPlane_iff.mpr (Or.inl (by simp)))
  have ta := real_slope a
  have tl := real_slope l
  simp only [Complex.ofReal_zero,f0,Complex.arg_one,norm_one,Real.log_one,sub_zero,div_one] at ta tl
  have cf' := hf.continuousAt.tendsto.comp cast
  rw [f0] at cf'
  exact ⟨Dz.congr' (eql.mono fun d h => by simp only [h]),cf'.congr' (eql.mono fun _ h => h.symm),
    ta.congr' (eql.mono fun d h => by simp only [h]),tl.congr' (eql.mono fun d h => by simp only [h])⟩

/-- The order location 1/s < r < 1 squeezes the small real root more
tightly than first order and determines its logarithmic slope. -/
theorem small_real :
    let r := fun d => (pointsAt (nearParam d)).r
    Tendsto (fun d : ℝ => (r d-1)/d) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun d : ℝ => Real.log (r d)/d) (𝓝[>] 0) (𝓝 0) := by
  have lim : Tendsto (fun d : ℝ => d^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((tendsto_id (α:=ℝ) (x:=𝓝 0)).pow 2).mono_left (nhdsWithin_le_nhds (s:=Ioi 0))
  have bound : ∀ᶠ d : ℝ in 𝓝[>] 0, let r := (pointsAt (nearParam d)).r
      |(r-1)/d|≤d^2 ∧ |Real.log r/d|≤d^2 := by
    filter_upwards [self_mem_nhdsWithin] with d hd
    have pos : 0<d := hd
    let g := pointsAt (nearParam d)
    have r1 := g.small.2
    have lo : 1/(1+d^3)<g.r := (congrArg (fun t : ℝ => 1/t) (nearParam_val pos)).symm ▸ g.small.1
    have p : 0<1+d^3 := by positivity
    have pos3 : 0<d^3 := by positivity
    have re := (div_lt_iff₀ p).mp lo
    have l := (Real.log_lt_log (one_div_pos.mpr p) lo).le
    rw [Real.log_div one_ne_zero p.ne',Real.log_one,zero_sub] at l
    have l1 := Real.log_nonpos g.rpos.le r1.le
    have l3 := Real.log_le_sub_one_of_pos p
    change |(g.r-1)/d|≤d^2 ∧ |Real.log g.r/d|≤d^2
    rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr r1.le) pos.le),
      abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg l1 pos.le),←neg_div,←neg_div,
      div_le_iff₀ pos,div_le_iff₀ pos]
    constructor
    · nlinarith [mul_nonneg (sub_nonneg.mpr r1.le) pos3.le]
    · linarith
  exact ⟨squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using bound.mono fun _ h => h.1) lim,
    squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using bound.mono fun _ h => h.2) lim⟩

/-- The logarithmic separation of the actual positive and upper roots has a
strictly positive first-order slope at the small end. -/
theorem small_gap {c : ℝ} (hc : 0<c) (cube : c^3=4) :
    Tendsto (fun d => (pointsAt (nearParam d)).logGap/d) (𝓝[>] 0) (𝓝 (c/2)) := by
  have l := small_real.2.sub (small_upper hc cube).2.2.2
  simp only [Complex.re_ofReal_mul,Branch.omega_re,zero_sub] at l
  convert l using 1
  · ext x
    let g := pointsAt (nearParam x)
    exact (congrArg (fun a : ℝ => a/x) (Real.log_div g.rpos.ne' (norm_ne_zero_iff.mpr g.u_ne))).trans (sub_div _ _ _)
  · congr 1; ring

end BigDescents132.Slit
