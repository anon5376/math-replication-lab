import BigDescents132.PhaseLift

namespace BigDescents132.Slit
open Complex Filter Set
open scoped Topology ComplexConjugate

theorem argument_div_real (z : ℂ) {a : ℝ} (ha : 0<a) : (z/(a:ℂ)).arg=z.arg := by
  rw [div_eq_mul_inv,←Complex.ofReal_inv,Complex.arg_mul_real (inv_pos.mpr ha)]

private theorem arg_real_factor (u : ℂ) {a : ℝ} (ha : 0<a) :
    (argFactor a u).arg=((a:ℂ)-u).arg := by
  have eq : argFactor a u=((a:ℂ)-u)/(a:ℂ) := by unfold argFactor; field_simp [ofReal_ne_zero.mpr ha.ne']
  rw [eq,argument_div_real _ ha]

private theorem arg_conj_factor {u : ℂ} (hu : 0<u.im) :
    (argFactor (conj u) u).arg=u.arg-Real.pi/2 := by
  have u0 : u≠0 := by intro e; simp [e] at hu
  have c0 : conj u≠0 := by simp [u0]
  have ii : 0<2*u.im/Complex.normSq u := div_pos (by positivity) (Complex.normSq_pos.mpr u0)
  have eq : argFactor (conj u) u=((2*u.im/Complex.normSq u:ℝ):ℂ)*((-I)*u) := by
    unfold argFactor
    rw [show 1-u/conj u=(conj u-u)/conj u by field_simp,
      show conj u-u= -(u-conj u) by ring,Complex.sub_conj,div_eq_mul_inv,Complex.inv_def]
    simp only [map_div,Complex.ofReal_div,Complex.normSq_conj,starRingEnd_self_apply,Complex.ofReal_inv]
    ring
  have span : (-I).arg+u.arg ∈ Ioc (-Real.pi) Real.pi := by
    rw [Complex.arg_neg_I]; constructor <;> linarith [Real.pi_pos,Complex.arg_le_pi u,Complex.arg_nonneg_iff.mpr hu.le]
  rw [eq,Complex.arg_real_mul _ ii,Complex.arg_mul (neg_ne_zero.mpr Complex.I_ne_zero) u0 span,Complex.arg_neg_I]; ring

theorem Points.offset_formula {s : ℝ} (g : Points s) :
    g.phaseOffset=Real.pi+(((g.r:ℂ)-g.u).arg+((g.R:ℂ)-g.u).arg+(g.u.arg-Real.pi/2))/2-
      g.u.arg-((s⁻¹:ℝ)-g.u).arg := by
  have sp := zero_lt_one.trans g.parameter
  have eq : (1-(s:ℂ)*g.u)=(s:ℂ)*((s⁻¹:ℝ)-g.u) := by push_cast; field_simp [ofReal_ne_zero.mpr sp.ne']
  rw [Points.phaseOffset,arg_real_factor _ g.rpos,arg_real_factor _ g.Rpos,arg_conj_factor g.upper,eq,Complex.arg_real_mul _ sp]

private theorem arg_const {c : ℝ} (hp : 0<c) :
    (-((c:ℂ)*Branch.omega3)).arg= -Real.pi/3 ∧ ((c:ℂ)-(c:ℂ)*Branch.omega3).arg= -Real.pi/6 := by
  have root := Real.sq_sqrt (by norm_num : 0≤(3:ℝ))
  have sqrtpos := Real.sqrt_pos_of_pos (by norm_num : 0<(3:ℝ))
  have f : -Branch.omega3=direction (-Real.pi/3) := by
    apply Complex.ext <;> simp [direction,Complex.exp_re,Complex.exp_im,Branch.omega_re,Branch.omega_im,
      show -Real.pi/3= -(Real.pi/3) by ring,Real.cos_pi_div_three,Real.sin_pi_div_three]
    ring
  have h : 1-Branch.omega3=(Real.sqrt 3:ℂ)*direction (-Real.pi/6) := by
    apply Complex.ext <;> simp [direction,Complex.exp_re,Complex.exp_im,Branch.omega_re,Branch.omega_im,
      show -Real.pi/6= -(Real.pi/6) by ring,Real.cos_pi_div_six,Real.sin_pi_div_six,Complex.mul_im] <;> nlinarith
  have ang {a : ℝ} (ha : a∈Ioc (-Real.pi) Real.pi) : (direction a).arg=a := by
    rw [direction,Complex.exp_mul_I]; exact Complex.arg_cos_add_sin_mul_I ha
  constructor
  · rw [←mul_neg,Complex.arg_real_mul _ hp,f,ang ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩]
  · rw [show (c:ℂ)-(c:ℂ)*Branch.omega3=(c:ℂ)*(1-Branch.omega3) by ring,
      Complex.arg_real_mul _ hp,h,Complex.arg_real_mul _ sqrtpos,ang ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩]

/-- The other positive root has slope c in the near-end coordinate. -/
theorem small_large {c : ℝ} (cp : 0<c) (cube : c^3=4) :
    Tendsto (fun d : ℝ => ((pointsAt (nearParam d)).R-1)/d) (𝓝[>] 0) (𝓝 c) := by
  have cc : (c:ℂ)^3=4 := by exact_mod_cast cube
  obtain ⟨f,f0,df,roots⟩ := Branch.small_branch (w:=(c:ℂ)) (Or.inr cc)
  have hi : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨by simpa using (Complex.continuous_ofReal.continuousAt (x:=0)).continuousWithinAt (s:=Ioi 0) |>.tendsto,?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact ofReal_ne_zero.mpr (ne_of_gt hx)
  have z : Tendsto (fun x : ℝ => (f x-1)/(x:ℂ)) (𝓝[>] 0) (𝓝 (c:ℂ)) := by
    simpa [f0,smul_eq_mul,div_eq_mul_inv,mul_comm,Function.comp_def] using df.tendsto_slope_zero.comp hi
  have up := (small_upper cp cube).1
  have re_div (w : ℂ) (x : ℝ) : (w/(x:ℂ)).re=w.re/x := Complex.div_ofReal_re _ _
  have fr : Tendsto (fun d : ℝ => ((f d).re-1)/d) (𝓝[>] 0) (𝓝 c) := by
    simpa [Function.comp_def,re_div] using (Complex.continuous_re.tendsto _).comp z
  have ur : Tendsto (fun d : ℝ => ((pointsAt (nearParam d)).u.re-1)/d) (𝓝[>] 0) (𝓝 (c*(-1/2))) := by
    simpa [Function.comp_def,re_div,Branch.omega_re] using (Complex.continuous_re.tendsto _).comp up
  apply fr.congr'
  have rts := (hi.mono_right nhdsWithin_le_nhds).eventually roots
  filter_upwards [self_mem_nhdsWithin,rts,fr.eventually_const_lt cp,ur.eventually_lt_const (by linarith : c*(-1/2)<0)] with d hd rt fp un
  have dp : 0<d := hd
  have ff : 1<(f (d:ℂ)).re := sub_pos.mp ((div_pos_iff_of_pos_right dp).mp fp)
  have uu : (pointsAt (nearParam d)).u.re<1 := sub_neg.mp (by simpa only [zero_mul] using (div_lt_iff₀ dp).mp un)
  let g := pointsAt (nearParam d)
  have root : (radicand ((nearParam d).val:ℂ)).IsRoot (f d) := by simpa [nearParam_val dp] using rt
  rcases (g.root_cases _).mp root with e|e|e|e
  · rw [e] at ff; exact (not_lt_of_ge g.small.2.le ff).elim
  · rw [e]; rfl
  · rw [e] at ff; exact (not_lt_of_ge ff.le uu).elim
  · rw [e,Complex.conj_re] at ff; exact (not_lt_of_ge ff.le uu).elim

private theorem scale_arg {l : Filter ℝ} {v : ℝ → ℝ} {f : ℝ → ℂ} {w : ℂ}
    (vp : ∀ᶠ d in l, 0<v d) (h : Tendsto (fun d => f d/(v d:ℂ)) l (𝓝 w)) (cut : w∈slitPlane) :
    Tendsto (fun d => (f d).arg) l (𝓝 w.arg) := by
  apply ((Complex.continuousAt_arg cut).tendsto.comp h).congr'
  exact vp.mono fun d hd => argument_div_real (f d) hd

private theorem lower_slit {c : ℝ} (cp : 0<c) :
    -((c:ℂ)*Branch.omega3)∈slitPlane ∧ (c:ℂ)-(c:ℂ)*Branch.omega3∈slitPlane := by
  have h := upperRoot c cp
  constructor <;> apply Complex.mem_slitPlane_iff.mpr (Or.inr ?_) <;> simp [h.ne',Complex.im_ofReal_mul,Branch.omega_im,cp.ne']

/-- The continuous lift uses the prescribed small-end offset, without a
possible hidden multiple of 2π. -/
theorem small_phase_offset : Tendsto (fun d => (pointsAt (nearParam d)).phaseOffset)
    (𝓝[>] (0:ℝ)) (𝓝 (5*Real.pi/6)) := by
  let c : ℝ := 4^((3:ℝ)⁻¹)
  have cp : 0<c := Real.rpow_pos_of_pos (by norm_num) _
  have cube : c^3=4 := Real.rpow_inv_natCast_pow (by norm_num) (by decide)
  let w := (c:ℂ)*Branch.omega3
  let g := fun e => pointsAt (nearParam e)
  have U := (small_upper cp cube).1
  have angle := (Complex.continuousAt_arg (show (1:ℂ)∈slitPlane by simp)).tendsto.comp (small_upper cp cube).2.1
  simp only [Complex.arg_one,Function.comp_def] at angle
  have l : Tendsto (fun e : ℝ => e) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have P : Tendsto (fun e : ℝ => ((nearParam e).val⁻¹-1)/e) (𝓝[>] 0) (𝓝 0) := by
    have v := (l.pow 2).neg.div ((tendsto_const_nhds (x:=(1:ℝ))).add (l.pow 3)) (by norm_num)
    simp only [zero_pow (by decide : 2≠0),zero_pow (by decide : 3≠0),neg_zero,add_zero,zero_div] at v
    apply v.congr'
    filter_upwards [self_mem_nhdsWithin] with e he
    have ep : 0<e := he
    have pp : 0<1+e^3 := by positivity
    rw [nearParam_val ep]; field_simp [ep.ne',pp.ne']; ring
  have A (f : ℝ → ℝ) {a : ℝ} (F : Tendsto (fun e => (f e-1)/e) (𝓝[>] (0:ℝ)) (𝓝 a))
      (cs : (a:ℂ)-w∈slitPlane) : Tendsto (fun e => ((f e:ℂ)-(g e).u).arg) (𝓝[>] 0) (𝓝 ((a:ℂ)-w).arg) := by
    apply scale_arg (v:=id) self_mem_nhdsWithin _ cs
    apply (((Complex.continuous_ofReal.tendsto _).comp F).sub U).congr'
    filter_upwards with e
    dsimp [g]; push_cast; ring
  obtain ⟨cut1,cut2⟩ := lower_slit cp
  obtain ⟨negw,dw⟩ := arg_const cp
  have h1 := A _ small_real.1 (by simpa [w] using cut1)
  have h2 := A _ (small_large cp cube) cut2
  have h3 := A _ P (by simpa [w] using cut1)
  simp only [Complex.ofReal_zero,zero_sub,w,negw,dw] at h1 h2 h3
  have ll := (((tendsto_const_nhds (x:=Real.pi)).add (((h1.add h2).add (angle.sub (tendsto_const_nhds (x:=Real.pi/2)))).div_const 2)).sub angle).sub h3
  convert ll.congr' (Eventually.of_forall fun e => (g e).offset_formula.symm) using 2
  ring

/-- The same lift tends to 2π/3 at the opposite endpoint. -/
theorem far_phase_offset : Tendsto (fun e => (pointsAt (farParam e)).phaseOffset)
    (𝓝[>] (0:ℝ)) (𝓝 (2*Real.pi/3)) := by
  let c : ℝ := (1/4:ℝ)^((3:ℝ)⁻¹)
  have cp : 0<c := Real.rpow_pos_of_pos (by norm_num) _
  have cc : c^3=1/4 := Real.rpow_inv_natCast_pow (by norm_num) (by decide)
  have cube : 4*c^3=1 := by rw [cc]; norm_num
  let g := fun e => pointsAt (farParam e)
  let w := (c:ℂ)*Branch.omega3
  have l : Tendsto (fun e : ℝ => e) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have EC : Tendsto (fun e : ℝ => (e:ℂ)) (𝓝[>] 0) (𝓝 0) := by simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto _).comp l
  obtain ⟨U,R,theta,_⟩ := far_geometry cp cube
  have positive : ∀ᶠ e in 𝓝[>] (0:ℝ), 0<e := self_mem_nhdsWithin
  have pos : ∀ᶠ e in 𝓝[>] (0:ℝ), 0<e^2 := positive.mono fun _ h => pow_pos h 2
  have Angle : Tendsto (fun e => (g e).u.arg) (𝓝[>] 0) (𝓝 (2*Real.pi/3)) := by
    have v := (tendsto_const_nhds (x:=2*Real.pi/3)).sub (theta.mul l)
    simp only [mul_zero,sub_zero] at v
    apply v.congr'
    exact positive.mono fun e h => by simp [g,(ne_of_gt (show 0<e from h))]
  have V : Tendsto (fun e => (g e).u) (𝓝[>] 0) (𝓝 0) := by
    have v := U.mul (EC.pow 2)
    simp only [zero_pow (by decide : 2≠0),mul_zero] at v
    apply v.congr'
    exact positive.mono fun e h => by simp [g,(ne_of_gt (show 0<e from h))]
  have P : Tendsto (fun e => (farParam e).val⁻¹/e^2) (𝓝[>] 0) (𝓝 0) := by
    apply l.congr'
    filter_upwards [self_mem_nhdsWithin,l.eventually_lt_const zero_lt_one] with e he h1
    rw [farParam_val ⟨he,h1⟩,inv_pow,inv_inv]
    field_simp [ne_of_gt (show 0<e from he)]; ring
  have A (f : ℝ → ℝ) {a : ℝ} (F : Tendsto (fun e => f e/e^2) (𝓝[>] (0:ℝ)) (𝓝 a))
      (cs : (a:ℂ)-w∈slitPlane) : Tendsto (fun e => ((f e:ℂ)-(g e).u).arg) (𝓝[>] 0) (𝓝 ((a:ℂ)-w).arg) := by
    apply scale_arg (v:=fun e : ℝ => e^2) pos _ cs
    apply (((Complex.continuous_ofReal.tendsto _).comp F).sub U).congr'
    filter_upwards with e
    dsimp [g]; push_cast; ring
  obtain ⟨cut1,cut2⟩ := lower_slit cp
  obtain ⟨negw,dw⟩ := arg_const cp
  have r := A _ R cut2
  have p := A _ P (by simpa [w] using cut1)
  simp only [Complex.ofReal_zero,zero_sub,w,negw,dw] at r p
  have UV : Tendsto (fun e => (g e).u/((g e).R:ℂ)) (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' _ (by simpa using V.norm)
    filter_upwards with e
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg (g e).Rpos.le]
    exact div_le_self (norm_nonneg _) (g e).large.1.le
  have vv := (tendsto_const_nhds (x:=(1:ℂ))).sub UV
  simp only [sub_zero] at vv
  have Z := (Complex.continuousAt_arg (show (1:ℂ)∈slitPlane by simp)).tendsto.comp vv
  rw [Complex.arg_one] at Z
  have large : Tendsto (fun e => (((g e).R:ℂ)-(g e).u).arg) (𝓝[>] 0) (𝓝 0) := Z.congr' (Eventually.of_forall fun e => arg_real_factor _ (g e).Rpos)
  have ll := (((tendsto_const_nhds (x:=Real.pi)).add (((r.add large).add (Angle.sub (tendsto_const_nhds (x:=Real.pi/2)))).div_const 2)).sub Angle).sub p
  convert ll.congr' (Eventually.of_forall fun e => (g e).offset_formula.symm) using 2
  ring

/-- Small-end phase matching at every fixed scaled radius M. -/
theorem small_phase_match {ι : Type*} {l : Filter ι} {N : ι → ℕ} {e : ι → ℝ} {M c : ℝ}
    (hc : 0<c) (cube : c^3=4) (endpt : Tendsto e l (𝓝[>] 0))
    (scale : Tendsto (fun i => (N i:ℝ)*e i) l (𝓝 M)) :
    Tendsto (fun i => phase (nearParam (e i)) (N i)) l (𝓝 (M*(c*Real.sqrt 3/2)-5*Real.pi/6)) := by
  have h := (small_upper hc cube).2.2.1.comp endpt
  have L := (scale.mul h).sub (small_phase_offset.comp endpt)
  rw [Complex.im_ofReal_mul,Branch.omega_im,←mul_div_assoc] at L
  apply L.congr'
  filter_upwards [endpt.eventually self_mem_nhdsWithin] with i ep
  have en := (ne_of_gt (show 0<e i from ep))
  dsimp [Function.comp_def,phase]
  field_simp; ring

/-- Far-end phase matching relative to N(2π/3), along any fixed scaled
radius and in particular along each degree residue class. -/
theorem far_phase_match {ι : Type*} {l : Filter ι} {N : ι → ℕ} {e : ι → ℝ} {M c : ℝ}
    (hc : 0<c) (cube : 4*c^3=1) (endpt : Tendsto e l (𝓝[>] 0))
    (scale : Tendsto (fun i => (N i:ℝ)*e i) l (𝓝 M)) :
    Tendsto (fun i => phase (farParam (e i)) (N i)-(N i:ℝ)*(2*Real.pi/3)) l
      (𝓝 (-(M*(Real.sqrt 3/(4*c)))-2*Real.pi/3)) := by
  have h := (far_geometry hc cube).2.2.1.comp endpt
  have L := (scale.mul h).neg.sub (far_phase_offset.comp endpt)
  apply L.congr'
  filter_upwards [endpt.eventually self_mem_nhdsWithin] with i ep
  have en := (ne_of_gt (show 0<e i from ep))
  dsimp [Function.comp_def,phase]
  field_simp; ring

/-- The edge scale over an entire sign interval is bounded below by its
small scale on the left and its reciprocal scale on the right. -/
theorem interval_scale {a p b : Param} (hap : a.val≤p.val) (hpb : p.val≤b.val) :
    min (smallScale a) (farScale b)≤edgeScale p := by
  have h : 0≤((3:ℝ)⁻¹) := by positivity
  have n := Real.rpow_le_rpow (sub_nonneg.mpr a.property.le) (sub_le_sub_right hap 1) h
  have f := Real.rpow_le_rpow (inv_pos.mpr (zero_lt_one.trans b.property)).le
    (inv_anti₀ (zero_lt_one.trans p.property) hpb) h
  exact min_le_min n f

end BigDescents132.Slit
