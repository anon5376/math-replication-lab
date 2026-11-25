import BigDescents132.AmplitudeBound

namespace BigDescents132.Slit
open Complex Filter Set
open scoped Topology ComplexConjugate

/-- The actual far-end error is uniformly O(1/(N ε)) for small ε>0 and
N ε ≥ 7, with s=ε⁻³. -/
theorem far_moving :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ e in 𝓝[>] (0:ℝ), ∀ n : ℕ, 8≤n+1 → 7≤((n+1:ℕ):ℝ)*e →
      coefficientError (farParam e) n ≤ C/(((n+1:ℕ):ℝ)*e) := by
  let c : ℝ := (1/4:ℝ)^((3:ℝ)⁻¹)
  have cp : 0<c := Real.rpow_pos_of_pos (by norm_num) _
  have cc : c^3=1/4 := Real.rpow_inv_natCast_pow (by norm_num) (by decide)
  have cube : 4*c^3=1 := by rw [cc]; norm_num
  let g := fun e => pointsAt (farParam e)
  let w := (c:ℂ)*Branch.omega3
  have wi : 0<w.im := upperRoot c cp
  have wn : 0<‖w‖ := norm_pos_iff.mpr (by intro t; rw [t] at wi; simp at wi)
  have E : Tendsto (fun e : ℝ => e) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have EC : Tendsto (fun e : ℝ => (e:ℂ)) (𝓝[>] 0) (𝓝 0) := by simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto _).comp E
  obtain ⟨U,R,_,G⟩ := far_geometry cp cube
  let V := fun e : ℝ => (g e).u/(e:ℂ)^2
  let q := fun e : ℝ => (g e).r/e^2
  have tv : Tendsto V (𝓝[>] 0) (𝓝 w) := U
  have tq : Tendsto q (𝓝[>] 0) (𝓝 c) := R
  have ti := (Complex.continuous_im.tendsto _).comp tv
  have tn := tv.norm
  have tc : Tendsto (fun e => (q e:ℂ)) (𝓝[>] 0) (𝓝 (c:ℂ)) := (Complex.continuous_ofReal.tendsto _).comp tq
  have te := (EC.sub tv).norm
  have td := (tc.sub tv).norm
  have tlim : ∀ᶠ e in 𝓝[>] (0:ℝ), e∈Ioo 0 1 := by
    filter_upwards [self_mem_nhdsWithin,E.eventually_lt_const zero_lt_one] with e ep e1
    exact ⟨ep,e1⟩
  have eqs (e : ℝ) (he : e∈Ioo 0 1) :
      (g e).slope=‖V e‖/(V e).im ∧
      (g e).poleBound=‖(e:ℂ)-V e‖/(V e).im ∧
      (g e).farPole=‖(e:ℂ)-V e‖/(q e-e) ∧
      (g e).amplitudeBound=(q e/‖V e‖)*(‖(q e:ℂ)-V e‖/(8*(V e).im)) := by
    have ep := he.1
    have e0 := ep.ne'
    have eC := Complex.ofReal_ne_zero.mpr e0
    have h2 := pow_pos ep 2
    have vi : (V e).im=(g e).u.im/e^2 := by
      dsimp [V]; rw [←Complex.ofReal_pow,div_eq_inv_mul,←Complex.ofReal_inv,Complex.im_ofReal_mul,div_eq_inv_mul]
    have vn : ‖V e‖=‖(g e).u‖/e^2 := by
      dsimp [V]; rw [norm_div,norm_pow,Complex.norm_real,Real.norm_of_nonneg ep.le]
    have pd : ‖(e:ℂ)-V e‖=e*‖1-((farParam e).val:ℂ)*(g e).u‖ := by
      have alg (z : ℂ) : (e:ℂ)-z/(e:ℂ)^2=(e:ℂ)*(1-((farParam e).val:ℂ)*z) := by
        rw [farParam_val he]; push_cast; field_simp; ring
      dsimp [V]; rw [alg,norm_mul,Complex.norm_real,Real.norm_of_nonneg ep.le]
    have diff : ‖(q e:ℂ)-V e‖=‖((g e).r:ℂ)-(g e).u‖/e^2 := by
      dsimp [q,V]; push_cast
      rw [←sub_div,norm_div,norm_pow,Complex.norm_real,Real.norm_of_nonneg ep.le]
    have i0 := (g e).upper.ne'
    have u0 := norm_ne_zero_iff.mpr (g e).u_ne
    have sid' : (farParam e).val*e^3=1 := by rw [farParam_val he]; field_simp
    have qp : e<q e := by
      apply (lt_div_iff₀ h2).mpr
      have sr := (g e).sr_gt
      change 1<(farParam e).val*(g e).r at sr
      calc
        e*e^2 = e^3 := by ring
        _ = 1*e^3 := by ring
        _ < ((farParam e).val*(g e).r)*e^3 := mul_lt_mul_of_pos_right sr (pow_pos ep 3)
        _ = (g e).r := by calc
          _ = ((farParam e).val*e^3)*(g e).r := by ring
          _ = _ := by rw [sid',one_mul]
    have pre : (farParam e).val≠0 := (zero_lt_one.trans (farParam e).property).ne'
    have den := (sub_pos.mpr (g e).sr_gt).ne'
    have d1 := (sub_pos.mpr qp).ne'
    refine ⟨?_,?_,?_,?_⟩
    · rw [vn,vi]; unfold Points.slope; field_simp
    · rw [pd,vi]; unfold Points.poleBound
      field_simp
      linear_combination -‖1-((farParam e).val:ℂ)*(g e).u‖*(g e).u.im*(sid')
    · rw [pd]; unfold Points.farPole
      apply (div_eq_div_iff den d1).mpr
      dsimp [q]
      field_simp
      linear_combination -‖1-((farParam e).val:ℂ)*(g e).u‖*(g e).r*sid'
    · rw [diff,vn,vi]; unfold Points.amplitudeBound q; field_simp
  refine moving_from_limits (p:=farParam) (h:=fun _ => 1) false ?_
    (k:=‖w‖/w.im) (a:=‖0-w‖/w.im) (b:=‖0-w‖/(c-0))
    (d:=(c/‖w‖)*(‖(c:ℂ)-w‖/(8*w.im))) (by positivity : 0<3/(4*c)) ?_ ?_ ?_ ?_ G
  · exact tlim.mono fun _ he => ⟨he.2.le,le_rfl,fun h => by contradiction⟩
  · exact (tn.div ti wi.ne').congr' (tlim.mono fun e he => by simpa only [mul_one] using (eqs e he).1.symm)
  · exact (te.div ti wi.ne').congr' (tlim.mono fun e he => (eqs e he).2.1.symm)
  · exact (te.div (tq.sub E) (by simpa using cp.ne')).congr' (tlim.mono fun e he => (eqs e he).2.2.1.symm)
  · exact ((tq.div tn wn.ne').mul (td.div ((tendsto_const_nhds (x:=(8:ℝ))).mul ti)
      (mul_ne_zero (by norm_num) wi.ne'))).congr' (tlim.mono fun e he => (eqs e he).2.2.2.symm)

end BigDescents132.Slit
