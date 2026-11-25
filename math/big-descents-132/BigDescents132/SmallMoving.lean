import BigDescents132.AmplitudeBound

namespace BigDescents132.Slit
open Complex Filter Set
open scoped Topology ComplexConjugate

private theorem norm_rescale (u : ℂ) {e : ℝ} (he : 0<e) : ‖u/(e:ℂ)‖=‖u‖/e := by
  rw [norm_div,Complex.norm_real,Real.norm_of_nonneg he.le]

private theorem im_rescale (u : ℂ) (e : ℝ) : (u/(e:ℂ)).im=u.im/e := by
  rw [div_eq_inv_mul,←Complex.ofReal_inv,Complex.im_ofReal_mul,div_eq_inv_mul]

/-- The actual near-end error is uniformly O(1/(N δ)) for small δ>0 and
N δ ≥ 7, with s=1+δ³. -/
theorem small_moving :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ e in 𝓝[>] (0:ℝ), ∀ n : ℕ, 8≤n+1 → 7≤((n+1:ℕ):ℝ)*e →
      coefficientError (nearParam e) n ≤ C/(((n+1:ℕ):ℝ)*e) := by
  let c : ℝ := 4^((3:ℝ)⁻¹)
  have cp : 0<c := Real.rpow_pos_of_pos (by norm_num) _
  have cube : c^3=4 := Real.rpow_inv_natCast_pow (by norm_num) (by decide)
  let g := fun e => pointsAt (nearParam e)
  let w := (c:ℂ)*Branch.omega3
  have wi : 0<w.im := upperRoot c cp
  have E : Tendsto (fun e : ℝ => e) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  obtain ⟨U,un,_,_⟩ := small_upper cp cube
  have R := small_real.1
  have rn : Tendsto (fun e => (g e).r) (𝓝[>] 0) (𝓝 1) := by
    have l := (R.mul E).add (tendsto_const_nhds (x:=(1:ℝ)))
    simp only [zero_mul,zero_add] at l
    apply l.congr'
    filter_upwards [self_mem_nhdsWithin] with e he
    have e0 := ne_of_gt (show 0<e from he)
    simp [g,e0]
  have RC := (Complex.continuous_ofReal.tendsto _).comp R
  have UI : Tendsto (fun e : ℝ => (g e).u.im/e) (𝓝[>] 0) (𝓝 w.im) := by
    simpa [Function.comp_def,g,w,im_rescale] using (Complex.continuous_im.tendsto _).comp U
  have S : Tendsto (fun e => (nearParam e).val) (𝓝[>] 0) (𝓝 1) := by
    have z := (tendsto_const_nhds (x:=(1:ℝ))).add (E.pow 3)
    simp at z
    apply z.congr'
    filter_upwards [self_mem_nhdsWithin] with e he
    exact (nearParam_val he).symm
  have E2C : Tendsto (fun e : ℝ => (e:ℂ)^2) (𝓝[>] 0) (𝓝 0) := by
    simpa [Function.comp_def] using ((Complex.continuous_ofReal.tendsto _).comp E).pow 2
  have P : Tendsto (fun e : ℝ => ‖1-((nearParam e).val:ℂ)*(g e).u‖/e) (𝓝[>] 0) (𝓝 ‖-w‖) := by
    have t := (U.neg.sub (E2C.mul un)).norm
    simp only [zero_mul,sub_zero] at t
    apply t.congr'
    filter_upwards [self_mem_nhdsWithin] with e he
    have ep : 0<e := he
    have ec := ofReal_ne_zero.mpr ep.ne'
    have alg (z : ℂ) : -((z-1)/(e:ℂ))-(e:ℂ)^2*z=(1-((1+e^3:ℝ):ℂ)*z)/(e:ℂ) := by
      push_cast; field_simp; ring
    rw [←norm_rescale _ ep,alg]
    exact congrArg (fun x : ℝ => ‖(1-(x:ℂ)*(g e).u)/(e:ℂ)‖) (nearParam_val ep).symm
  have D : Tendsto (fun e : ℝ => ‖((g e).r:ℂ)-(g e).u‖/e) (𝓝[>] 0) (𝓝 ‖-w‖) := by
    have t := (RC.sub U).norm
    simp only [Complex.ofReal_zero,zero_sub] at t
    apply t.congr'
    filter_upwards [self_mem_nhdsWithin] with e he
    have ep : 0<e := he
    rw [←norm_rescale _ ep]
    congr 1
    simp [Function.comp_def,g]
    ring
  have sNorm : Tendsto (fun e => ‖(g e).u‖) (𝓝[>] 0) (𝓝 1) := by simpa using un.norm
  refine moving_from_limits (p:=nearParam) (h:=id) true ?_ (k:=1/w.im) (a:=‖-w‖/(1*w.im))
    (b:=‖-w‖/(1*1)) (d:=(1/1)*(‖-w‖/(8*w.im))) (half_pos cp) ?_ ?_ ?_ ?_ (small_gap cp cube)
  · filter_upwards [E.eventually_lt_const zero_lt_one] with e he
    exact ⟨le_rfl,he.le,fun _ => rfl⟩
  · apply (sNorm.div UI wi.ne').congr'
    filter_upwards [self_mem_nhdsWithin] with e he
    change ‖(g e).u‖/((g e).u.im/e)=(g e).slope*e
    simp [Points.slope,div_div_eq_mul_div]; ring
  · have den := S.mul UI
    apply (P.div den (by simpa only [one_mul] using wi.ne')).congr'
    filter_upwards [self_mem_nhdsWithin] with e he
    have h1 := (zero_lt_one.trans (nearParam e).property).ne'
    have h2 := (g e).upper.ne'
    have h3 := ne_of_gt (show 0<e from he)
    change _ = ‖1-((nearParam e).val:ℂ)*(g e).u‖/((nearParam e).val*(g e).u.im)
    field_simp [h1,h2,h3]
  · have den := S.mul rn
    apply (P.div den (by norm_num)).congr'
    filter_upwards [self_mem_nhdsWithin] with e he
    dsimp [Points.nearPole,g]; ring
  · have v := (rn.div sNorm one_ne_zero).mul (D.div ((tendsto_const_nhds (x:=(8:ℝ))).mul UI) (mul_ne_zero (by norm_num) wi.ne'))
    apply v.congr'
    filter_upwards [self_mem_nhdsWithin] with e he
    dsimp [Points.amplitudeBound,g]
    congr 1
    have e0 := ne_of_gt (show 0<e from he)
    field_simp

end BigDescents132.Slit
