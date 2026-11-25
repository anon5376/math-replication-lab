import BigDescents132.SlitBranch

namespace BigDescents132.Slit
open Complex Filter Set
open scoped ComplexConjugate Topology

/-- Continuous extensions of the principal square root from the upper and
lower half-planes. They agree at nonnegative real inputs. -/
noncomputable def halfRoot (upper : Bool) (z : ℂ) : ℂ :=
  ⟨Real.sqrt ((‖z‖+z.re)/2),if upper then Real.sqrt ((‖z‖-z.re)/2)
    else -Real.sqrt ((‖z‖-z.re)/2)⟩

theorem halfRoot_continuous (b : Bool) : Continuous (halfRoot b) := by
  have e : halfRoot b=fun z => ((halfRoot b z).re:ℂ) + ((halfRoot b z).im:ℂ)*I :=
    funext fun z => (Complex.re_add_im _).symm
  rw [e]
  cases b <;> unfold halfRoot <;> simp only [Bool.false_eq_true,if_false,if_true] <;> fun_prop

theorem halfRoot_upper {z : ℂ} (h : 0≤z.im) : halfRoot true z=z^(2⁻¹:ℂ) :=
  Complex.ext (Complex.cpow_inv_two_re _).symm (Complex.cpow_inv_two_im_eq_sqrt h).symm

theorem halfRoot_lower {z : ℂ} (h : z.im<0) : halfRoot false z=z^(2⁻¹:ℂ) :=
  Complex.ext (Complex.cpow_inv_two_re _).symm (Complex.cpow_inv_two_im_eq_neg_sqrt h).symm

theorem halfRoot_neg (b : Bool) {v : ℝ} (hv : 0≤v) :
    halfRoot b (-(v:ℂ)) = (if b then I else -I)*(Real.sqrt v:ℂ) := by
  cases b <;> apply Complex.ext <;> simp [halfRoot,Real.norm_of_nonneg hv]

/-- The counterclockwise and clockwise sides of an oriented ray, respectively. -/
def leftSide (a : ℂ) := {z : ℂ | 0<(z/a).im}
def rightSide (a : ℂ) := {z : ℂ | (z/a).im<0}

theorem radical_lips {a : ℂ} (ha : a≠0) {v : ℝ} (hv : 0≤v) :
    Tendsto (radical a) (𝓝[leftSide a] (a*(1+(v:ℂ)))) (𝓝 (-I*(Real.sqrt v:ℂ))) ∧
    Tendsto (radical a) (𝓝[rightSide a] (a*(1+(v:ℂ)))) (𝓝 (I*(Real.sqrt v:ℂ))) := by
  have e : argFactor a (a*(1+(v:ℂ)))= -(v:ℂ) := by
    unfold argFactor; field_simp
  have lim (side : Set ℂ) (b : Bool) := (((halfRoot_continuous b).comp
    (show Continuous (argFactor a) by unfold argFactor; fun_prop)).continuousAt
      (x:=a*(1+(v:ℂ)))).continuousWithinAt (s:=side)
  constructor
  · have h := (lim (leftSide a) false).tendsto
    simp only [Function.comp_apply,e,halfRoot_neg false hv,Bool.false_eq_true,if_false] at h
    apply h.congr' (eventually_of_mem self_mem_nhdsWithin fun x hx => ?_)
    exact halfRoot_lower (by simpa [argFactor,leftSide] using hx)
  · have h := (lim (rightSide a) true).tendsto
    simp only [Function.comp_apply,e,halfRoot_neg true hv,if_true] at h
    apply h.congr' (eventually_of_mem self_mem_nhdsWithin fun x hx => ?_)
    exact halfRoot_upper (by simpa [argFactor,rightSide] using (le_of_lt hx : (x/a).im≤0))

/-- A cut avoids every point that is not a real multiple at least one of its
starting point. This includes its antipodal ray. -/
theorem factor_mem_iff {a z : ℂ} (ha : a≠0) :
    argFactor a z∈slitPlane ↔ ∀ t : ℝ, 1≤t → z≠(t:ℂ)*a := by
  rw [mem_slitPlane_iff]
  constructor
  · rintro h t ht rfl
    rw [argFactor,mul_div_cancel_right₀ _ ha] at h
    simp at h
    linarith
  · intro h
    by_contra! hn
    have hi : (z/a).im=0 := by simpa [argFactor] using hn.2
    have hr : 1≤(z/a).re := by simpa [argFactor] using hn.1
    apply h _ hr
    apply (div_eq_iff ha).mp
    exact Complex.ext rfl (by simpa using hi)

variable {s : ℝ} (g : Points s)

noncomputable def atRootBranch (s : ℝ) (z W : ℂ) :=
  (Branch.linearFactor (s:ℂ) z-W)/(2*Branch.quadraticFactor (s:ℂ) z)

private theorem lip_of_product {z W : ℂ} {S : Set ℂ}
    (hn : Branch.quadraticFactor (s:ℂ) z≠0) (hW : Tendsto g.product (𝓝[S] z) (𝓝 W)) :
    Tendsto g.branch (𝓝[S] z) (𝓝 (atRootBranch s z W)) := by
  have hN : Continuous (Branch.quadraticFactor (s:ℂ)) := by unfold Branch.quadraticFactor; fun_prop
  have hD : Continuous (Branch.linearFactor (s:ℂ)) := by unfold Branch.linearFactor; fun_prop
  have hd := (hD.continuousAt.continuousWithinAt (s:=S) (x:=z)).tendsto
  have hq := (hN.continuousAt.continuousWithinAt (s:=S) (x:=z)).tendsto
  apply ((hd.sub hW).div ((tendsto_const_nhds (x:=(2:ℂ))).mul hq)
    (mul_ne_zero (by norm_num) hn)).congr'
  filter_upwards [hq.eventually_ne hn] with x hx
  exact (g.unreduced hx).symm

/-- Counterclockwise minus clockwise. With this order the small counterclockwise
circle equals the outer circle plus the integrals of the jumps outwards. -/
def HasJump (f : ℂ → ℂ) (a z jump : ℂ) : Prop := ∃ L R : ℂ,
  Tendsto f (𝓝[leftSide a] z) (𝓝 L) ∧ Tendsto f (𝓝[rightSide a] z) (𝓝 R) ∧ L-R=jump

private theorem single_jump {a : ℂ} (ha : a≠0) {v : ℝ} (hv : 0≤v) (A : ℂ → ℂ)
    (prod : ∀ x, g.product x=radical a x*A x)
    (reg : ContinuousAt A (a*(1+(v:ℂ))))
    (hn : Branch.quadraticFactor (s:ℂ) (a*(1+(v:ℂ)))≠0) :
    HasJump g.branch a (a*(1+(v:ℂ))) (I*(Real.sqrt v:ℂ)*A (a*(1+(v:ℂ)))/
      Branch.quadraticFactor (s:ℂ) (a*(1+(v:ℂ)))) := by
  let z := a*(1+(v:ℂ))
  obtain ⟨hl,hr⟩ := radical_lips ha hv
  have eq : g.product = fun x => radical a x*A x := funext prod
  refine ⟨_,_,lip_of_product g hn (eq ▸ hl.mul reg.continuousWithinAt.tendsto),
    lip_of_product g hn (eq ▸ hr.mul reg.continuousWithinAt.tendsto),?_⟩
  unfold atRootBranch
  field_simp
  ring

include g in
private theorem num_ne_nonreal {z : ℂ} (hz : z.im≠0) :
    Branch.quadraticFactor (s:ℂ) z≠0 := by
  have sc1 : (1:ℂ)-(s:ℂ)≠0 := by exact_mod_cast sub_ne_zero.mpr g.parameter.ne
  have sc : s≠0 := (zero_lt_one.trans g.parameter).ne'
  have z0 : z≠0 := by rintro rfl; exact hz rfl
  refine mul_ne_zero (mul_ne_zero sc1 (pow_ne_zero 2 z0)) ?_
  intro h
  have e := congrArg im h
  simp [Complex.mul_im,sc,hz] at e

theorem ray_arguments {a : ℂ} (him : a.im≠0) {v : ℝ} (hv : 0≤v) :
    argFactor g.r (a*(1+(v:ℂ)))∈slitPlane ∧ argFactor g.R (a*(1+(v:ℂ)))∈slitPlane ∧
    argFactor (conj a) (a*(1+(v:ℂ)))∈slitPlane := by
  have hapos : 0<1+v := by linarith
  have ai : (a*(1+(v:ℂ))).im=a.im*(1+v) := by simp [Complex.mul_im]
  have hnon : (a*(1+(v:ℂ))).im≠0 := ai ▸ mul_ne_zero him hapos.ne'
  have realmem (c : ℝ) (hc : 0<c) : argFactor c (a*(1+(v:ℂ)))∈slitPlane := by
    apply (factor_mem_iff (ofReal_ne_zero.mpr hc.ne')).mpr
    intro t ht e
    exact hnon (by rw [e]; simp)
  have ca : conj a≠0 := by intro e; have h := congrArg im e; simp [him] at h
  have other : argFactor (conj a) (a*(1+(v:ℂ)))∈slitPlane := by
    apply (factor_mem_iff ca).mpr
    intro t ht e
    have h := congrArg im e
    rw [ai] at h
    simp [Complex.mul_im] at h
    have H : a.im*(1+v+t)=0 := by linarith
    exact (mul_ne_zero him (by linarith)) H
  exact ⟨realmem g.r g.rpos,realmem g.R g.Rpos,other⟩

private theorem ray_continuous {a : ℂ} (him : a.im≠0) {v : ℝ} (hv : 0≤v) :
    ContinuousAt (fun x => radical g.r x*radical g.R x*radical (conj a) x) (a*(1+(v:ℂ))) := by
  obtain ⟨h1,h2,h3⟩ := ray_arguments g him hv
  exact (((radical_diff h1).continuousAt.mul (radical_diff h2).continuousAt).mul (radical_diff h3).continuousAt)

noncomputable def Points.rayOther (a z : ℂ) :=
  radical g.r z*radical g.R z*radical (conj a) z

/-- The jump formula for each of the two actual complex rays. -/
theorem Points.complex_jump {a : ℂ} (ha : a=g.u ∨ a=conj g.u) {v : ℝ} (hv : 0≤v) :
    let z := a*(1+(v:ℂ))
    HasJump g.branch a z (I*(Real.sqrt v:ℂ)*g.rayOther a z/Branch.quadraticFactor (s:ℂ) z) := by
  have him : a.im≠0 := by rcases ha with rfl|rfl <;> simp [g.upper.ne']
  have an : a≠0 := by intro h; simp [h] at him
  apply single_jump g an hv _ _ (ray_continuous g him hv)
  · apply num_ne_nonreal g
    simp [Complex.mul_im,him,show (1+v:ℝ)≠0 by linarith]
  · intro z
    rcases ha with rfl|rfl <;> simp [Points.product,Points.rayOther] <;> ring

theorem leftSide_real {r : ℝ} (hr : 0<r) : leftSide (r:ℂ)={z : ℂ | 0<z.im} := by
  ext z
  simp [leftSide,Complex.div_im,hr,Real.sq_sqrt hr.le]

theorem rightSide_real {r : ℝ} (hr : 0<r) : rightSide (r:ℂ)={z : ℂ | z.im<0} := by
  ext z
  simp [rightSide,Complex.div_im,hr]
  rw [div_lt_iff₀ (mul_pos hr hr),zero_mul]
  constructor
  · intro h; by_contra! hn; exact (not_lt_of_ge (mul_nonneg hn hr.le)) h
  · exact fun h => mul_neg_of_neg_of_pos h hr

theorem real_factor_mem {a x : ℝ} (ha : 0<a) (hx : x<a) : argFactor a x∈slitPlane := by
  apply mem_slitPlane_iff.mpr (Or.inl ?_)
  simpa [argFactor,←ofReal_div] using sub_pos.mpr ((div_lt_one ha).mpr hx)

theorem Points.real_mem {x : ℝ} (hx : x<g.r) : (x:ℂ)∈g.domain := by
  by_cases h : x=0
  · simp [h]
  exact ⟨real_factor_mem g.rpos hx,real_factor_mem g.Rpos (hx.trans (g.small.2.trans g.large.1)),
    nonreal_factor_mem g.upper.ne' h,nonreal_factor_mem (by simpa using g.upper.ne') h⟩

theorem Points.pole_value :
    g.branch ((1/s:ℝ):ℂ)=((s/(s-1):ℝ):ℂ) := by
  let p := ((1/s:ℝ):ℂ)
  have sp : 0<s := zero_lt_one.trans g.parameter
  have hW := g.product_real_pos (one_div_pos.mpr sp) g.small.1
  change 2/(Branch.linearFactor (s:ℂ) p+g.product p)=_
  rw [←Complex.sq_cpow_two_inv hW.1, g.product_sq]
  exact Branch.regular_at_pole g.parameter

private theorem real_num_ne {x : ℝ} (hx : g.r≤x) : Branch.quadraticFactor (s:ℂ) x≠0 := by
  have hs := zero_lt_one.trans g.parameter
  have sc1 : (1:ℂ)-(s:ℂ)≠0 := by exact_mod_cast sub_ne_zero.mpr g.parameter.ne
  have xx : (x:ℂ)≠0 := ofReal_ne_zero.mpr (g.rpos.trans_le hx).ne'
  refine mul_ne_zero (mul_ne_zero sc1 (pow_ne_zero 2 xx)) ?_
  have ell : 1<x*s := (div_lt_iff₀ hs).mp (g.small.1.trans_le hx)
  exact_mod_cast (show 1-s*x≠0 by linarith [mul_comm s x])

noncomputable def Points.realOther (z : ℂ) :=
  radical g.R z*radical g.u z*radical (conj g.u) z

/-- On the finite positive cut only the first real factor changes sign. -/
theorem Points.real_jump {v : ℝ} (hv : 0≤v) (hx : g.r*(1+v)<g.R) :
    let z := (g.r:ℂ)*(1+(v:ℂ))
    HasJump g.branch g.r z (I*(Real.sqrt v:ℂ)*g.realOther z/Branch.quadraticFactor (s:ℂ) z) := by
  let x := g.r*(1+v)
  have xx : g.r≤x := le_mul_of_one_le_right g.rpos.le (by linarith)
  have xp := g.rpos.trans_le xx
  have e : ((x:ℝ):ℂ)=(g.r:ℂ)*(1+(v:ℂ)) := by dsimp [x]; push_cast; rfl
  apply single_jump g (ofReal_ne_zero.mpr g.rpos.ne') hv
  · intro w; unfold Points.product Points.realOther; ring
  · rw [←e]
    exact (((radical_diff (real_factor_mem g.Rpos hx)).continuousAt.mul
      (radical_diff (nonreal_factor_mem g.upper.ne' xp.ne')).continuousAt).mul
        (radical_diff (nonreal_factor_mem (a:=conj g.u) (by simpa using g.upper.ne') xp.ne')).continuousAt)
  · rw [←e]; exact real_num_ne g xx

/-- Beyond the larger positive root both real factors change sign. Their
product has equal limits from the two sides, including at the endpoint. -/
theorem Points.real_no_jump_after {x : ℝ} (hx : g.R≤x) : HasJump g.branch g.r x 0 := by
  have hxr := (g.small.2.trans g.large.1).le.trans hx
  have hpos := g.Rpos.trans_le hx
  have lips (c : ℝ) (hc : 0<c) (hcx : c≤x) := radical_lips (ofReal_ne_zero.mpr hc.ne')
    (show 0≤x/c-1 by rw [sub_nonneg,le_div_iff₀ hc,one_mul]; exact hcx)
  have get (c : ℝ) (hc : 0<c) (hcx : c≤x) :
      Tendsto (radical c) (𝓝[leftSide g.r] (x:ℂ)) (𝓝 (-I*(Real.sqrt (x/c-1):ℂ))) ∧
      Tendsto (radical c) (𝓝[rightSide g.r] (x:ℂ)) (𝓝 (I*(Real.sqrt (x/c-1):ℂ))) := by
    have e : (c:ℂ)*(1+((x/c-1:ℝ):ℂ))=(x:ℂ) := by push_cast; field_simp [ofReal_ne_zero.mpr hc.ne']
    simpa only [e,leftSide_real hc,rightSide_real hc,leftSide_real g.rpos,rightSide_real g.rpos] using lips c hc hcx
  obtain ⟨rl,rr⟩ := get g.r g.rpos hxr
  obtain ⟨Rl,Rr⟩ := get g.R g.Rpos hx
  have up := (radical_diff (nonreal_factor_mem g.upper.ne' hpos.ne')).continuousAt
  have dn := (radical_diff (nonreal_factor_mem (a:=conj g.u) (by simpa using g.upper.ne') hpos.ne')).continuousAt
  have hn := real_num_ne g hxr
  refine ⟨_,_,lip_of_product g hn (((rl.mul Rl).mul up.continuousWithinAt.tendsto).mul dn.continuousWithinAt.tendsto),
    lip_of_product g hn (((rr.mul Rr).mul up.continuousWithinAt.tendsto).mul dn.continuousWithinAt.tendsto),?_⟩
  simp [atRootBranch]

/-- The apparent pole and the part of the positive axis before the first
real root have equal traces. -/
theorem Points.real_no_jump_before {x : ℝ} (hx : x<g.r) : HasJump g.branch g.r x 0 :=
  ⟨_,_,(g.branch_diff (g.real_mem hx)).continuousAt.continuousWithinAt.tendsto,
    (g.branch_diff (g.real_mem hx)).continuousAt.continuousWithinAt.tendsto,sub_self _⟩

end BigDescents132.Slit
