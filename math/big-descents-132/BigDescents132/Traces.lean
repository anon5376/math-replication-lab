import BigDescents132.Angles

namespace BigDescents132.Slit
open Complex Filter Set MeasureTheory
open scoped ComplexConjugate Topology

variable {s : ℝ} (g : Points s)

theorem Points.dominant : ‖g.u‖<g.r := by
  have hr : (radicand s).IsRoot g.r := by
    have e := g.factor (g.r:ℂ)
    rw [div_self (ofReal_ne_zero.mpr g.rpos.ne'),sub_self,zero_mul,zero_mul,zero_mul] at e
    change (radicand s).eval g.r=0
    apply Complex.ofReal_eq_zero.mp
    simpa [radicand] using e
  apply Branch.dominant_pair g.parameter g.small hr _ g.upper.ne'
  change (radicand _).eval _=_
  simp [g.factor,g.u_ne]

theorem Points.inner_domain {z : ℂ} (hz : ‖z‖<‖g.u‖) : z∈g.domain := by
  have safe (a : ℂ) (ha : ‖z‖<‖a‖) : argFactor a z∈slitPlane := by
    apply mem_slitPlane_iff.mpr (Or.inl ?_)
    have an : 0<‖a‖ := (norm_nonneg z).trans_lt ha
    have e : (z/a).re<1 := (Complex.re_le_norm _).trans_lt (by rw [norm_div]; exact (div_lt_one an).mpr ha)
    simpa [argFactor] using e
  exact ⟨safe _ (by simpa [Real.norm_of_nonneg g.rpos.le] using hz.trans g.dominant),
    safe _ (by simpa [Real.norm_of_nonneg g.Rpos.le] using ((hz.trans g.dominant).trans (g.small.2.trans g.large.1))),
    safe _ hz,safe _ (by simpa using hz)⟩

/-- Radius exp(x) on the ray of a. -/
noncomputable def radial (a : ℂ) (x : ℝ) := a*((Real.exp x/‖a‖:ℝ):ℂ)
noncomputable def excess (a : ℂ) (x : ℝ) := Real.exp x/‖a‖-1

theorem radial_norm {a : ℂ} (ha : a≠0) (x : ℝ) : ‖radial a x‖=Real.exp x := by
  rw [radial,norm_mul,Complex.norm_real,Real.norm_of_nonneg (div_nonneg (Real.exp_pos _).le (norm_nonneg _))]
  field_simp [norm_ne_zero_iff.mpr ha]

theorem radial_excess (a : ℂ) (x : ℝ) : radial a x=a*(1+(excess a x:ℂ)) := by
  simp [radial,excess]

theorem radial_on {a : ℂ} {c φ : ℝ} (hc : 0<c) (ha : a=(c:ℂ)*direction φ) (x : ℝ) :
    polarPoint x φ=radial a x := by
  rw [polar_eq,radial,ha,norm_mul,norm_direction,mul_one,Complex.norm_real,Real.norm_of_nonneg hc.le]
  push_cast; field_simp [ofReal_ne_zero.mpr hc.ne']; ring

noncomputable def Points.complexJump (a : ℂ) (x : ℝ) :=
  if 0≤excess a x then I*(Real.sqrt (excess a x):ℂ)*g.rayOther a (radial a x)/
    Branch.quadraticFactor (s:ℂ) (radial a x) else 0

noncomputable def Points.realJump (x : ℝ) :=
  if g.r≤Real.exp x ∧ Real.exp x<g.R then
    I*(Real.sqrt (excess g.r x):ℂ)*g.realOther (Real.exp x)/Branch.quadraticFactor (s:ℂ) (Real.exp x)
  else 0

theorem Points.all_complex_jumps {a : ℂ} (ha : a=g.u ∨ a=conj g.u) (x : ℝ) :
    HasJump g.branch a (radial a x) (g.complexJump a x) := by
  rw [Points.complexJump]
  split_ifs with hv
  · rw [radial_excess]
    exact g.complex_jump ha hv
  · have an : ‖a‖=‖g.u‖ := by rcases ha with rfl|rfl <;> simp
    have ne : a≠0 := norm_pos_iff.mp (an ▸ norm_pos_iff.mpr g.u_ne)
    have h : Real.exp x<‖a‖ := (div_lt_one (norm_pos_iff.mpr ne)).mp (by dsimp [excess] at hv; linarith)
    have D := (g.branch_diff (g.inner_domain (by rw [radial_norm ne,←an]; exact h))).continuousAt
    exact ⟨_,_,D.continuousWithinAt.tendsto,D.continuousWithinAt.tendsto,sub_self _⟩

theorem Points.all_real_jumps (x : ℝ) : HasJump g.branch g.r (radial g.r x) (g.realJump x) := by
  have e : radial g.r x=(Real.exp x:ℂ) := by
    simpa [polar_eq] using (radial_on (φ:=0) g.rpos (by simp : (g.r:ℂ)=g.r*direction 0) x).symm
  rw [Points.realJump]
  split_ifs with h
  · have v : 0≤excess g.r x := by
      rw [excess,Complex.norm_real,Real.norm_of_nonneg g.rpos.le,sub_nonneg,le_div_iff₀ g.rpos,one_mul]
      exact h.1
    have xx : g.r*(1+excess g.r x)=Real.exp x := by
      simp [excess,Real.norm_of_nonneg g.rpos.le]
      field_simp [g.rpos.ne']
    have xxc : (g.r:ℂ)*(1+(excess g.r x:ℂ))=(Real.exp x:ℂ) := by exact_mod_cast xx
    rw [e]
    simpa only [xxc] using g.real_jump v (xx ▸ h.2)
  · rw [e]
    rcases lt_or_ge (Real.exp x) g.r with hlt|hle
    · exact g.real_no_jump_before hlt
    · exact g.real_no_jump_after (le_of_not_gt (fun hn => h ⟨hle,hn⟩))

/-- The log-coordinate boundary values of a function along a fixed ray. -/
structure Axis (f : ℂ → ℂ) (a : ℂ) (J : ℝ → ℂ) where
  left : ℝ → ℂ
  right : ℝ → ℂ
  left_limit : ∀ x, Tendsto f (𝓝[leftSide a] (radial a x)) (𝓝 (left x))
  right_limit : ∀ x, Tendsto f (𝓝[rightSide a] (radial a x)) (𝓝 (right x))
  jump : ∀ x, left x-right x=J x

theorem axis_exists {f : ℂ → ℂ} {a : ℂ} {J : ℝ → ℂ}
    (h : ∀ x, HasJump f a (radial a x) (J x)) : Nonempty (Axis f a J) := by
  choose L R hl hr hj using h
  exact ⟨⟨L,R,hl,hr,hj⟩⟩

noncomputable def lifted (f : ℂ → ℂ) (n : ℕ) (z : ℂ) := (Complex.exp z)⁻¹^n*f (Complex.exp z)

noncomputable def weighted (n : ℕ) (a : ℂ) (v : ℝ → ℂ) (x : ℝ) := (radial a x)⁻¹^n*v x

/-- Pull the two one-sided boundary values back through exp. -/
noncomputable def sectorTraces {a b : ℂ} {l h c d : ℝ} {JL JH : ℝ → ℂ} (lh : l<h)
    (ac : 0<c) (bd : 0<d) (al : a=(c:ℂ)*direction l) (bh : b=(d:ℂ)*direction h)
    (L : Axis g.branch a JL) (H : Axis g.branch b JH) (n : ℕ)
    (inside : ∀ z∈strip l h, Complex.exp z∈g.domain) :
    StripTraces (lifted g.branch n) l h where
  ordered := lh
  lower := weighted n a L.left
  upper := weighted n b H.right
  hol z hz := ((Complex.differentiableAt_exp.inv (Complex.exp_ne_zero _)).pow n).mul
    ((g.branch_diff (inside z hz)).comp z Complex.differentiableAt_exp)
  low x := by
    have v := exp_left (l:=l) (h:=h) ac x
    rw [←al,radial_on ac al] at v
    have E := (L.left_limit x).comp v
    exact ((v.mono_right nhdsWithin_le_nhds).inv₀ (by rw [←radial_on ac al]; exact Complex.exp_ne_zero _) |>.pow n).mul E
  high x := by
    have v := exp_right (l:=l) (h:=h) bd x
    rw [←bh,radial_on bd bh] at v
    have E := (H.right_limit x).comp v
    exact ((v.mono_right nhdsWithin_le_nhds).inv₀ (by rw [←radial_on bd bh]; exact Complex.exp_ne_zero _) |>.pow n).mul E

end BigDescents132.Slit
