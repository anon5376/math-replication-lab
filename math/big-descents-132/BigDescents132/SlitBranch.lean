import BigDescents132.SlitRoots
import BigDescents132.Cauchy

namespace BigDescents132.Slit
open Complex Filter Set
open scoped ComplexConjugate Topology

noncomputable def argFactor (a z : ℂ) := 1-z/a
noncomputable def radical (a z : ℂ) := (argFactor a z)^(2⁻¹:ℂ)

theorem radical_sq (a z : ℂ) : radical a z^2=argFactor a z := by
  unfold radical
  rw [←Complex.cpow_mul_nat]
  norm_num

theorem radical_diff {a z : ℂ} (h : argFactor a z ∈ slitPlane) :
    DifferentiableAt ℂ (radical a) z :=
  (show DifferentiableAt ℂ (argFactor a) z by unfold argFactor; fun_prop).cpow_const h

@[simp] theorem radical_zero (a : ℂ) : radical a 0=1 := by simp [radical,argFactor]

theorem radical_conj {a z : ℂ} (h : argFactor a z∈slitPlane) :
    radical (conj a) (conj z)=conj (radical a z) := by
  have hc : argFactor (conj a) (conj z)=conj (argFactor a z) := by simp [argFactor]
  simpa only [radical,hc,map_inv₀,map_ofNat] using
    Complex.conj_cpow (argFactor a z) (2⁻¹:ℂ) (slitPlane_arg_ne_pi h)

variable {s : ℝ} (g : Points s)

theorem Points.rpos : 0<g.r := (one_div_pos.mpr (zero_lt_one.trans g.parameter)).trans g.small.1
theorem Points.Rpos : 0<g.R := zero_lt_one.trans g.large.1
theorem Points.u_ne : g.u≠0 := by intro h; simpa [h] using g.upper
theorem Points.cu_ne : conj g.u≠0 := by simp [g.u_ne]

def Points.domain : Set ℂ := {z | argFactor g.r z∈slitPlane ∧ argFactor g.R z∈slitPlane ∧
  argFactor g.u z∈slitPlane ∧ argFactor (conj g.u) z∈slitPlane}

theorem Points.domain_open : IsOpen g.domain := by
  have h (a : ℂ) : IsOpen ((argFactor a) ⁻¹' slitPlane) :=
    isOpen_slitPlane.preimage (by unfold argFactor; fun_prop)
  exact (h _).inter ((h _).inter ((h _).inter (h _)))

noncomputable def Points.product (z : ℂ) :=
  radical g.r z*radical g.R z*radical g.u z*radical (conj g.u) z

theorem Points.product_sq (z : ℂ) : g.product z^2=(radicand (s:ℂ)).eval z := by
  simp only [Points.product,mul_pow,radical_sq,argFactor,g.factor]

theorem Points.product_diff {z : ℂ} (hz : z∈g.domain) :
    DifferentiableAt ℂ g.product z :=
  (((radical_diff hz.1).mul (radical_diff hz.2.1)).mul (radical_diff hz.2.2.1)).mul
    (radical_diff hz.2.2.2)

@[simp] theorem Points.product_zero : g.product 0=1 := by simp [Points.product]

@[simp] theorem Points.zero_mem : (0:ℂ)∈g.domain := by
  simp [Points.domain,argFactor,Complex.mem_slitPlane_iff]

theorem Points.germ_product :
    ∀ᶠ z : ℂ in 𝓝 0, ((radicand (s:ℂ)).eval z)^(2⁻¹:ℂ)=g.product z := by
  have h := (Complex.continuous_re.continuousAt.comp (g.product_diff g.zero_mem).continuousAt).tendsto.eventually_const_lt
    (show 0<(g.product 0).re by simp)
  filter_upwards [h] with z hz
  rw [←g.product_sq,Complex.sq_cpow_two_inv hz]

private theorem positive_real_factor {a x : ℝ} (ha : 0<a) (hx : x<a) :
    radical a x = (((1-x/a)^(1/2:ℝ):ℝ):ℂ) := by
  have h : 0<1-x/a := sub_pos.mpr ((div_lt_one ha).mpr hx)
  rw [radical,argFactor,show (1:ℂ)-(x:ℂ)/a=((1-x/a:ℝ):ℂ) by push_cast; rfl]
  simpa using (Complex.ofReal_cpow h.le (1/2:ℝ)).symm

theorem nonreal_factor_mem {a : ℂ} (ha : a.im≠0) {x : ℝ} (hx : x≠0) :
    argFactor a x∈slitPlane := by
  apply mem_slitPlane_iff.mpr (Or.inr ?_)
  have hn : a≠0 := by intro h; simp [h] at ha
  simp [argFactor,Complex.div_im,ha,hx,Complex.normSq_pos.mpr hn |>.ne']

theorem Points.product_real_pos {x : ℝ} (hx : 0<x) (hr : x<g.r) :
    0<(g.product x).re ∧ (g.product x).im=0 := by
  have hR := hr.trans (g.small.2.trans g.large.1)
  have hmem := nonreal_factor_mem g.upper.ne' hx.ne'
  have e : radical (conj g.u) x=conj (radical g.u x) := by simpa using radical_conj hmem
  have nu : radical g.u x≠0 := by
    intro h
    have e := radical_sq g.u (x:ℂ)
    rw [h,zero_pow (by decide)] at e
    exact slitPlane_ne_zero hmem e.symm
  have r₀ : 0<(1-x/g.r)^(1/2:ℝ) := Real.rpow_pos_of_pos (sub_pos.mpr ((div_lt_one g.rpos).mpr hr)) _
  have R₀ : 0<(1-x/g.R)^(1/2:ℝ) := Real.rpow_pos_of_pos (sub_pos.mpr ((div_lt_one g.Rpos).mpr hR)) _
  simp only [Points.product,positive_real_factor g.rpos hr,positive_real_factor g.Rpos hR,e,
    mul_assoc,Complex.mul_conj,←Complex.ofReal_mul,Complex.ofReal_re,Complex.ofReal_im,and_true]
  exact mul_pos r₀ (mul_pos R₀ (Complex.normSq_pos.mpr nu))

/-- Continuation of the generating germ by the normalized product. The
rationalized expression automatically fills the two removable points. -/
noncomputable def Points.branch (z : ℂ) := 2/(Branch.linearFactor (s:ℂ) z+g.product z)

theorem Points.den_ne (z : ℂ) : Branch.linearFactor (s:ℂ) z+g.product z≠0 := by
  intro h
  have hw := (g.product_sq z).trans (Branch.square_identity _ _)
  have ne : Branch.quadraticFactor (s:ℂ) z=0 := by
    linear_combination (Branch.linearFactor (s:ℂ) z - g.product z)/4*h + hw/4
  have sc : (s:ℂ)≠0 := ofReal_ne_zero.mpr (zero_lt_one.trans g.parameter).ne'
  have sc1 : (1:ℂ)-(s:ℂ)≠0 := by exact_mod_cast sub_ne_zero.mpr g.parameter.ne
  rcases mul_eq_zero.mp ne with e|e
  · have z0 : z=0 := pow_eq_zero ((mul_eq_zero.mp e).resolve_left sc1)
    simp [z0,Branch.linearFactor] at h
  · have ez : z=((1/s:ℝ):ℂ) := by
      push_cast
      apply (eq_div_iff sc).mpr
      linear_combination -e
    subst z
    have sp := zero_lt_one.trans g.parameter
    have pp := g.product_real_pos (one_div_pos.mpr sp) g.small.1
    have D : Branch.linearFactor (s:ℂ) ((1/s:ℝ):ℂ)=(((s-1)/s:ℝ):ℂ) := by
      unfold Branch.linearFactor; push_cast; field_simp [sc]; ring
    have hh := congrArg Complex.re h
    rw [D,Complex.add_re,Complex.ofReal_re,Complex.zero_re] at hh
    linarith [div_pos (sub_pos.mpr g.parameter) sp]

theorem Points.branch_diff {z : ℂ} (hz : z∈g.domain) : DifferentiableAt ℂ g.branch z :=
  (differentiableAt_const _).div ((show DifferentiableAt ℂ (Branch.linearFactor (s:ℂ)) z by
    unfold Branch.linearFactor; fun_prop).add (g.product_diff hz)) (g.den_ne z)

theorem Points.unreduced {z : ℂ} (hn : Branch.quadraticFactor (s:ℂ) z≠0) :
    g.branch z=(Branch.linearFactor (s:ℂ) z-g.product z)/(2*Branch.quadraticFactor (s:ℂ) z) := by
  have e := (g.product_sq z).trans (Branch.square_identity _ _)
  apply (div_eq_div_iff (g.den_ne _) (mul_ne_zero (by norm_num) hn)).mpr
  linear_combination e

/-- The actual coefficient, with the branch already continued to the radial slit plane. -/
theorem Points.coefficient :
    ∃ ε : ℝ, 0<ε ∧ ∀ r∈Ioo 0 ε, ∀ n : ℕ, Complex.ofReal ((B (n+1)).eval (1-s)) =
      (2*Real.pi*I:ℂ)⁻¹ * ∮ z in C((0:ℂ),r), z⁻¹^(n+1)*g.branch z := by
  apply Series.cauchy_coefficient_of_germ
  filter_upwards [Series.series_eq_regular_near_zero (1-s),g.germ_product] with z h1 h2
  rw [h1,Branch.regularBranch,show (1:ℂ)-((1-s:ℝ):ℂ)=(s:ℂ) by push_cast; ring,h2]
  rfl

end BigDescents132.Slit
