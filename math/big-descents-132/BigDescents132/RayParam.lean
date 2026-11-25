import BigDescents132.Deformation
import BigDescents132.MovingCuts

namespace BigDescents132.Slit
open Complex Set MeasureTheory
open scoped ComplexConjugate Topology

noncomputable def advance (a : ℂ) (v : ℝ) := Real.log ‖a‖+Real.log (1+v)

theorem exp_advance {a : ℂ} (ha : a≠0) {v : ℝ} (hv : -1<v) :
    Real.exp (advance a v)=‖a‖*(1+v) := by
  rw [advance,Real.exp_add,Real.exp_log (norm_pos_iff.mpr ha),Real.exp_log (by linarith)]

theorem advance_excess {a : ℂ} (ha : a≠0) (x : ℝ) : advance a (excess a x)=x := by
  rw [advance,excess,show 1+(Real.exp x/‖a‖-1)=Real.exp x/‖a‖ by ring,
    Real.log_div (Real.exp_pos _).ne' (norm_pos_iff.mpr ha).ne',Real.log_exp]
  ring

theorem excess_advance {a : ℂ} (ha : a≠0) {v : ℝ} (hv : -1<v) : excess a (advance a v)=v := by
  rw [excess,exp_advance ha hv]
  field_simp [norm_ne_zero_iff.mpr ha]

theorem radial_advance {a : ℂ} (ha : a≠0) {v : ℝ} (hv : -1<v) :
    radial a (advance a v)=a*(1+(v:ℂ)) := by rw [radial_excess,excess_advance ha hv]

private theorem wholeCut_change (n : ℕ) {a : ℂ} (ha : a≠0) (J : ℝ → ℂ) {S : Set ℝ}
    (hs : MeasurableSet S) (hp : S⊆Ioi 0) (zero : ∀ x, excess a x∉S → J x=0) :
    wholeCut n a J=∫ v in S, (1+v)⁻¹ • weighted n a J (advance a v) := by
  have der (v : ℝ) (hv : v∈S) : HasDerivWithinAt (advance a) (1+v)⁻¹ S v := by
    have H := hp hv
    have vp : 0<v := H
    have h := (((hasDerivAt_id v).const_add 1).log (by change (1:ℝ)+v≠0; positivity)).const_add (Real.log ‖a‖)
    simpa only [advance,id_eq,one_div] using h.hasDerivWithinAt (s:=S)
  have inj : InjOn (advance a) S := fun v hv w hw e => by
    have e' := congrArg (excess a) e
    have v' : 0<v := hp hv
    have w' : 0<w := hp hw
    simpa only [excess_advance ha (show -1<v by linarith),excess_advance ha (show -1<w by linarith)] using e'
  have bound : ∀ x, x∉advance a '' S → weighted n a J x=0 := by
    intro x hx
    have h : excess a x∉S := fun h => hx ⟨_,h,advance_excess ha x⟩
    simp [weighted,zero _ h]
  rw [wholeCut,←setIntegral_eq_integral_of_forall_compl_eq_zero bound,
    integral_image_eq_integral_abs_deriv_smul hs der inj]
  apply setIntegral_congr_fun hs
  intro v hv
  have vp : 0<v := hp hv
  dsimp only
  rw [abs_of_pos (inv_pos.mpr (by linarith : 0<1+v))]

/-- Complex coefficient of the beta moment at a branch point. -/
noncomputable def amplitude (s : ℝ) (a : ℂ) (A : ℂ → ℂ) :=
  A a/(2*(Real.pi:ℂ)*(1-(s:ℂ))*a*(1-(s:ℂ)*a))

noncomputable def multiplier (s : ℝ) (a : ℂ) (A : ℂ → ℂ) (v : ℝ) :=
  let z := a*(1+(v:ℂ))
  (A z/A a)*(1-(s:ℂ)*a)/((1+(v:ℂ))*(1-(s:ℂ)*z))

noncomputable def weight (s : ℝ) (n : ℕ) (a : ℂ) (A : ℂ → ℂ) :=
  a⁻¹^n * amplitude s a A

theorem radical_ne {a z : ℂ} (h : argFactor a z∈slitPlane) : radical a z≠0 := by
  intro hz
  have e := radical_sq a z
  rw [hz,zero_pow (by decide)] at e
  exact slitPlane_ne_zero h e.symm

variable {s : ℝ} (g : Points s)

theorem Points.rayOther_ne {a : ℂ} (him : a.im≠0) {v : ℝ} (hv : 0≤v) :
    g.rayOther a (a*(1+(v:ℂ)))≠0 := by
  obtain ⟨h1,h2,h3⟩ := ray_arguments g him hv
  exact mul_ne_zero (mul_ne_zero (radical_ne h1) (radical_ne h2)) (radical_ne h3)

theorem Points.rayOther_conj {a : ℂ} (him : a.im≠0) {v : ℝ} (hv : 0≤v) :
    g.rayOther (conj a) ((conj a)*(1+(v:ℂ)))=conj (g.rayOther a (a*(1+(v:ℂ)))) := by
  obtain ⟨h1,h2,h3⟩ := ray_arguments g him hv
  have e1 := radical_conj h1
  have e2 := radical_conj h2
  have e3 := radical_conj h3
  simp only [map_mul,map_add,map_one,conj_ofReal,conj_conj] at e1 e2 e3
  simp [Points.rayOther,e1,e2,e3]

theorem Points.realOther_ne : g.realOther g.r≠0 := by
  exact mul_ne_zero (mul_ne_zero (radical_ne (real_factor_mem g.Rpos (g.small.2.trans g.large.1)))
    (radical_ne (nonreal_factor_mem g.upper.ne' g.rpos.ne')))
    (radical_ne (nonreal_factor_mem (by simpa using g.upper.ne') g.rpos.ne'))

theorem Points.realOther_fixed : conj (g.realOther g.r)=g.realOther g.r := by
  have h1 := radical_conj (real_factor_mem g.Rpos (g.small.2.trans g.large.1))
  have h2 := radical_conj (nonreal_factor_mem g.upper.ne' g.rpos.ne')
  have h3 := radical_conj (nonreal_factor_mem (a:=conj g.u) (by simpa using g.upper.ne') g.rpos.ne')
  simp only [conj_ofReal,conj_conj] at h1 h2 h3
  simp only [Points.realOther,map_mul,←h1,←h2,←h3]
  ring

private theorem density_algebra {K : Type*} [Field K] (a b t d e p i A B v : K)
    (hd : d≠0) (hi : i≠0) (hA : A≠0) (n : ℕ) :
    (p*i)⁻¹*(b⁻¹*((a*b)⁻¹^n*(i*v*B/(t*(a*b)^2*e)))) =
    a⁻¹^(n+1)*(A/(p*t*a*d))*((v/b^(n+1+1))*(B/A*d/(b*e))) := by
  simp only [div_eq_mul_inv,mul_inv,mul_pow,pow_succ,←inv_pow]
  let F := v*B*p⁻¹*b⁻¹^3*b⁻¹^n*a⁻¹^2*a⁻¹^n*t⁻¹*e⁻¹
  calc
    _ = (i*i⁻¹)*F := by dsimp [F]; ring
    _ = (A*A⁻¹)*(d*d⁻¹)*F := by simp [hi,hA,hd]
    _ = _ := by dsimp [F]; ring

private theorem point_density {a : ℂ} (A : ℂ → ℂ) (A0 : A a≠0)
    {v : ℝ} (pole : 1-(s:ℂ)*a≠0) (n : ℕ) :
    let z := a*(1+(v:ℂ))
    (2*(Real.pi:ℂ)*I)⁻¹*((1+v)⁻¹ • (z⁻¹^n*(I*(Real.sqrt v:ℂ)*A z/Branch.quadraticFactor (s:ℂ) z))) =
      weight s (n+1) a A * (Cut.kernel (n+1) v • multiplier s a A v) := by
  dsimp only
  simp only [weight,amplitude,multiplier,Cut.kernel,Branch.quadraticFactor,Complex.real_smul,
    ←Real.sqrt_eq_rpow,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_inv,
    Complex.ofReal_add,Complex.ofReal_one]
  exact density_algebra _ _ _ _ _ _ _ _ _ _ pole Complex.I_ne_zero A0 n

private theorem realPole {x : ℝ} (hx : g.r≤x) : 1-(s:ℂ)*(x:ℂ)≠0 := by
  have sp := zero_lt_one.trans g.parameter
  have e : 1<x*s := (div_lt_iff₀ sp).mp (g.small.1.trans_le hx)
  exact_mod_cast (show 1-s*x≠0 by linarith [mul_comm s x])

include g in
private theorem complexPole {a : ℂ} (h : a.im≠0) {v : ℝ} (hv : 0≤v) : 1-(s:ℂ)*(a*(1+(v:ℂ)))≠0 := by
  have hs := (zero_lt_one.trans g.parameter).ne'
  intro e
  have hi := congrArg im e
  simp [Complex.mul_im,h,hs,show (1+v:ℝ)≠0 by linarith] at hi

/-- The full complex ray, in the beta-prime parameter used in the interior estimate. -/
theorem Points.complex_cut {a : ℂ} (him : a.im≠0) (n : ℕ) :
    (2*(Real.pi:ℂ)*I)⁻¹*wholeCut n a (g.complexJump a)=
    weight s (n+1) a (g.rayOther a) * ∫ v in Ioi (0:ℝ), Cut.kernel (n+1) v • multiplier s a (g.rayOther a) v := by
  have ha : a≠0 := by intro h; simp [h] at him
  have A0 : g.rayOther a a≠0 := by simpa using g.rayOther_ne him (le_rfl : (0:ℝ)≤0)
  have pole : 1-(s:ℂ)*a≠0 := by simpa using complexPole g him (le_rfl : (0:ℝ)≤0)
  have zero (x : ℝ) (h : excess a x∉Ioi 0) : g.complexJump a x=0 := by
    have hn : excess a x≤0 := not_lt.mp h
    rcases hn.eq_or_lt with e|h
    · simp [Points.complexJump,e]
    · simp [Points.complexJump,not_le.mpr h]
  rw [wholeCut_change n ha _ measurableSet_Ioi (Subset.rfl) zero,←integral_const_mul,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  have vp : 0<v := hv
  have lo : -1<v := by linarith
  simp only [weighted,Points.complexJump,radial_advance ha lo,excess_advance ha lo, if_pos vp.le]
  exact point_density _ A0 pole n

noncomputable def Points.endReal := g.R/g.r-1

/-- The positive real cut stops at the second real root. -/
theorem Points.real_cut (n : ℕ) :
    (2*(Real.pi:ℂ)*I)⁻¹*wholeCut n g.r g.realJump=
    weight s (n+1) g.r g.realOther * ∫ v in Ioo (0:ℝ) g.endReal, Cut.kernel (n+1) v • multiplier s g.r g.realOther v := by
  have ha : (g.r:ℂ)≠0 := ofReal_ne_zero.mpr g.rpos.ne'
  have exc (x : ℝ) : excess g.r x=Real.exp x/g.r-1 := by simp [excess,Real.norm_of_nonneg g.rpos.le]
  have zero (x : ℝ) (h : excess g.r x∉Ioo 0 g.endReal) : g.realJump x=0 := by
    unfold Points.realJump
    split_ifs with inr
    · rcases inr.1.eq_or_lt with eq|lt
      · simp [exc,←eq,g.rpos.ne']
      · exact (h ⟨by rw [exc,sub_pos,lt_div_iff₀ g.rpos,one_mul]; exact lt,
          by rw [exc,Points.endReal,sub_lt_sub_iff_right,div_lt_div_iff_of_pos_right g.rpos]; exact inr.2⟩).elim
    · rfl
  rw [wholeCut_change n ha _ measurableSet_Ioo Ioo_subset_Ioi_self zero,←integral_const_mul,←integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro v hv
  have vlo := hv.1
  have lo : -1<v := by linarith
  have hxr : g.r≤g.r*(1+v) := le_mul_of_one_le_right g.rpos.le (by linarith)
  have hxR : g.r*(1+v)<g.R := by
    have hhi : 1+v<g.R/g.r := by have h := hv.2; change v<g.R/g.r-1 at h; linarith
    simpa [mul_comm] using (lt_div_iff₀ g.rpos).mp hhi
  have exp : Real.exp (advance (g.r:ℂ) v)=g.r*(1+v) := by simpa [Real.norm_of_nonneg g.rpos.le] using exp_advance ha lo
  have p0 := realPole g (le_rfl : g.r≤g.r)
  simp only [weighted,Points.realJump,radial_advance ha lo,excess_advance ha lo,exp, if_pos (And.intro hxr hxR),
    Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_one]
  exact point_density _ g.realOther_ne p0 n

end BigDescents132.Slit
