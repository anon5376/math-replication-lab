import BigDescents132.Annulus
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace BigDescents132.Slit
open Complex Filter Set MeasureTheory
open scoped ComplexConjugate Topology

private noncomputable def factorConstant (a : ℂ) := Real.sqrt (1+‖a‖⁻¹)

private theorem factor_bound (a z : ℂ) (h : 1≤‖z‖) :
    ‖radical a z‖≤factorConstant a*Real.sqrt ‖z‖ := by
  have sq : ‖radical a z‖^2=‖argFactor a z‖ := by rw [←norm_pow,radical_sq]
  have e := norm_sub_le (1:ℂ) (z/a)
  rw [norm_one,norm_div] at e
  have bound : ‖argFactor a z‖≤(1+‖a‖⁻¹)*‖z‖ := by
    unfold argFactor
    calc
      _ ≤ 1+‖z‖/‖a‖ := e
      _ ≤ ‖z‖+‖z‖/‖a‖ := by linarith
      _ = _ := by ring
  rw [←sq] at bound
  have pos : 0≤1+‖a‖⁻¹ := by positivity
  simpa [Real.sqrt_sq (norm_nonneg _),Real.sqrt_mul pos,factorConstant] using Real.sqrt_le_sqrt bound

/-- Global in z for each fixed parameter, uniformly over all directions and both
lips of every slit. This bound suffices to discard the outer circle. -/
theorem Points.outer_bound {s : ℝ} (g : Points s) :
    ∃ C : ℝ, 0<C ∧ ∀ z : ℂ, 2≤‖z‖ → ‖g.branch z‖≤C/‖z‖ := by
  let K := factorConstant g.r*factorConstant g.R*factorConstant g.u*factorConstant (conj g.u)
  have kp : 0≤K := by dsimp [K,factorConstant]; positivity
  have hs := zero_lt_one.trans g.parameter
  let M := 3+s+K
  have Mp : 0<M := by dsimp [M]; linarith
  refine ⟨M/((s-1)*s),div_pos Mp (mul_pos (sub_pos.mpr g.parameter) hs),fun z hz => ?_⟩
  let r := ‖z‖
  have h₁ : 1≤r := by dsimp [r]; linarith
  have rp : 0<r := zero_lt_one.trans_le h₁
  have q := Real.sq_sqrt (norm_nonneg z)
  have W : ‖g.product z‖≤K*r^2 := by
    simp only [Points.product,norm_mul]
    calc
      _ ≤ (factorConstant g.r*Real.sqrt r)*(factorConstant g.R*Real.sqrt r)*
        (factorConstant g.u*Real.sqrt r)*(factorConstant (conj g.u)*Real.sqrt r) := by
          gcongr <;> first | exact factor_bound _ _ h₁ | unfold factorConstant; positivity
      _ = K*r^2 := by dsimp only [K,r]; linear_combination (factorConstant g.r*factorConstant g.R*factorConstant g.u*factorConstant (conj g.u))*(Real.sqrt ‖z‖^2+‖z‖)*q
  have D : ‖Branch.linearFactor (s:ℂ) z‖≤(3+s)*r^2 := by
    have e := (norm_add_le ((1:ℂ)-2*z) ((s:ℂ)*z^2)).trans
      (add_le_add_right (norm_sub_le (1:ℂ) (2*z)) _)
    simp [norm_mul,norm_pow,Real.norm_of_nonneg hs.le] at e
    change ‖1-2*z+(s:ℂ)*z^2‖≤_
    apply e.trans
    change 1+2*r+s*r^2≤_
    have r₂ : r≤r^2 := by nlinarith [mul_nonneg rp.le (sub_nonneg.mpr h₁)]
    linarith
  have pole : s*r/2≤‖(1:ℂ)-(s:ℂ)*z‖ := by
    have e := norm_sub_norm_le ((s:ℂ)*z) (1:ℂ)
    rw [norm_sub_rev,norm_one,norm_mul,Complex.norm_real,Real.norm_of_nonneg hs.le] at e
    have sr : 2≤s*r := by nlinarith [mul_nonneg (sub_nonneg.mpr g.parameter.le) rp.le]
    linarith
  have N : (s-1)*s*r^3/2≤‖Branch.quadraticFactor (s:ℂ) z‖ := by
    simp only [Branch.quadraticFactor,norm_mul,norm_pow,show (1:ℂ)-(s:ℂ)=((1-s:ℝ):ℂ) by push_cast; rfl,
      Complex.norm_real,Real.norm_of_nonpos (sub_nonpos.mpr g.parameter.le)]
    have K₀ : 0≤(s-1)*r^2 := by have hp := sub_pos.mpr g.parameter; positivity
    change _≤ -(1-s)*r^2*_
    nlinarith only [mul_le_mul_of_nonneg_left pole K₀]
  have NP : 0<‖Branch.quadraticFactor (s:ℂ) z‖ := (show 0<(s-1)*s*r^3/2 by have hp := sub_pos.mpr g.parameter; positivity).trans_le N
  rw [g.unreduced (norm_pos_iff.mp NP),norm_div,norm_mul,Complex.norm_ofNat]
  apply (div_le_div_iff₀ (mul_pos (by norm_num) NP) rp).mpr
  have num : ‖Branch.linearFactor (s:ℂ) z-g.product z‖ ≤ M*r^2 :=
    (norm_sub_le _ _).trans ((add_le_add D W).trans_eq (by dsimp [M]; ring))
  have di : 0<(s-1)*s := mul_pos (sub_pos.mpr g.parameter) hs
  calc
    _ ≤ (M*r^2)*r := mul_le_mul_of_nonneg_right num rp.le
    _ = (M/((s-1)*s))*((s-1)*s*r^3) := by field_simp [di.ne']; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (div_nonneg Mp.le di.le)

/-- The outer coefficient circle converges to zero, including rank one. -/
theorem Points.outer_vanishes {s : ℝ} (g : Points s) (n : ℕ) :
    Tendsto (fun x : ℝ => ∮ z in C((0:ℂ),Real.exp x), z⁻¹^(n+1)*g.branch z) atTop (𝓝 0) := by
  obtain ⟨C,hC,bnd⟩ := g.outer_bound
  have lim : Tendsto (fun x : ℝ => 2*Real.pi*C/(Real.exp x)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_exp_atTop
  apply squeeze_zero_norm' _ lim
  filter_upwards [Real.tendsto_exp_atTop.eventually_ge_atTop 2] with x h
  let R := Real.exp x
  have rp : 0<R := Real.exp_pos _
  have bnd' : ∀ z∈Metric.sphere (0:ℂ) R, ‖z⁻¹^(n+1)*g.branch z‖≤C/R^2 := by
    intro z hz
    have e : ‖z‖=R := by simpa [Metric.mem_sphere,dist_eq] using hz
    have H := bnd z (e ▸ h)
    rw [e] at H
    rw [norm_mul,norm_pow,norm_inv,e,pow_succ]
    have pow : R⁻¹^n≤1 := pow_le_one₀ (inv_nonneg.mpr rp.le) ((inv_le_one₀ rp).mpr (by dsimp [R]; linarith))
    calc
      _ ≤ (1*R⁻¹)*(C/R) := by gcongr
      _ = _ := by ring
  apply (circleIntegral.norm_integral_le_of_norm_le_const rp.le bnd').trans_eq
  change 2*Real.pi*R*(C/R^2)=2*Real.pi*C/R
  field_simp [rp.ne']; ring

end BigDescents132.Slit
