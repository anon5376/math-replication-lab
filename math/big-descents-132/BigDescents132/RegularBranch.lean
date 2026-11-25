import BigDescents132.Quartic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace BigDescents132.Branch
open Complex Set

def linearFactor {K : Type*} [CommRing K] (s x : K) := 1-2*x+s*x^2
def quadraticFactor {K : Type*} [CommRing K] (s x : K) := (1-s)*x^2*(1-s*x)

theorem square_identity {K : Type*} [CommRing K] (s x : K) :
    (radicand s).eval x=linearFactor s x^2-4*quadraticFactor s x := by simp [radicand,linearFactor,quadraticFactor]; ring

/-- Rationalized square branch of the quadratic generating function, with
value 1 at the origin. -/
noncomputable def regularBranch (s z : ℂ) : ℂ :=
  2/(linearFactor s z+((radicand s).eval z)^(2⁻¹:ℂ))

@[simp] theorem regularBranch_zero (s : ℂ) : regularBranch s 0=1 := by
  norm_num [regularBranch,linearFactor,radicand]

private theorem complex_sqrt_sq (v : ℂ) : (v^(2⁻¹:ℂ))^2=v := by
  rw [← Complex.cpow_mul_nat]
  norm_num

theorem rationalized_eq {s z : ℂ} (hN : quadraticFactor s z≠0) :
    regularBranch s z = (linearFactor s z-((radicand s).eval z)^(2⁻¹:ℂ))/(2*quadraticFactor s z) := by
  let r := ((radicand s).eval z)^(2⁻¹:ℂ)
  have h : r^2=linearFactor s z^2-4*quadraticFactor s z := (complex_sqrt_sq _).trans (square_identity _ _)
  have hden : linearFactor s z+r≠0 := by
    intro H
    apply hN
    linear_combination (linearFactor s z-r)/4*H + h/4
  change 2/(linearFactor s z+r)=(linearFactor s z-r)/(2*quadraticFactor s z)
  apply (div_eq_div_iff hden (mul_ne_zero (by norm_num) hN)).mpr
  linear_combination h

private theorem segment_pos {s x : ℝ} (hs : 1<s) (hx : x∈Icc 0 (1/s)) :
    0<linearFactor s x ∧ 0<(radicand s).eval x := by
  have hs' : 0<s := by linarith
  have hx' := hx.2.trans_lt ((div_lt_one hs').mpr hs)
  have hD : 0<linearFactor s x := by
    have e : linearFactor s x=(1-x)^2+(s-1)*x^2 := by dsimp [linearFactor]; ring
    rw [e]
    exact add_pos_of_pos_of_nonneg (sq_pos_of_pos (sub_pos.mpr hx')) (mul_nonneg (sub_nonneg.mpr hs.le) (sq_nonneg _))
  have hx₁ : x*s≤1 := (le_div_iff₀ hs').mp hx.2
  have hN : quadraticFactor s x≤0 := mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)) (by nlinarith)
  exact ⟨hD,by rw [square_identity]; nlinarith [sq_pos_of_pos hD]⟩

private theorem cast_rad (s x : ℝ) : (radicand (s:ℂ)).eval (x:ℂ)=((radicand s).eval x:ℝ) := by
  simp [radicand]

/-- The rationalized expression extends holomorphically at each point of
the real segment from 0 through the apparent pole 1/s. -/
theorem regular_on_segment {s x : ℝ} (hs : 1<s) (hx : x∈Icc 0 (1/s)) :
    DifferentiableAt ℂ (regularBranch (s:ℂ)) (x:ℂ) := by
  obtain ⟨hD,hQ⟩ := segment_pos hs hx
  have hslit : (radicand (s:ℂ)).eval (x:ℂ)∈Complex.slitPlane := by
    rw [cast_rad]; exact Complex.mem_slitPlane_iff.mpr (Or.inl hQ)
  have hroot := ((radicand (s:ℂ)).differentiableAt (x:=(x:ℂ))).cpow_const (c:=(2⁻¹:ℂ)) hslit
  have hden : linearFactor (s:ℂ) (x:ℂ) + ((radicand (s:ℂ)).eval (x:ℂ))^(2⁻¹:ℂ)≠0 := by
    rw [cast_rad, show (2⁻¹:ℂ)=((2⁻¹:ℝ):ℂ) by norm_num,←Complex.ofReal_cpow hQ.le]
    have e : linearFactor (s:ℂ) (x:ℂ) = (linearFactor s x:ℝ) := by simp [linearFactor]
    rw [e,←Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr (add_pos hD (Real.rpow_pos_of_pos hQ _)).ne'
  exact (differentiableAt_const _).div ((show DifferentiableAt ℂ (linearFactor (s:ℂ)) (x:ℂ) by unfold linearFactor; fun_prop).add hroot) hden

/-- At the apparent pole of the unreduced expression the value is s/(s-1). -/
theorem regular_at_pole {s : ℝ} (hs : 1<s) : regularBranch s ((1/s:ℝ):ℂ)=((s/(s-1):ℝ):ℂ) := by
  have hs' : 0<s := by linarith
  have sc : (s:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hs'.ne'
  have de : linearFactor (s:ℂ) ((1/s:ℝ):ℂ)=(((s-1)/s:ℝ):ℂ) := by unfold linearFactor; push_cast; field_simp [sc]; ring
  have ne : quadraticFactor (s:ℂ) ((1/s:ℝ):ℂ)=0 := by unfold quadraticFactor; push_cast; field_simp [sc]
  have pos : 0<(((s-1)/s:ℝ):ℂ).re := div_pos (sub_pos.mpr hs) hs'
  rw [regularBranch,square_identity,ne,mul_zero,sub_zero,de,Complex.sq_cpow_two_inv pos]
  push_cast
  field_simp [show (s:ℂ)-1≠0 by exact_mod_cast sub_ne_zero.mpr hs.ne']
  ring

end BigDescents132.Branch
