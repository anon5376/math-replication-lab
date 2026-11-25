import BigDescents132.Dominance
import Mathlib.Topology.Order.Compact

namespace BigDescents132.Branch
open Complex Set Metric

private def value {K : Type*} [CommRing K] (s x : K) :=
  1-4*x+6*s*x^2-4*s^2*x^3+s^2*x^4
private theorem value_eq {K : Type*} [CommRing K] (s x : K) :
    (radicand s).eval x = value s x := by simp [radicand,value]

/-- Imaginary part of the quartic divided by Im z, extended polynomially
across the real axis. At y=0 it is precisely the real derivative. -/
private def dividedImag (s x y : ℝ) :=
  -4+12*s*x-4*s^2*(3*x^2-y^2)+4*s^2*x*(x^2-y^2)

private theorem imag_value (s : ℝ) (z : ℂ) :
    (value (s:ℂ) z).im=z.im*dividedImag s z.re z.im := by
  simp [value,dividedImag,pow_succ,Complex.mul_re,Complex.mul_im]
  ring

private theorem divided_excludes_real {s : ℝ} {z : ℂ} (hs : 1<s) (hz : value (s:ℂ) z=0)
    (hd : dividedImag s z.re z.im=0) : z.im≠0 := by
  intro hi
  have eq : z = (z.re:ℂ) := by apply Complex.ext <;> simp [hi]
  have h₀ : (radicand (s:ℂ)).IsRoot z := (value_eq _ _).trans hz
  apply radicand_simple (s:=(s:ℂ)) (by exact_mod_cast (show s≠0 by linarith)) (by exact_mod_cast hs.ne') h₀
  change (radicand (s:ℂ)).derivative.eval z=0
  rw [eq]
  norm_num [radicand,Polynomial.derivative_sub,Polynomial.derivative_add,
    Polynomial.derivative_mul,Polynomial.derivative_pow]
  rw [hi] at hd
  unfold dividedImag at hd
  norm_num at hd
  have H : (((-4+12*s*z.re-4*s^2*(3*z.re^2)+4*s^2*z.re*z.re^2:ℝ):ℂ))=0 := by exact_mod_cast hd
  push_cast at H
  linear_combination H

private abbrev Parameters := ℝ × ℝ × ℂ
private def geometry (p : Parameters) : Prop :=
  value p.1 p.2.1=0 ∧ value (p.1:ℂ) p.2.2=0 ∧
    dividedImag p.1 p.2.2.re p.2.2.im=0

private theorem geometry_closed : IsClosed {p : Parameters | geometry p} := by
  have c₁ : Continuous (fun p : Parameters => value p.1 p.2.1) := by unfold value; fun_prop
  have c₂ : Continuous (fun p : Parameters => value (p.1:ℂ) p.2.2) := by unfold value; fun_prop
  have c₃ : Continuous (fun p : Parameters => dividedImag p.1 p.2.2.re p.2.2.im) := by unfold dividedImag; fun_prop
  exact (isClosed_eq c₁ continuous_const).inter ((isClosed_eq c₂ continuous_const).inter (isClosed_eq c₃ continuous_const))

/-- On a compact interval of parameters away from the endpoints, the
dominant nonreal roots are separated in modulus by a uniform positive gap. -/
theorem compact_gap {a b : ℝ} (ha : 1<a) :
    ∃ c : ℝ, 0<c ∧ ∀ s∈Icc a b, ∀ r∈Ioo (1/s) 1, (radicand s).IsRoot r →
      ∀ z : ℂ, (radicand (s:ℂ)).IsRoot z → z.im≠0 → c≤r-‖z‖ := by
  let K : Set Parameters := (Icc a b ×ˢ (Icc 0 1 ×ˢ closedBall (0:ℂ) 1)) ∩
    {p : Parameters | geometry p}
  have Kc : IsCompact K := (isCompact_Icc.prod (isCompact_Icc.prod (isCompact_closedBall (0:ℂ) 1))).inter_right geometry_closed
  let gap := fun p : Parameters => p.2.1-‖p.2.2‖
  have gc : Continuous gap := by dsimp [gap]; fun_prop
  have positive (p : Parameters) (hp : p∈K) : 0<gap p := by
    obtain ⟨⟨hs,hr,_⟩,h₁,h₂,h₃⟩ := hp
    have hs' := ha.trans_le hs.1
    have hroot : (radicand p.1).IsRoot p.2.1 := (value_eq _ _).trans h₁
    obtain ⟨r,hr₀,R,hR,hall⟩ := real_branch_points hs'
    have hpr : p.2.1=r := ((hall _).mp hroot).resolve_right (by intro e; linarith [hr.2,hR.1])
    have hI : p.2.1∈Ioo (1/p.1) 1 := hpr ▸ hr₀
    exact sub_pos.mpr (dominant_pair hs' hI hroot ((value_eq _ _).trans h₂) (divided_excludes_real hs' h₂ h₃))
  have include' (s : ℝ) (hs : s∈Icc a b) (r : ℝ) (hr : r∈Ioo (1/s) 1) (h : (radicand s).IsRoot r)
      (z : ℂ) (hz : (radicand (s:ℂ)).IsRoot z) (hi : z.im≠0) : (s,r,z)∈K := by
    have hs' := ha.trans_le hs.1
    have hr' : 0<r := (one_div_pos.mpr (show 0<s by linarith)).trans hr.1
    have hm := dominant_pair hs' hr h hz hi
    have vz : value (s:ℂ) z=0 := (value_eq _ _).symm.trans hz
    have he := congrArg Complex.im vz
    rw [imag_value,Complex.zero_im] at he
    exact ⟨⟨hs,⟨hr'.le,hr.2.le⟩,by simpa using (hm.trans hr.2).le⟩,
      (value_eq _ _).symm.trans h,vz,(mul_eq_zero.mp he).resolve_left hi⟩
  by_cases hK : K.Nonempty
  · obtain ⟨p,hp,hmin⟩ := Kc.exists_isMinOn hK gc.continuousOn
    exact ⟨gap p,positive p hp,fun s hs r hr h z hz hi => hmin (include' s hs r hr h z hz hi)⟩
  · exact ⟨1,by norm_num,fun s hs r hr h z hz hi => False.elim (hK ⟨_,include' s hs r hr h z hz hi⟩)⟩

end BigDescents132.Branch
