import BigDescents132.AllRankScale
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace BigDescents132.AllRanks
open Set Slit Complex

private noncomputable def eta (p : ℝ) := (1-p^2)*(second p)^2*(1+3*p^2)/(p+second p)^4

private theorem eta_cont : ContinuousOn eta (Icc 0 1) := by
  have rad : Continuous radicalS := by unfold radicalS;fun_prop
  have den (x : ℝ) (hx : x∈Icc 0 1) : 0<radicalS x+2*x := by
    rcases hx.1.eq_or_lt with h|h
    · subst x;norm_num [radicalS]
    · exact add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) (by linarith)
  have Z : ContinuousOn second (Icc 0 1) := by
    unfold second;exact (by fun_prop : Continuous fun p : ℝ => 1-p^2).continuousOn.div
      (rad.add (continuous_const.mul continuous_id)).continuousOn (fun p hp => (den p hp).ne')
  have hh (p : ℝ) (hp : p∈Icc 0 1) : 0<p+second p := by
    rcases hp.1.eq_or_lt with h|h
    · subst p;norm_num [second,radicalS]
    · apply add_pos_of_pos_of_nonneg h
      apply div_nonneg _ (den p hp).le
      nlinarith only [mul_nonneg (sub_nonneg.mpr hp.2) (show 0≤1+p by linarith)]
  unfold eta
  exact (((by fun_prop : Continuous fun p : ℝ => 1-p^2).continuousOn.mul (Z.pow 2)).mul
    (by fun_prop : Continuous fun p : ℝ => 1+3*p^2).continuousOn).div
      ((continuousOn_id.add Z).pow 4) (fun p hp => (pow_pos (hh p hp) _).ne')

private theorem eta_inv {p : ℝ} (hp : p∈Ioo 0 1) : eta p=(coordinate p hp).sVal⁻¹ := by
  rw [Coordinate.sVal,inv_div];rfl

theorem parameter_onto (s : Param) : ∃ (p : ℝ) (hp : p∈Ioo 0 1), (coordinate p hp).param=s := by
  have sp:=s.property
  have e0 : eta 0=1 := by norm_num [eta,second,radicalS]
  have e1 : eta 1=0 := by norm_num [eta]
  obtain ⟨p,hp,ep⟩:=intermediate_value_Ioo' (by norm_num : (0:ℝ)≤1) eta_cont
    (show s.val⁻¹∈Ioo (eta 1) (eta 0) by rw [e1,e0];exact ⟨inv_pos.mpr (by linarith),inv_lt_one_of_one_lt₀ sp⟩)
  refine ⟨p,hp,Subtype.ext ?_⟩
  exact inv_injective ((eta_inv hp).symm.trans ep)

theorem moving_parameter {p : ℝ} (hp : p∈Ioo 0 1) (N : ℕ) (hN : 128≤N)
    (left : 3800/(N:ℝ)^3≤(coordinate p hp).sVal-1) : 5≤(N:ℝ)*p := by
  have nb : (128:ℝ)≤N := by exact_mod_cast hN
  have np : (0:ℝ)<N := by linarith
  have pp:=hp.1
  by_contra! h
  have small : p≤1/16 := by nlinarith only [mul_le_mul_of_nonneg_right nb pp.le,h]
  obtain ⟨_,hi⟩:=small_scale_bounds hp small
  have bound:=(div_le_iff₀ (pow_pos pp 3)).mp hi
  have low:=(div_le_iff₀ (pow_pos np 3)).mp left
  have upper:=mul_le_mul_of_nonneg_right bound (pow_pos np 3).le
  have cube:=pow_lt_pow_left₀ h (mul_nonneg np.le pp.le) (by decide : 3≠0)
  nlinarith only [low,upper,cube]

theorem left_phase_bound (N : ℕ) (hN : 128≤N) :
    ∃ s : Param, s.val-1=3800/(N:ℝ)^3 ∧ phase s N/Real.pi<7 := by
  let L:=3800/(N:ℝ)^3
  have nb : (128:ℝ)≤N := by exact_mod_cast hN
  have np : (0:ℝ)<N := by linarith
  have lp : 0<L := by dsimp [L];positivity
  have b0 : (1/16:ℝ)∈Ioo 0 1 := by constructor <;>norm_num
  let c0:=coordinate (1/16) b0
  have hb := (small_scale_bounds b0 (le_refl _)).1
  have v0 : (1:ℝ)+L<c0.sVal := by
    have n3:=pow_le_pow_left₀ (by norm_num : (0:ℝ)≤128) nb 3
    have h : L≤3800/(128:ℝ)^3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) n3
    change 15≤(c0.sVal-1)/(1/16)^3 at hb
    norm_num at h hb
    linarith only [h,hb]
  have e0 : eta 0=1 := by norm_num [eta,second,radicalS]
  have y : (1+L)⁻¹∈Ioo (eta (1/16)) (eta 0) := by
    rw [e0,eta_inv b0]
    exact ⟨inv_strictAnti₀ (by positivity) v0,inv_lt_one_of_one_lt₀ (by linarith)⟩
  obtain ⟨p,hp,ep⟩:=intermediate_value_Ioo' (by norm_num : (0:ℝ)≤1/16)
    (eta_cont.mono (Icc_subset_Icc le_rfl (by norm_num))) y
  have pp:=hp.1
  have mem : p∈Ioo 0 1 := ⟨pp,by linarith [hp.2]⟩
  let c:=coordinate p mem
  let g:=pointsAt c.param
  have sv : c.sVal=1+L := inv_injective ((eta_inv mem).symm.trans ep)
  refine ⟨c.param,by change c.sVal-1=L;linarith only [sv],?_⟩
  have low := (small_scale_bounds mem hp.2.le).1
  change 15≤(c.sVal-1)/p^3 at low
  rw [sv,add_sub_cancel_left] at low
  have lim : (N:ℝ)*p<19/3 := by
    have h:=(le_div_iff₀ (pow_pos pp 3)).mp low
    have hyp := (le_div_iff₀ (pow_pos np 3)).mp (show 15*p^3≤3800/(N:ℝ)^3 from h)
    apply lt_of_not_ge
    intro bad
    have cube:=pow_le_pow_left₀ (by norm_num : (0:ℝ)≤19/3) bad 3
    nlinarith only [cube,hyp]
  have root:=Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have rootb : Real.sqrt 3<26/15 := by nlinarith only [root,sq_nonneg (Real.sqrt 3-26/15)]
  have upre : 0<g.u.re := by
    rw [c.actual_upper_data.2.1]
    have cz:=c.z_mem.1
    have ch:=c.hpos
    have pp2:=pow_le_pow_left₀ pp.le hp.2.le 2
    have b : 0<1-3*c.p^2 := by change 0<1-3*p^2; nlinarith only [pp2]
    positivity
  have Rr : g.r<g.R := g.small.2.trans g.large.1
  have arglo (a : ℝ) (ha : ‖g.u‖<a) : -(Real.pi/2)<((a:ℂ)-g.u).arg := by
    apply Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl ?_)
    simp only [Complex.sub_re,Complex.ofReal_re]
    linarith only [(le_abs_self g.u.re).trans (Complex.abs_re_le_norm g.u),ha]
  have polearg : ((((c.param:ℝ)⁻¹:ℝ):ℂ)-g.u).arg<0 := by
    apply Complex.arg_neg_iff.mpr
    simp only [Complex.sub_im,Complex.ofReal_im,zero_sub,neg_lt_zero];exact g.upper
  have off : 0<g.phaseOffset := by
    rw [g.offset_formula]
    linarith only [arglo _ g.dominant,arglo _ (g.dominant.trans Rr),polearg,
      Complex.arg_lt_pi_div_two_iff.mpr (Or.inl upre)]
  have apos : 0<Real.arctan (Real.sqrt 3*p) := by simpa using Real.arctan_lt_arctan (show (0:ℝ)<Real.sqrt 3*p by positivity)
  have ang := Real.lt_tan apos (Real.arctan_lt_pi_div_two _)
  rw [Real.tan_arctan] at ang
  change ((N:ℝ)*g.u.arg-g.phaseOffset)/Real.pi<7
  rw [div_lt_iff₀ Real.pi_pos,c.theta_eq]
  change (N:ℝ)*(2*Real.arctan (Real.sqrt 3*p))-g.phaseOffset<_
  have alf:=mul_lt_mul_of_pos_left ang np
  have rt:=mul_lt_mul_of_pos_right rootb (mul_pos np pp)
  nlinarith only [off,alf,rt,lim,Real.pi_gt_d2]

end BigDescents132.AllRanks
