import BigDescents132.AllRankAlgebra

namespace BigDescents132.AllRanks
open Complex Set Slit
open scoped ComplexConjugate

structure Coordinate where
  p : ℝ
  z : ℝ
  p_mem : p∈Ioo 0 1
  z_mem : z∈Ioo 0 1
  curve : p^2+4*p*z+z^2+3*p^2*z^2=1

noncomputable def radicalS (p : ℝ) := Real.sqrt (1+6*p^2-3*p^4)
noncomputable def second (p : ℝ) := (1-p^2)/(radicalS p+2*p)

theorem radical_sq {p : ℝ} (hp : p∈Ioo 0 1) :
    1≤radicalS p ∧ (radicalS p)^2=1+6*p^2-3*p^4 := by
  have p2 : p^2≤1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hp.2.le) (show 0≤1+p by linarith [hp.1])]
  have a : 1≤1+6*p^2-3*p^4 := by nlinarith [mul_nonneg (sq_nonneg p) (sub_nonneg.mpr p2)]
  exact ⟨Real.one_le_sqrt.mpr a,Real.sq_sqrt (by linarith)⟩

theorem second_mem {p : ℝ} (hp : p∈Ioo 0 1) : second p∈Ioo 0 1 := by
  have s := (radical_sq hp).1
  have den : 0<radicalS p+2*p := by linarith [hp.1]
  have num : 0<1-p^2 := by nlinarith [mul_pos (sub_pos.mpr hp.2) (show 0<1+p by linarith [hp.1])]
  exact ⟨div_pos num den,(div_lt_one den).mpr (by linarith [sq_nonneg p,hp.1])⟩

noncomputable def coordinate (p : ℝ) (hp : p∈Ioo 0 1) : Coordinate where
  p := p
  z := second p
  p_mem := hp
  z_mem := second_mem hp
  curve := by
    obtain ⟨s,sq⟩ := radical_sq hp
    have dn : 0<radicalS p+2*p := by linarith [hp.1]
    unfold second
    field_simp [dn.ne']
    linear_combination ((p^2-1)*(radicalS p+2*p)^3)*sq

namespace Coordinate
variable (c : Coordinate)
def h := c.p+c.z
noncomputable def prod := (1-c.p^2)*c.z^2*(1+3*c.p^2)
noncomputable def sVal := c.h^4/c.prod
noncomputable def ru := (c.p-1)/c.h
noncomputable def Ru := (c.p+1)/c.h
noncomputable def cu : ℂ := (c.z:ℂ)*(1+(Real.sqrt 3:ℂ)*c.p*I)/c.h

theorem hpos : 0<c.h := add_pos c.p_mem.1 c.z_mem.1

theorem prod_pos : 0<c.prod := by
  have pz := c.p_mem
  have zz := c.z_mem
  have pos : 0<1-c.p^2 := by nlinarith [mul_pos (sub_pos.mpr pz.2) (show 0<1+c.p by linarith [pz.1])]
  exact mul_pos (mul_pos pos (pow_pos zz.1 2)) (by positivity)

theorem sgt : 1<c.sVal := by
  have cz := c.z_mem
  have cp := c.p_mem
  have pos : 0<1-c.z^2 := by nlinarith [mul_pos (sub_pos.mpr cz.2) (show 0<1+c.z by linarith [cz.1])]
  have other : 0<(1-c.z^2)*c.p^2*(1+3*c.z^2) := mul_pos (mul_pos pos (pow_pos cp.1 2)) (by positivity)
  have eqn := reciprocal_complement c.p c.z c.curve
  exact (one_lt_div c.prod_pos).mpr (by dsimp [h,prod]; linarith)

noncomputable def param : Slit.Param := ⟨c.sVal,c.sgt⟩

private theorem isRoot {w : ℂ}
    (zero : (((c.h:ℂ)*w-c.p)^2-1)*(((c.h:ℂ)*w-c.z)^2+3*(c.p:ℂ)^2*c.z^2)=0) :
    (radicand (c.sVal:ℂ)).IsRoot (w^2) := by
  have cv : (c.p:ℂ)^2+4*c.p*c.z+c.z^2+3*c.p^2*c.z^2=1 := by exact_mod_cast c.curve
  have prod' : (c.prod:ℂ)=(1-(c.p:ℂ)^2)*c.z^2*(1+3*c.p^2) := by simp [prod]
  have H := lifted_quartic (c.p:ℂ) (c.z:ℂ) w cv
  have h' : (c.h:ℂ)=(c.p:ℂ)+c.z := by simp [h]
  rw [←h',←prod',zero] at H
  apply square_root_discriminant
  unfold sVal
  push_cast
  field_simp [ofReal_ne_zero.mpr c.prod_pos.ne']
  linear_combination H

theorem small_large_upper :
    (pointsAt c.param).r=c.ru^2 ∧ (pointsAt c.param).R=c.Ru^2 ∧
    (pointsAt c.param).u=c.cu^2 := by
  have hpos := c.hpos
  have hc : (c.h:ℂ)≠0 := ofReal_ne_zero.mpr hpos.ne'
  have cre : (c.ru:ℂ)=((c.p:ℂ)-1)/c.h := by simp [ru]
  have cre' : (c.Ru:ℂ)=((c.p:ℂ)+1)/c.h := by simp [Ru]
  have hsh (x : ℂ) : (c.h:ℂ)*(x/c.h)=x := by field_simp
  have smallrt := c.isRoot (w:=(c.ru:ℂ)) (by rw [cre,hsh]; ring)
  have largert := c.isRoot (w:=(c.Ru:ℂ)) (by rw [cre',hsh]; ring)
  have ip := Complex.I_sq
  have sq : (Real.sqrt 3:ℂ)^2=3 := by exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ)≤3))
  have up := c.isRoot (w:=c.cu) (by
    rw [cu,hsh]; apply mul_eq_zero_of_right
    linear_combination (c.z^2*c.p^2*(Real.sqrt 3:ℂ)^2)*ip-(c.z^2*c.p^2)*sq)
  have hp:=c.p_mem
  have hz:=c.z_mem
  have compare : 1<2*c.p+c.z := by
    by_contra H
    have H' := le_of_not_gt H
    have h0 : c.z≤1-2*c.p := by linarith
    have z2 := pow_le_pow_left₀ hz.1.le h0 2
    have sm := mul_le_mul_of_nonneg_left h0 (show 0≤4*c.p by linarith [hp.1])
    have lg := mul_le_mul_of_nonneg_left z2 (show 0≤3*c.p^2 by positivity)
    nlinarith [c.curve,mul_pos (pow_pos hp.1 3) (sub_pos.mpr hp.2)]
  have smallpos : 0<(1-c.p)/c.h := div_pos (sub_pos.mpr hp.2) hpos
  have ltone : (1-c.p)/c.h<1 := (div_lt_one hpos).mpr (by dsimp [h]; linarith)
  have small : c.ru^2<1 := by
    rw [ru,show c.p-1= -(1-c.p) by ring,neg_div,neg_sq]
    nlinarith [mul_pos (sub_pos.mpr ltone) (show 0<1+(1-c.p)/c.h by linarith)]
  have large : 1<c.Ru := (one_lt_div hpos).mpr (by dsimp [h]; linarith [hz.2])
  have sq3 := Real.sqrt_pos_of_pos (by norm_num : (0:ℝ)<3)
  have uform : c.cu.re=c.z/c.h ∧ c.cu.im=c.z*(Real.sqrt 3*c.p)/c.h := by
    simp [cu,Complex.div_ofReal_re,Complex.div_ofReal_im,Complex.mul_re,Complex.mul_im]
  have zpos := hz.1
  have ppos := hp.1
  have uim : 0<(c.cu^2).im := by
    rw [pow_two,Complex.mul_im,uform.1,uform.2]; positivity
  rw [←Complex.ofReal_pow] at smallrt largert
  have s₁ := (pointsAt c.param).unique_small smallrt rfl (by simpa only [Complex.ofReal_re] using small)
  have s₂ := (pointsAt c.param).unique_large largert rfl (by simpa only [Complex.ofReal_re] using (show 1<c.Ru^2 by nlinarith [sq_nonneg (c.Ru-1)]))
  exact ⟨by exact_mod_cast s₁.symm,by exact_mod_cast s₂.symm,((pointsAt c.param).unique_upper up uim).symm⟩

end Coordinate
end BigDescents132.AllRanks
