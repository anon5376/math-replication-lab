import BigDescents132.AllRankGap

namespace BigDescents132.AllRanks
open Set Slit

theorem Coordinate.scale_identity (c : Coordinate) :
    (c.sVal-1)/c.p^3 =
      (c.p+4*c.z+3*c.p*c.z^2)*(1+3*c.z^2)/
      ((c.z+4*c.p+3*c.p^2*c.z)*(1+3*c.p^2)*c.z^3) := by
  have pc := c.p_mem.1
  have zc := c.z_mem.1
  have pp := c.prod_pos
  have az : 1-c.z^2=c.p*(c.p+4*c.z+3*c.p*c.z^2) := by nlinarith only [c.curve]
  have ap : 1-c.p^2=c.z*(c.z+4*c.p+3*c.p^2*c.z) := by nlinarith only [c.curve]
  have comp : c.h^4-c.prod=(1-c.z^2)*c.p^2*(1+3*c.z^2) := by
    unfold Coordinate.h Coordinate.prod
    linarith only [reciprocal_complement c.p c.z c.curve]
  rw [Coordinate.sVal,div_sub_one pp.ne',comp,Coordinate.prod,az,ap]
  have hd : 0<c.z+4*c.p+3*c.p^2*c.z := by positivity
  have hq : 0<1+3*c.p^2 := by positivity
  field_simp [pc.ne',zc.ne',hd.ne',hq.ne']
  ring

theorem small_scale_bounds {p : ℝ} (hp : p∈Ioo 0 1) (small : p≤1/16) :
    let c := coordinate p hp
    15≤(c.sVal-1)/p^3 ∧ (c.sVal-1)/p^3≤20 := by
  let c := coordinate p hp
  change 15≤(c.sVal-1)/c.p^3 ∧ (c.sVal-1)/c.p^3≤20
  rw [c.scale_identity]
  have cz := c.z_mem.1
  have cp := hp.1
  have P : c.p=p := rfl
  obtain ⟨h,S⟩ := radical_sq hp
  let v := radicalS p
  have hv : 0<v := by dsimp [v];linarith
  have sq : v^2=-3*p^4+6*p^2+1 := by rw [show v=radicalS p by rfl,S];ring
  have lo := Bernstein.scale_lower_numerator (p:=p) ⟨hp.1.le,small⟩ hv sq
  have hi := Bernstein.scale_upper_numerator (p:=p) ⟨hp.1.le,small⟩ hv sq
  let b := 2*p+v
  have bp : 0<b := by dsimp [b];positivity
  have zb : 1-p^2=c.z*b := by
    change 1-p^2=(1-p^2)/(radicalS p+2*p)*b
    rw [show radicalS p+2*p=b by dsimp [b,v];ring]
    field_simp
  rw [P]
  have dn : 0<(c.z+4*p+3*p^2*c.z)*(1+3*p^2)*c.z^3 := by positivity
  rw [le_div_iff₀ dn,div_le_iff₀ dn]
  change 0 < -15*(1-p^2)^3*(3*p^2+1)*(3*p^2*(1-p^2)-p^2+4*p*b+1)+
    (3*(1-p^2)^2+b^2)*(3*p*(1-p^2)^2+p*b^2+(4-4*p^2)*b) at lo
  change 0 < 20*(1-p^2)^3*(3*p^2+1)*(3*p^2*(1-p^2)-p^2+4*p*b+1)-
    (3*(1-p^2)^2+b^2)*(3*p*(1-p^2)^2+p*b^2+(4-4*p^2)*b) at hi
  have z4 : 4-4*p^2=4*(c.z*b) := by rw [←zb];ring
  have z1 : ∀ i : ℝ, 3*p^2*(1-p^2)-p^2+i+1=3*p^2*(c.z*b)+c.z*b+i := by
    intro i;rw [←zb];ring
  rw [z1,zb,z4] at lo hi
  constructor
  · apply le_of_mul_le_mul_right (a:=b^4) _ (pow_pos bp _)
    nlinarith only [lo]
  · apply le_of_mul_le_mul_right (a:=b^4) _ (pow_pos bp _)
    nlinarith only [hi]

end BigDescents132.AllRanks
