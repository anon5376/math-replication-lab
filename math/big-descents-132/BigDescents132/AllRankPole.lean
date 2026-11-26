import BigDescents132.AllRankGap
import BigDescents132.AllRankMoments

namespace BigDescents132.AllRanks
open Slit Set Complex

theorem pole_square {s : ℝ} (g : Points s) :
    g.poleBound^2=1+((s⁻¹-g.u.re)/g.u.im)^2 := by
  have sp:=zero_lt_one.trans g.parameter
  have ip:=g.upper
  rw [Points.poleBound,div_pow,Complex.sq_norm,Complex.normSq_apply]
  simp only [Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,Complex.mul_re,
    Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]
  field_simp
  ring

theorem Coordinate.normalized_parts (c : Coordinate) :
    let g:=pointsAt c.param
    let q:=1+3*c.p^2
    c.sVal⁻¹/‖g.u‖=(1-c.p^2)/c.h^2 ∧ g.u.re/‖g.u‖=(1-3*c.p^2)/q ∧
      g.u.im/‖g.u‖=(2*Real.sqrt 3*c.p)/q := by
  obtain ⟨mu,re,im⟩:=c.actual_upper_data
  have hz:=c.z_mem.1
  have hh:=c.hpos
  have Q : 0<1+3*c.p^2 := by positivity
  have pr:=c.prod_pos
  dsimp only
  rw [mu,re,im,Coordinate.sVal,inv_div,Coordinate.prod]
  constructor
  · field_simp;ring
  constructor <;> field_simp <;> ring

private noncomputable def poleH (p v : ℝ) : ℝ :=
  let b:=2*p+v
  let u:= -p^2+p*b+1
  6*p*u^2+(3*p^2+1)*(3*p*(1-p^2)^2-p*b^2+(2-2*p^2)*b)

private noncomputable def U (p v : ℝ) : ℝ := -p^2+p*(2*p+v)+1

theorem algebraic_pole_square {p : ℝ} (hp : p∈Ioo 0 1) :
    let c:=coordinate p hp
    let g:=pointsAt c.param
    let v:=radicalS p
    12*(U p v)^4*g.poleBound^2=12*(U p v)^4+(poleH p v)^2 := by
  let c:=coordinate p hp
  let g:=pointsAt c.param
  let v:=radicalS p
  let b:=2*p+v
  let q:=1+3*p^2
  have pp:=hp.1
  have vv : 0<v := by dsimp [v];linarith [(radical_sq hp).1]
  have bp : 0<b := by dsimp [b];positivity
  have qp : 0<q := by dsimp [q];positivity
  have cp : c.p=p := rfl
  have hpz : 0<c.h := c.hpos
  have zp:=c.z_mem.1
  have ip:=g.upper
  have up:=norm_pos_iff.mpr g.u_ne
  have rp : 0<Real.sqrt 3 := by positivity
  have rt:=Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have zb : 1-p^2=c.z*b := by
    change 1-p^2=(1-p^2)/(v+2*p)*b
    rw [show v+2*p=b by unfold b;ring];field_simp
  have ub : U p v=c.h*b := by
    unfold U Coordinate.h
    rw [cp];change -p^2+p*b+1=(p+c.z)*b
    linarith only [zb]
  obtain ⟨beta,re,im⟩:=c.normalized_parts
  rw [cp] at beta re im
  have E : 1-p^2-c.h^2=p*(2*c.z+3*p*c.z^2-p) := by
    have curve:=c.curve
    rw [cp] at curve
    unfold Coordinate.h;rw [cp]
    linarith only [curve]
  let D:=(c.sVal⁻¹-g.u.re)/g.u.im
  have eq : D*(2*Real.sqrt 3*c.h^2)=(2*c.z+3*p*c.z^2-p)*q+6*p*c.h^2 := by
    have d : D=((c.sVal⁻¹/‖g.u‖)-(g.u.re/‖g.u‖))/(g.u.im/‖g.u‖) := by dsimp [D];rw [←sub_div,div_div_div_cancel_right₀ up.ne']
    rw [d,beta,re,im]
    change (((1-p^2)/c.h^2-(1-3*p^2)/q)/(2*Real.sqrt 3*p/q))*(2*Real.sqrt 3*c.h^2)=_
    calc
      _ = ((1-p^2)*q-(1-3*p^2)*c.h^2)/p := by field_simp;ring
      _ = _ := by
        apply (div_eq_iff pp.ne').mpr
        dsimp [q]
        linear_combination (1+3*p^2)*E
  have ee : D*(2*Real.sqrt 3*(U p v)^2)=poleH p v := by
    have hh : poleH p v=6*p*(c.h*b)^2+q*((2*c.z+3*p*c.z^2-p)*b^2) := by
      unfold poleH
      change 6*p*(U p v)^2+(3*p^2+1)*(3*p*(1-p^2)^2-p*b^2+(2-2*p^2)*b)=_
      rw [ub,show 2-2*p^2=2*(1-p^2) by ring,zb]
      dsimp [q];ring
    rw [hh,ub]
    linear_combination b^2*eq
  change 12*(U p v)^4*g.poleBound^2=_
  rw [pole_square]
  change 12*(U p v)^4*(1+D^2)=_
  rw [←ee]
  linear_combination -(4*(U p v)^4*D^2)*rt

theorem actual_pole_bound {p : ℝ} (hp : p∈Ioo 0 1) :
    (pointsAt (coordinate p hp).param).poleBound≤3/2 := by
  let v:=radicalS p
  obtain ⟨h,sq⟩:=radical_sq hp
  have vp : 0<v := by dsimp [v];linarith
  have q : v^2=-3*p^4+6*p^2+1 := by dsimp [v];linarith
  have B:=Bernstein.pole_numerator ⟨hp.1.le,hp.2.le⟩ vp q
  change 0 < -(poleH p v)^2+15*(U p v)^4 at B
  have H:=algebraic_pole_square hp
  let P:=(pointsAt (coordinate p hp).param).poleBound
  change 12*(U p v)^4*P^2=12*(U p v)^4+(poleH p v)^2 at H
  have up : 0<(U p v)^4 := by nlinarith only [B,sq_nonneg (poleH p v)]
  have lim : P^2≤(3/2:ℝ)^2 := by
    apply le_of_mul_le_mul_left (a:=12*(U p v)^4) _ (by positivity)
    nlinarith only [H,B]
  change P≤3/2
  nlinarith only [lim,sq_nonneg (P-3/2)]

private theorem pole_relations {s : ℝ} (g : Points s) :
    g.nearPole*(g.r/‖g.u‖)=g.poleBound*(g.u.im/‖g.u‖) ∧
    g.farPole*(g.r/‖g.u‖-s⁻¹/‖g.u‖)=g.poleBound*(g.u.im/‖g.u‖) := by
  have s0:=zero_lt_one.trans g.parameter
  have r0:=g.rpos
  have u0:=norm_pos_iff.mpr g.u_ne
  have i0:=g.upper
  have d0:=sub_pos.mpr g.sr_gt
  constructor <;> simp only [Points.nearPole, Points.farPole, Points.poleBound] <;> field_simp <;> ring

private theorem actual_pole_relations {p : ℝ} (hp : p∈Ioo 0 1) :
    let c:=coordinate p hp
    let g:=pointsAt c.param
    let b:=2*p+radicalS p
    let u:=U p (radicalS p)
    let rd:=(1+p)^2*(1+3*p^2)
    let d:=u^2-(1-p^2)*rd
    g.nearPole*b^2=g.poleBound*(2*Real.sqrt 3*p)*(1+p)^2 ∧
    g.farPole*(b^2*d)=g.poleBound*(2*Real.sqrt 3*p)*(1+p)^2*u^2 := by
  let c:=coordinate p hp
  let g:=pointsAt c.param
  let v:=radicalS p
  let b:=2*p+v
  let u:=U p v
  let q:=1+3*p^2
  let rd:=(1+p)^2*q
  let d:=u^2-(1-p^2)*rd
  have pp:=hp.1
  have vv : 0<v := by dsimp [v];linarith [(radical_sq hp).1]
  have bp : 0<b := by dsimp [b];positivity
  have qp : 0<q := by dsimp [q];positivity
  have op : 0<1+p := by linarith
  have dp : 0<rd := by dsimp [rd];positivity
  have hpz:=c.hpos
  have cp : c.p=p := rfl
  have zb : 1-p^2=c.z*b := by
    change 1-p^2=(1-p^2)/(v+2*p)*b
    rw [show v+2*p=b by unfold b;ring];field_simp
  have ub : u=c.h*b := by
    change -p^2+p*b+1=(c.p+c.z)*b
    rw [cp];linarith only [zb]
  have up : 0<u := ub ▸ mul_pos hpz bp
  have rho : g.r/‖g.u‖=b^2/rd := by
    rw [actual_modulus_ratio hp]
    dsimp only [b,v,rd,q];ring
  obtain ⟨beta,_,si⟩:=c.normalized_parts
  have eta : c.sVal⁻¹/‖g.u‖=(1-p^2)*b^2/u^2 := by rw [beta,cp,ub];field_simp;ring
  have im : g.u.im/‖g.u‖=2*Real.sqrt 3*p/q := si
  obtain ⟨nr,fr⟩:=pole_relations g
  change g.farPole*(g.r/‖g.u‖-c.sVal⁻¹/‖g.u‖)=_ at fr
  rw [rho,im] at nr
  rw [rho,eta,im,show b^2/rd-(1-p^2)*b^2/u^2=b^2*d/(rd*u^2) by unfold d;field_simp;ring] at fr
  change g.nearPole*b^2=_ ∧ g.farPole*(b^2*d)=_
  constructor
  · calc
      _ = (g.nearPole*(b^2/rd))*rd := by field_simp
      _ = _ := by rw [nr];dsimp only [rd];field_simp;ring
  · calc
      _ = (g.farPole*(b^2*d/(rd*u^2)))*(rd*u^2) := by field_simp
      _ = _ := by rw [fr];dsimp only [rd];field_simp;ring

theorem actual_near_pole_bound {p : ℝ} (hp : p∈Ioo 0 1) (hl : p≤1/2) :
    (pointsAt (coordinate p hp).param).nearPole≤5*p := by
  let g:=pointsAt (coordinate p hp).param
  let v:=radicalS p
  let b:=2*p+v
  let u:=U p v
  have pp:=hp.1
  have vp : 0<v := by dsimp [v];linarith [(radical_sq hp).1]
  have sq : v^2=-3*p^4+6*p^2+1 := by dsimp [v];linarith [(radical_sq hp).2]
  have br:=Bernstein.near_numerator ⟨hp.1.le,hl⟩ vp sq
  change 0 < -(p+1)^4*((poleH p v)^2+12*u^4)+25*b^4*u^4 at br
  have pl:=algebraic_pole_square hp
  change 12*u^4*g.poleBound^2=12*u^4+(poleH p v)^2 at pl
  rw [add_comm ((poleH p v)^2),←pl] at br
  have bp : 0<b := by dsimp [b];positivity
  have up4 : 0<u^4 := by
    have : 0<1-p^2 := by nlinarith only [mul_pos (sub_pos.mpr hp.2) (show 0<1+p by linarith)]
    have pu : 0<p*b := mul_pos pp bp
    have : 0<u := by change 0 < -p^2+p*b+1;linarith only [this,pu]
    positivity
  have eq:=congrArg (fun t : ℝ => t^2) (actual_pole_relations hp).1
  change (g.nearPole*b^2)^2=(g.poleBound*(2*Real.sqrt 3*p)*(1+p)^2)^2 at eq
  have rt:=Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  simp only [mul_pow,pow_mul] at eq
  rw [rt] at eq
  have lim : g.nearPole^2≤(5*p)^2 := by
    apply le_of_mul_le_mul_right (a:=b^4*u^4) _ (by positivity)
    nlinarith only [mul_nonneg (sq_nonneg p) br.le,congrArg (·*u^4) eq]
  change g.nearPole≤5*p
  exact le_of_sq_le_sq lim (by linarith)

theorem actual_far_pole_bounds {p : ℝ} (hp : p∈Ioo 0 1) (hl : 1/2≤p) :
    let g:=pointsAt (coordinate p hp).param
    g.farPole≤7/2 ∧ (19/20≤p → g.farPole≤6/5) := by
  let g:=pointsAt (coordinate p hp).param
  let v:=radicalS p
  let b:=2*p+v
  let u:=U p v
  let dd:=u^2-(1-p^2)*((p+1)^2*(3*p^2+1))
  have pp:=hp.1
  have vp : 0<v := by dsimp [v];linarith [(radical_sq hp).1]
  have sq : v^2=-3*p^4+6*p^2+1 := by dsimp [v];linarith [(radical_sq hp).2]
  have dp:=Bernstein.far_denominator ⟨hl,hp.2.le⟩ vp sq
  change 0 < -(1-p^2)*(p+1)^2*(3*p^2+1)+u^2 at dp
  have dpos : 0<dd := by dsimp [dd];linarith only [dp]
  have bp : 0<b := by dsimp [b];positivity
  have pl:=algebraic_pole_square hp
  change 12*u^4*g.poleBound^2=12*u^4+(poleH p v)^2 at pl
  have re:= (actual_pole_relations hp).2
  change g.farPole*(b^2*(u^2-(1-p^2)*((1+p)^2*(1+3*p^2))))=_ at re
  rw [add_comm (1:ℝ) p,add_comm (1:ℝ) (3*p^2)] at re
  change g.farPole*(b^2*dd)=g.poleBound*(2*Real.sqrt 3*p)*(p+1)^2*u^2 at re
  have eq:=congrArg (fun t : ℝ => t^2) re
  simp only [mul_pow] at eq
  rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤3)] at eq
  have id : (b^4*dd^2)*g.farPole^2=p^2*(p+1)^4*((poleH p v)^2+12*u^4) := by
    rw [add_comm ((poleH p v)^2),←pl]
    nlinarith only [eq]
  have f:=Bernstein.far_numerator ⟨hl,hp.2.le⟩ vp sq
  have den : 0<b^4*dd^2 := by positivity
  have rewr : -(1-p^2)*(p+1)^2*(3*p^2+1)+u^2=dd := by dsimp [dd];ring
  change 0 < -4*p^2*(p+1)^4*((poleH p v)^2+12*u^4)+49*b^4*(-(1-p^2)*(p+1)^2*(3*p^2+1)+u^2)^2 at f
  rw [rewr] at f
  change g.farPole≤7/2 ∧ _
  constructor
  · apply le_of_sq_le_sq _ (by norm_num)
    apply le_of_mul_le_mul_left (a:=b^4*dd^2) _ den
    rw [id]
    linear_combination (1/4:ℝ)*f.le
  · intro outer
    have f:=Bernstein.outer_numerator ⟨outer,hp.2.le⟩ vp sq
    change 0 < -25*p^2*(p+1)^4*((poleH p v)^2+12*u^4)+36*b^4*(-(1-p^2)*(p+1)^2*(3*p^2+1)+u^2)^2 at f
    rw [rewr] at f
    apply le_of_sq_le_sq _ (by norm_num)
    apply le_of_mul_le_mul_left (a:=b^4*dd^2) _ den
    change b^4*dd^2*g.farPole^2≤_
    rw [id]
    linear_combination (1/25:ℝ)*f.le

end BigDescents132.AllRanks
