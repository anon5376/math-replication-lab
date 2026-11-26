import BigDescents132.AllRankPole

namespace BigDescents132.AllRanks
open Slit Set Complex

theorem actual_amplitude_bound {p : ℝ} (hp : p∈Ioo 0 1) :
    (pointsAt (coordinate p hp).param).amplitudeRatio≤5/8 := by
  let c:=coordinate p hp
  let g:=pointsAt c.param
  let v:=radicalS p
  let b:=2*p+v
  let q:=1+3*p^2
  let rd:=(1+p)^2*q
  let rho:=g.r/‖g.u‖
  let J:=(g.r-g.u.re)/g.u.im
  let D:=‖(g.r:ℂ)-g.u‖/g.u.im
  have pp:=hp.1
  have vp : 0<v := by dsimp [v];linarith [(radical_sq hp).1]
  have rp : 0<2+v := by linarith
  have bpos : 0<b := by dsimp [b];positivity
  have qp : 0<q := by dsimp [q];positivity
  have op : 0<1+p := by linarith
  have rdpos : 0<rd := by dsimp [rd];positivity
  have mup:=norm_pos_iff.mpr g.u_ne
  have rr:=g.rpos
  have ip:=g.upper
  have ipr : 0<Real.sqrt 3 := by positivity
  have sqv : v^2=-3*p^4+6*p^2+1 := by dsimp [v];linarith [(radical_sq hp).2]
  have r3:=Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have rdef : rho=b^2/rd := by rw [show rho=g.r/‖g.u‖ by rfl,actual_modulus_ratio hp];dsimp [b,rd,v,q];ring
  have gap:=actual_gap hp
  change 1-‖g.u‖/g.r=p*(1-p)*(6*(1+p)^2/((2+v)*(v+2*p))) at gap
  rw [add_comm v (2*p)] at gap
  have rel : (rho-1)*q=p*(1-p)*6*b/(2+v) := by
    calc
      _ = rho*(1-‖g.u‖/g.r)*q := by dsimp [rho];field_simp;ring
      _ = _ := by rw [gap,rdef];dsimp only [rd];change b^2/((1+p)^2*q)*(p*(1-p)*(6*(1+p)^2/((2+v)*b)))*q=_;field_simp;ring
  obtain ⟨_,re,im⟩:=c.normalized_parts
  have reu : g.u.re/‖g.u‖=(1-3*p^2)/q := re
  have imu : g.u.im/‖g.u‖=2*Real.sqrt 3*p/q := im
  have JR : J*(2*Real.sqrt 3*(2+v))=6*(v+4*p-2*p^2) := by
    have jdef : J=(rho-g.u.re/‖g.u‖)/(g.u.im/‖g.u‖) := by dsimp [J,rho];rw [←sub_div,div_div_div_cancel_right₀ mup.ne']
    have red : J*(2*Real.sqrt 3*p)=(rho-1)*q+6*p^2 := by
      rw [jdef,reu,imu]
      calc
        _ = rho*q-(1-3*p^2) := by field_simp
        _ = _ := by dsimp [q];ring
    rw [rel] at red
    apply le_antisymm <;> apply le_of_mul_le_mul_right (a:=p) _ pp
    all_goals have z:=congrArg (·*(2+v)) red
    all_goals dsimp only at z
    all_goals rw [add_mul,div_mul_cancel₀ _ rp.ne'] at z
    all_goals dsimp only [b] at z; linarith only [z]
  have ds : D^2=1+J^2 := by
    dsimp [D,J]
    rw [div_pow,Complex.sq_norm,Complex.normSq_apply]
    simp only [Complex.sub_re,Complex.ofReal_re,Complex.sub_im,Complex.ofReal_im,zero_sub,neg_mul_neg]
    field_simp;ring
  have j2:=congrArg (fun t : ℝ => t^2) JR
  simp only [mul_pow] at j2
  rw [r3] at j2
  have id : 12*(2+v)^2*D^2=12*(2+v)^2+36*(v+4*p-2*p^2)^2 := by rw [ds];nlinarith only [j2]
  have B:=Bernstein.amplitude_numerator ⟨hp.1.le,hp.2.le⟩ vp sqv
  have raw : 0<480000*rd^2*(2+v)^2-4096*b^4*(12*(2+v)^2+36*(v+4*p-2*p^2)^2) := by
    change 0 < 480000*(p+1)^4*(3*p^2+1)^2*(v+2)^2-4096*b^4*(12*(v+2)^2+36*(-2*p^2+4*p+v)^2) at B
    dsimp only [rd,q]
    linarith only [B]
  rw [←id] at raw
  have prod : rho*D≤25/8 := by
    apply le_of_sq_le_sq _ (by norm_num)
    rw [rdef,mul_pow,div_pow]
    apply le_of_mul_le_mul_right (a:=rd^2*(2+v)^2) _ (by positivity)
    calc
      _ = b^4*D^2*(2+v)^2 := by field_simp;ring
      _ ≤ _ := by linear_combination (1/49152:ℝ)*raw.le
  change g.amplitudeRatio≤5/8
  apply le_of_sq_le_sq _ (by norm_num)
  apply g.amplitude_sq_le.trans
  change rho*(‖(g.r:ℂ)-g.u‖/(8*g.u.im)) ≤ _
  calc
    _ = rho*D/8 := by dsimp [D];ring
    _ ≤ _ := by linarith only [prod]

end BigDescents132.AllRanks
