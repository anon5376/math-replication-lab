import BigDescents132.AllRankPolar
import BigDescents132.AllRankBernstein

namespace BigDescents132.AllRanks
open Complex Set Slit

theorem actual_modulus_ratio {p : ℝ} (hp : p∈Ioo 0 1) :
    let c := coordinate p hp
    let g := pointsAt c.param
    g.r/‖g.u‖=(radicalS p+2*p)^2/((1+p)^2*(1+3*p^2)) := by
  let c := coordinate p hp
  let g := pointsAt c.param
  have pos := c.hpos
  have pp := hp.1
  have zz := c.z_mem.1
  have s := (radical_sq hp).1
  have dn : 0<radicalS p+2*p := by linarith
  have one : 0<1+p := by linarith
  have less : 0<1-p := by linarith [hp.2]
  have Q : 0<1+3*p^2 := by positivity
  have rz : c.z=(1-p)*(1+p)/(radicalS p+2*p) := by change (1-p^2)/_=_; ring
  have P : c.p=p := rfl
  change g.r/‖g.u‖=_
  rw [c.small_large_upper.1,c.actual_upper_data.1,Coordinate.ru,P]
  calc
    _ = (p-1)^2/(c.z^2*(1+3*p^2)) := by field_simp [pos.ne',zz.ne',Q.ne']
    _ = _ := by rw [rz]; field_simp [less.ne',one.ne',Q.ne',dn.ne']; ring

theorem actual_gap {p : ℝ} (hp : p∈Ioo 0 1) :
    let c := coordinate p hp
    let g := pointsAt c.param
    1-‖g.u‖/g.r=p*(1-p)*(6*(1+p)^2/((2+radicalS p)*(radicalS p+2*p))) := by
  let c := coordinate p hp
  let g := pointsAt c.param
  have H : g.r/‖g.u‖=(radicalS p+2*p)^2/((1+p)^2*(1+3*p^2)) := actual_modulus_ratio hp
  have z := congrArg (fun x : ℝ => x⁻¹) H
  simp only [inv_div] at z
  change 1-‖g.u‖/g.r=_
  rw [z]
  obtain ⟨rs,sq⟩ := radical_sq hp
  exact normalized_gap hp (by linarith) sq

theorem parameter_injective : Function.Injective
    (fun p : Ioo (0:ℝ) 1 => (coordinate p.val p.property).param) := by
  intro x y e
  have h := congrArg (fun t : Slit.Param => (pointsAt t).u.arg) e
  dsimp only at h
  rw [(coordinate x.val x.property).theta_eq,(coordinate y.val y.property).theta_eq] at h
  have eq : Real.arctan (Real.sqrt 3*x.val)=Real.arctan (Real.sqrt 3*y.val) := by
    change 2*Real.arctan (Real.sqrt 3*x.val)=2*Real.arctan (Real.sqrt 3*y.val) at h
    linarith
  have m := Real.arctan_injective eq
  exact Subtype.ext ((mul_right_inj' (by positivity : Real.sqrt 3≠0)).mp m)

/-- Explicit separation of the actual real and dominant complex branch points. -/
theorem gap_lower_bound {p : ℝ} (hp : p∈Ioo 0 1) :
    let g := pointsAt (coordinate p hp).param
    p*(1-p)*(4/3) ≤ 1-‖g.u‖/g.r := by
  obtain ⟨h,S⟩ := radical_sq hp
  have H := Bernstein.gap_numerator (p:=p) (v:=radicalS p) ⟨hp.1.le,hp.2.le⟩
    (by linarith) (by rw [S]; ring)
  have den : 0<(2+radicalS p)*(radicalS p+2*p) := mul_pos (by linarith) (by linarith [hp.1])
  dsimp only
  rw [actual_gap hp]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hp.1.le (sub_nonneg.mpr hp.2.le))
  exact (le_div_iff₀ den).mpr (by nlinarith only [H])

theorem small_slope_bound {p : ℝ} (hp : p∈Ioo 0 1) (small : p≤1/4) :
    p*(pointsAt (coordinate p hp).param).slope≤7/20 := by
  rw [(coordinate p hp).actual_slope]
  change p*((1+3*p^2)/(2*Real.sqrt 3*p))≤7/20
  have pp := hp.1
  have sr : 0<Real.sqrt 3 := by positivity
  have rt := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  obtain ⟨h,S⟩ := radical_sq hp
  have H := Bernstein.small_slope_numerator (v:=radicalS p) ⟨hp.1.le,small⟩
    (by linarith) (by rw [S];ring)
  have less : 20*(1+3*p^2)≤14*Real.sqrt 3 := by
    by_contra! hh
    nlinarith only [H,rt,pow_le_pow_left₀ (by positivity : 0≤14*Real.sqrt 3) hh.le 2]
  rw [show p*((1+3*p^2)/(2*Real.sqrt 3*p))=(1+3*p^2)/(2*Real.sqrt 3) by field_simp; ring]
  exact (div_le_iff₀ (by positivity)).mpr (by linarith only [less])

theorem regular_slope_bound {p : ℝ} (hp : p∈Ioo 0 1) (regular : 1/4≤p) :
    (pointsAt (coordinate p hp).param).slope≤3/2 := by
  rw [(coordinate p hp).actual_slope]
  change (1+3*p^2)/(2*Real.sqrt 3*p)≤3/2
  have pp := hp.1
  have sr : 0<Real.sqrt 3 := by positivity
  have rt := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  obtain ⟨h,S⟩ := radical_sq hp
  have H := Bernstein.large_slope_numerator (v:=radicalS p) ⟨regular,hp.2.le⟩
    (by linarith) (by rw [S];ring)
  apply (div_le_iff₀ (by positivity)).mpr
  by_contra! hh
  have bad : ((3/2)*(2*Real.sqrt 3*p))^2≤(1+3*p^2)^2 :=
    pow_le_pow_left₀ (by positivity) hh.le 2
  nlinarith only [H,bad,congrArg (fun x : ℝ => x*(9*p^2)) rt]

end BigDescents132.AllRanks
