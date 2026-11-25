import BigDescents132.FarGeometry

namespace BigDescents132.Slit
open Complex Filter Set
open scoped Topology ComplexConjugate

/-- Squaring removes the principal radicals from the ratio of the real and
complex amplitudes. The large positive root contributes a factor at most one. -/
theorem Points.amplitude_sq_le {s : ℝ} (g : Points s) :
    g.amplitudeRatio^2 ≤ (g.r/‖g.u‖)*(‖(g.r:ℂ)-g.u‖/(8*g.u.im)) := by
  have rs := g.rpos
  have Rs := g.Rpos
  have us := norm_pos_iff.mpr g.u_ne
  have is := g.upper
  have rR := g.small.2.trans g.large.1
  have dr : 0<‖(g.r:ℂ)-g.u‖ := by
    apply norm_pos_iff.mpr
    intro h
    have eq := congrArg Complex.im (sub_eq_zero.mp h)
    simp at eq; linarith
  have dR : g.R-g.r≤‖(g.R:ℂ)-g.u‖ := calc
    _ ≤ g.R-‖g.u‖ := by linarith [g.dominant]
    _ = ‖(g.R:ℂ)‖-‖g.u‖ := by simp [Real.norm_of_nonneg Rs.le]
    _ ≤ _ := norm_sub_norm_le _ _
  have Dr : 0<‖(g.R:ℂ)-g.u‖ := lt_of_lt_of_le (sub_pos.mpr rR) dR
  have sqr {a : ℂ} (ha : a≠0) (z : ℂ) : ‖radical a z‖^2=‖a-z‖/‖a‖ := by
    rw [←norm_pow,radical_sq,←norm_div]
    congr 1; unfold argFactor; field_simp
  have diff : ‖conj g.u-(g.r:ℂ)‖=‖(g.r:ℂ)-g.u‖ := by
    calc
      _ = ‖conj (g.u-(g.r:ℂ))‖ := by simp
      _ = _ := by rw [Complex.norm_conj,norm_sub_rev]
  have ii : ‖conj g.u-g.u‖=2*g.u.im := by
    rw [norm_sub_rev,Complex.sub_conj,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  have re : ‖(g.R:ℂ)-(g.r:ℂ)‖=g.R-g.r := by
    rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_of_nonneg (sub_nonneg.mpr rR.le)]
  have eq : g.amplitudeRatio^2 = ((g.r/‖g.u‖)*(‖(g.r:ℂ)-g.u‖/(8*g.u.im)))*
      ((g.R-g.r)/‖(g.R:ℂ)-g.u‖) := by
    simp only [Points.amplitudeRatio,Points.realOther,Points.rayOther,norm_mul,div_pow,mul_pow,
      sqr (ofReal_ne_zero.mpr rs.ne'),sqr (ofReal_ne_zero.mpr Rs.ne'),sqr g.u_ne,sqr g.cu_ne,
      re,diff,ii,Complex.norm_conj,Complex.norm_real,Real.norm_of_nonneg rs.le,Real.norm_of_nonneg Rs.le]
    rw [norm_sub_rev g.u (g.r:ℂ)]
    field_simp [us.ne',rs.ne',Rs.ne',dr.ne',Dr.ne',is.ne']; ring
  rw [eq]
  apply mul_le_of_le_one_right (by positivity)
  exact (div_le_one Dr).mpr dR

noncomputable def Points.amplitudeBound {s : ℝ} (g : Points s) :=
  (g.r/‖g.u‖)*(‖(g.r:ℂ)-g.u‖/(8*g.u.im))

/-- Absolute error of the normalized oscillatory approximation. -/
noncomputable def coefficientError (p : Param) (n : ℕ) :=
  let g := pointsAt p
  |(B (n+1)).eval (1-p.val)/(2*‖g.complexWeight (n+1)‖*Cut.moment (n+1) 0)-
    Real.cos (g.complexWeight (n+1)).arg|

theorem moving_from_limits {p : ℝ → Param} {h : ℝ → ℝ} (near : Bool)
    (size : ∀ᶠ e in 𝓝[>] (0:ℝ), e≤h e ∧ h e≤1 ∧ (near=true → h e=e))
    {k a b d j : ℝ} (jpos : 0<j)
    (slope : Tendsto (fun e => (pointsAt (p e)).slope*h e) (𝓝[>] 0) (𝓝 k))
    (pole : Tendsto (fun e => (pointsAt (p e)).poleBound) (𝓝[>] 0) (𝓝 a))
    (realPole : Tendsto (fun e => if near then (pointsAt (p e)).nearPole/h e else (pointsAt (p e)).farPole) (𝓝[>] 0) (𝓝 b))
    (ratio : Tendsto (fun e => (pointsAt (p e)).amplitudeBound) (𝓝[>] 0) (𝓝 d))
    (gap : Tendsto (fun e => (pointsAt (p e)).logGap/e) (𝓝[>] 0) (𝓝 j)) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ e in 𝓝[>] (0:ℝ), ∀ n : ℕ, 8≤n+1 → 7≤((n+1:ℕ):ℝ)*e →
      coefficientError (p e) n ≤ C/(((n+1:ℕ):ℝ)*e) := by
  let K := max 1 (k+1)
  let P := max 1 (max (a+1) (b+1))
  let D := 1+max 0 (d+1)
  let c := j/2
  have cpos : 0<c := half_pos jpos
  have k1 : 1≤K := le_max_left _ _
  have k0 := zero_le_one.trans k1
  have p0 : 0≤P := zero_le_one.trans (le_max_left _ _)
  have d0 : 0≤D := by dsimp [D]; positivity
  have err : 0≤cosineError K P := by unfold cosineError; positivity
  refine ⟨28*cosineError K P+6*D*cosineError K P/c^2,by positivity,?_⟩
  filter_upwards [self_mem_nhdsWithin,size,slope.eventually_lt_const (lt_add_one k),
    pole.eventually_lt_const (lt_add_one a),realPole.eventually_lt_const (lt_add_one b),
    ratio.eventually_lt_const (lt_add_one d),gap.eventually_const_lt (half_lt_self jpos)] with e he size sk pa pb rd gj
  have ep : 0<e := he
  have hp := ep.trans_le size.1
  let g := pointsAt (p e)
  have Kbound : g.slope≤K/h e := (le_div_iff₀ hp).mpr (sk.le.trans (le_max_right _ _))
  have Pbound : g.poleBound≤P := pa.le.trans ((le_max_left _ _).trans (le_max_right _ _))
  have rbound : (h e=e ∧ g.nearPole≤P*h e) ∨ g.farPole≤P := by
    cases near with
    | false => exact Or.inr (pb.le.trans ((le_max_right _ _).trans (le_max_right _ _)))
    | true => exact Or.inl ⟨size.2.2 rfl, (div_le_iff₀ hp).mp (pb.le.trans ((le_max_right _ _).trans (le_max_right _ _)))⟩
  have dbound : g.amplitudeRatio≤D := by
    have sq : g.amplitudeRatio^2≤g.amplitudeBound := g.amplitude_sq_le
    have t : g.amplitudeBound≤max 0 (d+1) := rd.le.trans (le_max_right _ _)
    dsimp [D]
    nlinarith [sq_nonneg (g.amplitudeRatio-1)]
  exact fun n hn hu => g.geometry_cosine n hn ep size.1 size.2.1 k1 d0 cpos hu Kbound Pbound rbound dbound
    ((le_div_iff₀ ep).mp gj.le)

end BigDescents132.Slit
