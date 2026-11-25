import BigDescents132.RealBounds

namespace BigDescents132.Slit
open Complex Filter Set
open scoped Topology

variable {s : ℝ} (g : Points s)

noncomputable def Points.amplitudeRatio :=
  ‖g.realOther g.r‖/(2*‖g.rayOther g.u g.u‖)
noncomputable def Points.logGap := Real.log (g.r/‖g.u‖)

theorem Points.logGap_pos : 0<g.logGap :=
  Real.log_pos ((one_lt_div (norm_pos_iff.mpr g.u_ne)).mpr g.dominant)

private theorem damping {c E D : ℝ} (hd : g.amplitudeRatio≤D) (gap : c*E≤g.logGap) (N : ℕ) :
    |g.scaledReal N|≤D*Real.exp (-(c*((N:ℝ)*E))) := by
  let q := ‖g.u‖/g.r
  have rpos := g.rpos
  have up := norm_pos_iff.mpr g.u_ne
  have qp : 0<q := div_pos up rpos
  have qone : q≤1 := ((div_lt_one rpos).mpr g.dominant).le
  have dq : q^N=Real.exp ((N:ℝ)*Real.log q) := by rw [Real.exp_nat_mul,Real.exp_log qp]
  have lq : Real.log q= -g.logGap := by
    simp [q,Points.logGap,Real.log_div up.ne' rpos.ne',Real.log_div rpos.ne' up.ne']
  have bnd : q^(N+1)≤Real.exp (-(c*((N:ℝ)*E))) := by
    calc
      q^(N+1) ≤ q^N := by rw [pow_succ]; exact mul_le_of_le_one_right (pow_nonneg qp.le _) qone
      _ = _ := dq
      _ ≤ _ := by rw [lq]; apply Real.exp_le_exp.mpr; nlinarith only [mul_le_mul_of_nonneg_left gap (Nat.cast_nonneg (α:=ℝ) N)]
  have hn : 0≤g.amplitudeRatio := by dsimp [Points.amplitudeRatio]; positivity
  rw [g.scaled_real_size]
  exact mul_le_mul hd bnd (pow_nonneg qp.le _) (hn.trans hd)

noncomputable def cosineError (K P : ℝ) := (3*P*K^3+P*K+1)+(1+K)*P

/-- Scalar inequalities on the four actual branch points imply an interior
error bound for the literal coefficient, including both radial multipliers,
the positive-axis pole and the real-cut damping. -/
theorem Points.geometry_cosine (n : ℕ) (hn : 8≤n+1) {h E K P D c : ℝ}
    (hE : 0<E) (hEh : E≤h) (h1 : h≤1) (hK : 1≤K) (hD : 0≤D) (hc : 0<c)
    (hu : 7≤((n+1:ℕ):ℝ)*E)
    (slope : g.slope≤K/h) (pole : g.poleBound≤P)
    (realPole : (h=E ∧ g.nearPole≤P*h) ∨ g.farPole≤P)
    (ratio : g.amplitudeRatio≤D) (gap : c*E≤g.logGap) :
    |(B (n+1)).eval (1-s)/(2*‖g.complexWeight (n+1)‖*Cut.moment (n+1) 0)-
      Real.cos (g.complexWeight (n+1)).arg|≤
      (28*cosineError K P+6*D*cosineError K P/c^2)/(((n+1:ℕ):ℝ)*E) := by
  have hp := g.poleBound_pos.trans_le pole
  have hh := hE.trans_le hEh
  have k0 : 0≤K := zero_le_one.trans hK
  have u0 : 0≤3*P*K^3+P*K+1 := by positivity
  have r0 : 0≤(1+K)*P := by positivity
  have K0 : 0≤cosineError K P := add_nonneg u0 r0
  have Rle : (1+K)*P≤cosineError K P := le_add_of_nonneg_left u0
  apply g.scaled_moving_cosine n hn hE hEh K0 hD hc hu _ _ (damping g ratio gap _)
  · intro v hv
    have vp : 0≤v := (show 0<v from hv).le
    have hl : 3*g.poleBound*K^3+g.poleBound*K+1≤3*P*K^3+P*K+1 := by gcongr
    have H := g.upper_bound hh h1 hK slope vp
    exact H.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (hl.trans (le_add_of_nonneg_right r0)) (div_nonneg vp hh.le)) (sq_nonneg _))
  · have shape (v : ℝ) (vp : 0<v) :
        1+(1+g.slope)*v≤(1+K)*(1+v/h)^2 := by
      have t := div_nonneg vp.le hh.le
      have vh : v≤v/h := (le_div_iff₀ hh).mpr (by nlinarith [mul_nonneg vp.le (sub_nonneg.mpr h1)])
      have s : g.slope*v≤K*(v/h) := (mul_le_mul_of_nonneg_right slope vp.le).trans_eq (by ring)
      have quad : 1+v/h≤(1+v/h)^2 := by nlinarith [sq_nonneg (v/h)]
      apply le_trans _ (mul_le_mul_of_nonneg_left quad (by positivity))
      linarith
    rcases realPole with ⟨he,ps⟩|ps
    · refine Or.inl ⟨he,fun v hv => ?_⟩
      have vp := hv.1
      have p := div_le_div_of_nonneg_right ps vp.le
      have npe : 0≤g.nearPole := by dsimp [Points.nearPole]; exact div_nonneg (norm_nonneg _) (mul_nonneg (zero_lt_one.trans g.parameter).le g.rpos.le)
      calc
        _ ≤ (1+(1+g.slope)*v)*(g.nearPole/v) := (g.real_bounds hv).1
        _ ≤ ((1+K)*(1+v/h)^2)*(P*h/v) := mul_le_mul (shape v vp) p (div_nonneg npe vp.le) (by positivity)
        _ = ((1+K)*P)*(h/v)*(1+v/h)^2 := by ring
        _ ≤ _ := by gcongr
    · refine Or.inr (fun v hv => ?_)
      have fp : 0≤g.farPole := div_nonneg (norm_nonneg _) (sub_nonneg.mpr g.sr_gt.le)
      calc
        _ ≤ (1+(1+g.slope)*v)*g.farPole := (g.real_bounds hv).2
        _ ≤ ((1+K)*(1+v/h)^2)*P := mul_le_mul (shape v hv.1) ps fp (by positivity)
        _ = ((1+K)*P)*(1+v/h)^2 := by ring
        _ ≤ _ := by gcongr

/-- At every fixed negative real parameter the oscillatory approximation for
the literal permutations has an O(1/N) error, with an explicit quantifier. -/
theorem Points.fixed_error {s : ℝ} (g : Points s) :
    ∃ C : ℝ, 0≤C ∧ ∀ n : ℕ, 8≤n+1 →
      |(B (n+1)).eval (1-s)/(2*‖g.complexWeight (n+1)‖*Cut.moment (n+1) 0)-
        Real.cos (g.complexWeight (n+1)).arg|≤C/((n+1:ℕ):ℝ) := by
  let K := g.slope
  let P := max g.poleBound g.farPole
  let D := g.amplitudeRatio
  let c := g.logGap
  have k0 := zero_le_one.trans g.slope_ge_one
  have p0 : 0≤P := g.poleBound_pos.le.trans (le_max_left _ _)
  have d0 : 0≤D := by dsimp [D,Points.amplitudeRatio]; positivity
  have cp : 0<c := g.logGap_pos
  have b0 : 0≤cosineError K P := by dsimp [cosineError,K]; positivity
  refine ⟨28*cosineError K P+6*D*cosineError K P/c^2,by positivity,fun n hn => ?_⟩
  have hv : 7≤((n+1:ℕ):ℝ)*1 := by rw [mul_one]; exact_mod_cast (show 7≤n+1 by omega)
  simpa only [mul_one] using g.geometry_cosine n hn zero_lt_one (le_rfl : (1:ℝ)≤1) (le_rfl) g.slope_ge_one
    d0 cp hv (by simp [K]) (le_max_left _ _) (Or.inr (le_max_right _ _)) le_rfl (by simp [c])

end BigDescents132.Slit
