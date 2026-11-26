import BigDescents132.AllRankAmplitude

namespace BigDescents132.AllRanks
open Slit Cut Set

private theorem damping_bound {q T : ℝ} (qp : 0≤q) (qu : q≤1) (N : ℕ) (bound : T≤(N:ℝ)*(1-q)) :
    q^(N+1)≤1/Real.exp T := by
  calc
    _ ≤ q^N := by rw [pow_succ];exact mul_le_of_le_one_right (pow_nonneg qp _) qu
    _ ≤ (Real.exp (q-1))^N := pow_le_pow_left₀ qp (by linarith only [Real.add_one_le_exp (q-1)]) N
    _ = Real.exp ((N:ℝ)*(q-1)) := (Real.exp_nat_mul ..).symm
    _ ≤ Real.exp (-T) := Real.exp_le_exp.mpr (by linarith only [bound])
    _ = _ := by rw [Real.exp_neg,one_div]

private theorem affine_damping {T t c a K : ℝ} (big : t≤T) (ap : 0<a) (kp : 0<K)
    (start : K≤Real.exp (a*t)) (slope : 2≤a*(2*t+c)) (positive : 0≤2*t+c) :
    (2*T+c)/Real.exp (a*T) ≤ (2*t+c)/K := by
  have dx : 0≤a*(T-t) := mul_nonneg ap.le (sub_nonneg.mpr big)
  have exp := Real.add_one_le_exp (a*(T-t))
  have E : K*(a*(T-t)+1)≤Real.exp (a*T) := by
    rw [show a*T=a*t+a*(T-t) by ring,Real.exp_add]
    exact mul_le_mul start exp (by linarith) (Real.exp_pos _).le
  apply (div_le_div_iff₀ (Real.exp_pos _) kp).mpr
  calc
    _ ≤ (2*t+c)*(K*(a*(T-t)+1)) := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr slope) (mul_nonneg kp.le (sub_nonneg.mpr big))]
    _ ≤ _ := mul_le_mul_of_nonneg_left E positive

noncomputable def actualError {s : ℝ} (g : Points s) (N : ℕ) :=
  |(B N).eval (1-s)/(2*‖g.complexWeight N‖*moment N 0)-Real.cos (g.complexWeight N).arg|

private theorem error_near {s : ℝ} (g : Points s) (n : ℕ) (hn : 128≤n+1)
    (P : g.poleBound≤3/2) (A : g.amplitudeRatio≤5/8) {a L E : ℝ}
    (S : g.slope/(n+1:ℕ)≤a) (V : g.nearPole*((2*(n+1:ℕ):ℝ)+g.slope)≤L)
    (D : (‖g.u‖/g.r)^((n+1)+1)≤1/Real.exp E) :
    actualError g (n+1)≤upperError a+(5/8)*L/Real.exp E := by
  let N:=n+1
  have np : (0:ℝ)<N := by exact_mod_cast (show 0<N by dsimp [N];omega)
  have sc:=g.slope_ge_one
  have a0 : 0≤g.amplitudeRatio := by unfold Points.amplitudeRatio;positivity
  have v0 : 0≤g.nearPole := by unfold Points.nearPole;exact div_nonneg (norm_nonneg _) (mul_nonneg (zero_lt_one.trans g.parameter).le g.rpos.le)
  have pow0 : 0≤(‖g.u‖/g.r)^(N+1) := pow_nonneg (div_nonneg (norm_nonneg _) g.rpos.le) _
  have upper := (normalize_complex g hn P).trans (upperError_mono (div_nonneg (by linarith) np.le) S)
  have h:=contour_error g n (by omega)
  apply h.trans (add_le_add upper ?_)
  have vlim : 0≤g.nearPole*((2*N:ℝ)+g.slope) := mul_nonneg v0 (by linarith)
  apply (mul_le_mul_of_nonneg_left (min_le_left _ _) (mul_nonneg a0 pow0)).trans
  calc
    _ ≤ ((5/8)*(1/Real.exp E))*L := mul_le_mul (mul_le_mul A D pow0 (by norm_num)) V vlim (by positivity)
    _ = _ := by ring

private theorem error_far {s : ℝ} (g : Points s) (n : ℕ) (hn : 128≤n+1)
    (P : g.poleBound≤3/2) (A : g.amplitudeRatio≤5/8) (S : g.slope≤3/2)
    {f d : ℝ} (V : g.farPole≤f) (df : 0≤d) (D : (‖g.u‖/g.r)^((n+1)+1)≤d) :
    actualError g (n+1)≤upperError ((3/2)/128)+(5/8)*d*(f*(1+(5/2)*((8/5)/128))) := by
  let N:=n+1
  have nb : (128:ℝ)≤N := by exact_mod_cast hn
  have np : (0:ℝ)<N := by linarith
  have sc:=g.slope_ge_one
  have a0 : 0≤g.amplitudeRatio := by unfold Points.amplitudeRatio;positivity
  have fp : 0≤g.farPole := div_nonneg (norm_nonneg _) (sub_pos.mpr g.sr_gt).le
  have pow0 : 0≤(‖g.u‖/g.r)^(N+1) := pow_nonneg (div_nonneg (norm_nonneg _) g.rpos.le) _
  have mm : 0≤moment N 1/moment N 0 := div_nonneg (moment_pos N 1 (by norm_num) (by linarith)).le (moment_pos N 0 (by norm_num) (by linarith)).le
  have uu := (normalize_complex g hn P).trans (upperError_mono (div_nonneg (by linarith) np.le)
    ((div_le_div_of_nonneg_right S np.le).trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) nb)))
  have mlim : moment N 1/moment N 0≤(8/5)/128 := (moments128 hn).1.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) nb)
  have rv : g.farPole*(1+(1+g.slope)*(moment N 1/moment N 0))≤f*(1+(5/2)*((8/5)/128)) := by
    gcongr <;> first | exact V | exact mlim | linarith
  have h:=contour_error g n (by omega)
  apply h.trans (add_le_add uu ?_)
  apply (mul_le_mul_of_nonneg_left (min_le_right _ _) (mul_nonneg a0 pow0)).trans
  exact mul_le_mul (mul_le_mul A D pow0 (by norm_num)) rv
    (mul_nonneg fp (by nlinarith only [mul_nonneg (show 0≤1+g.slope by linarith) mm])) (by positivity)

/-- Strict uniform error on the whole moving interior, including parameters arbitrarily close to one. -/
theorem four_ranges {p : ℝ} (hp : p∈Ioo 0 1) (n : ℕ) (hn : 128≤n+1) (moving : 5≤((n+1:ℕ):ℝ)*p) :
    actualError (pointsAt (coordinate p hp).param) (n+1)<1 := by
  let g:=pointsAt (coordinate p hp).param
  let N:=n+1
  let T:=(N:ℝ)*p
  let u:=‖g.u‖/g.r
  have nb : (128:ℝ)≤N := by exact_mod_cast hn
  have np : (0:ℝ)<N := by linarith
  have pp:=hp.1
  have t0 : 5≤T := moving
  have u0 : 0≤u := div_nonneg (norm_nonneg _) g.rpos.le
  have u1 : u≤1 := (div_le_one g.rpos).mpr g.dominant.le
  have gap : p*(1-p)*(4/3)≤1-u := gap_lower_bound hp
  have damp (E : ℝ) (h : E≤(N:ℝ)*(p*(1-p)*(4/3))) : u^(N+1)≤1/Real.exp E :=
    damping_bound u0 u1 N (h.trans (mul_le_mul_of_nonneg_left gap np.le))
  have P : g.poleBound≤3/2 := actual_pole_bound hp
  have A : g.amplitudeRatio≤5/8 := actual_amplitude_bound hp
  have vs (p2 : p≤1/2) {C : ℝ} (S : p*g.slope≤C) :
      g.nearPole*((2*N:ℝ)+g.slope)≤5*(2*T+C) := by
    calc
      _ ≤ 5*p*((2*N:ℝ)+g.slope) := mul_le_mul_of_nonneg_right (actual_near_pole_bound hp p2) (by linarith [g.slope_ge_one])
      _ ≤ _ := by dsimp [T];linarith only [S]
  by_cases p1 : p≤1/4
  · have sl : p*g.slope≤7/20 := small_slope_bound hp p1
    have bound : g.slope/(N:ℝ)≤(7/20)/5 := by
      apply (div_le_iff₀ np).mpr
      apply le_of_mul_le_mul_left (a:=p) _ pp
      dsimp [T] at t0;nlinarith only [sl,t0]
    have dc:=damp T (by dsimp [T];nlinarith only [mul_nonneg (mul_nonneg np.le pp.le) (sub_nonneg.mpr p1)])
    have ex : (130:ℝ)≤Real.exp 5 := by
      apply le_trans _ (Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤5) 9)
      norm_num [Finset.sum_range_succ,Nat.factorial]
    have rate:=affine_damping (a:=1) (K:=130) (c:=7/20) t0 (by norm_num) (by norm_num) (by simpa using ex) (by norm_num) (by norm_num)
    rw [one_mul] at rate
    have h:=error_near g n hn P A bound (vs (by linarith) sl) dc
    calc
      _ ≤ _ := h
      _ ≤ upperError ((7/20)/5)+(5/8)*5*((2*5+7/20)/130) := by linear_combination (25/8:ℝ)*rate
      _ < 1 := by norm_num [upperError]
  have reg : g.slope≤3/2 := regular_slope_bound hp (le_of_not_ge p1)
  by_cases p2 : p≤1/2
  · have sb : g.slope/(N:ℝ)≤(3/2)/128 := (div_le_div_of_nonneg_right reg np.le).trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) nb)
    have T32 : 32≤T := by dsimp [T];nlinarith only [mul_le_mul nb (le_of_not_ge p1) (by norm_num) np.le]
    have dc:=damp ((2/3)*T) (by dsimp [T];nlinarith only [mul_nonneg (mul_nonneg np.le pp.le) (sub_nonneg.mpr p2)])
    have sl : p*g.slope≤3/4 := by nlinarith only [mul_le_mul p2 reg (by linarith [g.slope_ge_one]) (by norm_num)]
    have ex : (1024:ℝ)≤Real.exp ((2/3)*32) := by
      apply le_trans _ (Real.pow_div_factorial_le_exp ((2/3)*32) (by norm_num) 4)
      norm_num [Nat.factorial]
    have rate:=affine_damping (a:=2/3) (K:=1024) (c:=3/4) T32 (by norm_num) (by norm_num) ex (by norm_num) (by norm_num)
    have h:=error_near g n hn P A sb (vs p2 sl) dc
    calc
      _ ≤ _ := h
      _ ≤ upperError ((3/2)/128)+(5/8)*5*((2*32+3/4)/1024) := by linear_combination (25/8:ℝ)*rate
      _ < 1 := by norm_num [upperError]
  have far:=actual_far_pole_bounds hp (le_of_not_ge p2)
  by_cases p3 : p≤19/20
  · have lo : 4≤(N:ℝ)*(p*(1-p)*(4/3)) := by
      have hi : 1/20≤1-p := by linarith
      have mid : (1/2:ℝ)*(1/20)≤p*(1-p) := mul_le_mul (le_of_not_ge p2) hi (by norm_num) pp.le
      nlinarith only [mul_le_mul nb mid (by norm_num) np.le]
    have dc : u^(N+1)≤1/5 := (damp 4 lo).trans (one_div_le_one_div_of_le (by norm_num) (by linarith only [Real.add_one_le_exp 4]))
    exact (error_far g n hn P A reg far.1 (by norm_num) dc).trans_lt (by norm_num [upperError])
  exact far_uniform_strict g n hn P reg A (far.2 (le_of_not_ge p3))

end BigDescents132.AllRanks
