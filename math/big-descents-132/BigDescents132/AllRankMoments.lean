import BigDescents132.AllRankCuts

namespace BigDescents132.AllRanks
open Cut

/-- Three normalized beta moments, uniformly up to their sharp leading powers. -/
theorem moments128 {n : ℕ} (hn : 128≤n) :
    moment n 1/moment n 0 ≤ (8/5)/(n:ℝ) ∧
    moment n 2/moment n 0 ≤ (21/5)/(n:ℝ)^2 ∧
    moment n 3/moment n 0 ≤ 15/(n:ℝ)^3 := by
  have big : (128:ℝ)≤n := by exact_mod_cast hn
  have pos : (0:ℝ)<n := by linarith
  have hM (j : ℝ) (hj : j∈Set.Icc (0:ℝ) 3) : 0<moment n j :=
    moment_pos n j (by linarith [hj.1]) (by linarith [hj.2])
  have step (j c : ℝ) (hj : j∈Set.Icc (0:ℝ) 2) (coef : c= (2*j+3)/(2-(2*j+3)/128)) :
      moment n (j+1)≤(c/n)*moment n j := by
    have eqn := moment_step n j (by linarith [hj.1]) (by linarith [hj.2])
    have jm := hM j ⟨hj.1,by linarith [hj.2]⟩
    have den : 0<(2-(2*j+3)/128) := by linarith [hj.2]
    have den' : 0<(n:ℝ)-3/2-j := by linarith [hj.2]
    have jj : 0≤2*j+3 := by linarith [hj.1]
    have bound : (2*j+3)*(n:ℝ) ≤ c*(2*n-3-2*j) := by
      rw [coef,div_mul_eq_mul_div,le_div_iff₀ den]
      nlinarith only [mul_nonneg (sub_nonneg.mpr big) (mul_nonneg jj jj)]
    apply (le_of_mul_le_mul_right (a:=((n:ℝ)-3/2-j)) _ den')
    rw [eqn]
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div,le_div_iff₀ pos]
    nlinarith only [mul_le_mul_of_nonneg_right bound jm.le]
  have h₁ := step 0 (384/253) (by constructor <;> norm_num) (by norm_num)
  have h₂ := step 1 (640/251) (by constructor <;> norm_num) (by norm_num)
  have h₃ := step 2 (896/249) (by constructor <;> norm_num) (by norm_num)
  norm_num at h₁ h₂ h₃
  have m0 := hM 0 (by constructor <;> norm_num)
  have H₂ : moment n 2≤(640/251/n)*(384/253/n)*moment n 0 :=
    h₂.trans ((mul_le_mul_of_nonneg_left h₁ (by positivity)).trans_eq (by ring))
  have H₃ : moment n 3≤(896/249/n)*((640/251/n)*(384/253/n))*moment n 0 :=
    h₃.trans ((mul_le_mul_of_nonneg_left H₂ (by positivity)).trans_eq (by ring))
  refine ⟨(div_le_iff₀ m0).mpr (h₁.trans (mul_le_mul_of_nonneg_right ?_ m0.le)),
    (div_le_iff₀ m0).mpr (H₂.trans (mul_le_mul_of_nonneg_right ?_ m0.le)),
    (div_le_iff₀ m0).mpr (H₃.trans (mul_le_mul_of_nonneg_right ?_ m0.le))⟩
  · exact div_le_div_of_nonneg_right (by norm_num) pos.le
  · rw [div_mul_div_comm,←pow_two]; exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)
  · rw [div_mul_div_comm,div_mul_div_comm,show (n:ℝ)*(n*n)=n^3 by ring]
    exact div_le_div_of_nonneg_right (by norm_num) (pow_nonneg pos.le _)

end BigDescents132.AllRanks

namespace BigDescents132.AllRanks
open Cut Slit

noncomputable def upperError (a : ℝ) := (8/5)*(1/128+7/2*(3/2)*a)+(21/5)*3*a^2+(45/4)*a^3

theorem upperError_mono {a b : ℝ} (ha : 0≤a) (hab : a≤b) : upperError a≤upperError b := by
  unfold upperError; gcongr

theorem normalize_complex {s : ℝ} (g : Points s) {n : ℕ} (hn : 128≤n) (p : g.poleBound≤3/2) :
    ((1+7/2*g.poleBound*g.slope)*moment n 1+2*g.poleBound*g.slope^2*moment n 2+
      g.poleBound/2*g.slope^3*moment n 3)/moment n 0≤upperError (g.slope/n) := by
  have nbig : (128:ℝ)≤n := by exact_mod_cast hn
  have np : 0<(n:ℝ) := by linarith
  have sp := zero_le_one.trans g.slope_ge_one
  have pp := g.poleBound_pos.le
  obtain ⟨one,two,three⟩ := moments128 hn
  simp only [add_div,mul_div_assoc]
  calc
    _ ≤ (1+7/2*(3/2)*g.slope)*((8/5)/n)+2*(3/2)*g.slope^2*((21/5)/(n:ℝ)^2)+
        ((3/2)/2*g.slope^3)*(15/(n:ℝ)^3) := by
      gcongr <;> first | assumption | positivity | exact div_nonneg (moment_pos n _ (by norm_num) (by linarith)).le (moment_pos n _ (by norm_num) (by linarith)).le
    _ = (8/5)*((n:ℝ)⁻¹+7/2*(3/2)*(g.slope/n))+(21/5)*3*(g.slope/n)^2+(45/4)*(g.slope/n)^3 := by ring
    _ ≤ _ := by
      unfold upperError
      have h : (n:ℝ)⁻¹≤1/128 := by simpa only [one_div] using inv_anti₀ (by norm_num : (0:ℝ)<128) nbig
      linarith only [h]

/-- This range needs no damping and imposes no lower bound on the distance
of the parameter from the far endpoint. -/
theorem far_uniform_strict {s : ℝ} (g : Points s) (n : ℕ) (hn : 128≤n+1)
    (P : g.poleBound≤3/2) (S : g.slope≤3/2) (A : g.amplitudeRatio≤5/8)
    (F : g.farPole≤6/5) :
    |(B (n+1)).eval (1-s)/(2*‖g.complexWeight (n+1)‖*moment (n+1) 0)-
      Real.cos (g.complexWeight (n+1)).arg|<1 := by
  let N := n+1
  let M := moment N
  have H : (128:ℝ)≤N := by exact_mod_cast hn
  have np : 0<(N:ℝ) := by linarith
  have s0 := zero_le_one.trans g.slope_ge_one
  have a0 : 0≤g.amplitudeRatio := by dsimp [Points.amplitudeRatio]; positivity
  have fp : 0≤g.farPole := div_nonneg (norm_nonneg _) (sub_pos.mpr g.sr_gt).le
  have r0 := div_nonneg (norm_nonneg g.u) g.rpos.le
  have r1 := (div_le_one g.rpos).mpr g.dominant.le
  have hpow : (‖g.u‖/g.r)^(N+1)≤1 := pow_le_one₀ r0 r1
  have damp : g.amplitudeRatio*(‖g.u‖/g.r)^(N+1) ≤ 5/8 :=
    (mul_le_of_le_one_right a0 hpow).trans A
  have dd : 0≤g.amplitudeRatio*(‖g.u‖/g.r)^(N+1) := mul_nonneg a0 (pow_nonneg r0 _)
  have bound : g.slope/(N:ℝ)≤(3/2)/128 :=
    (div_le_div_of_nonneg_right S np.le).trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) H)
  have cu := (normalize_complex g hn P).trans (upperError_mono (div_nonneg s0 np.le) bound)
  have mpos : 0≤M 1/M 0 := div_nonneg (moment_pos N 1 (by norm_num) (by linarith)).le (moment_pos N 0 (by norm_num) (by linarith)).le
  have mlim : M 1/M 0≤(8/5)/128 := (moments128 hn).1.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) H)
  have realBound : g.farPole*(1+(1+g.slope)*(M 1/M 0))≤(6/5)*(1+(5/2)*((8/5)/128)) := by
    gcongr; first | exact F | exact mlim | linarith
  have re := (mul_le_mul_of_nonneg_left (min_le_right (g.nearPole*((2*N:ℝ)+g.slope))
    (g.farPole*(1+(1+g.slope)*(M 1/M 0)))) dd).trans
      (mul_le_mul damp realBound (by positivity) (by norm_num))
  exact (contour_error g n (by omega)).trans_lt ((add_le_add cu re).trans_lt (by norm_num [upperError]))

end BigDescents132.AllRanks
