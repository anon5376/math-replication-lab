import BigDescents132.RealCut
import BigDescents132.CutMultiplier

namespace BigDescents132.Cut
open Real Complex Set MeasureTheory

/-- A conjugate pair of cuts, combined by taking a real part, plus the
truncated positive cut. All three contributions are normalized by W_n. -/
noncomputable def normalizedCuts (n : ℕ) (q : ℂ) (b T : ℝ) (U V : ℝ → ℂ) : ℝ :=
  (q*((∫ v in Ioi (0:ℝ), kernel n v • U v)/(moment n 0:ℂ))).re +
    b*(∫ v in Ioo (0:ℝ) T, kernel n v • V v).re/moment n 0

/-- Uniform moving-interior estimate for the explicit cut expression. For a
coefficient application the branch geometry must supply the multiplier
bounds and the exact equality with the normalized coefficient. -/
theorem moving_cut_cosine {n : ℕ} (hn : 8≤n) {h E K D c θ b T : ℝ}
    (hE : 0<E) (hEh : E≤h) (hK : 0≤K) (hD : 0≤D) (hc : 0<c) (hu : 7≤(n:ℝ)*E)
    (q : ℂ) (hq : ‖q‖=1) (hphase : q.re=Real.cos θ)
    (U V : ℝ → ℂ) (hU : ContinuousOn U (Ioi 0))
    (complexBound : ∀ v∈Ioi (0:ℝ), ‖U v-1‖≤K*(v/h)*(1+v/h)^2)
    (realBound : (h=E ∧ ∀ v∈Ioo (0:ℝ) T, ‖V v‖≤K*(h/v)*(1+v/h)^2) ∨
      (∀ v∈Ioo (0:ℝ) T, ‖V v‖≤K*(1+v/h)^2))
    (damping : |b|≤D*Real.exp (-(c*((n:ℝ)*E)))) :
    |normalizedCuts n q b T U V - Real.cos θ| ≤
      (28*K+6*D*K/c^2)/((n:ℝ)*E) := by
  let u := (n:ℝ)*E
  let W := moment n 0
  let Z := ∫ v in Ioi (0:ℝ), kernel n v • U v
  let R := ∫ v in Ioo (0:ℝ) T, kernel n v • V v
  have hn' : (8:ℝ)≤n := by exact_mod_cast hn
  have hW : 0<W := moment_pos n 0 (by norm_num) (by linarith)
  have hWc : (W:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hW.ne'
  have hh := hE.trans_le hEh
  have u₇ : (7:ℝ)≤u := hu
  have up : 0<u := by linarith
  have hs : u≤(n:ℝ)*h := mul_le_mul_of_nonneg_left hEh (by positivity)
  have hs₇ := u₇.trans hs
  have hspos := up.trans_le hs
  have hsmall := moving_complex_cut_bound hn hh hK hs₇ U hU complexBound
  have errC : |(q*(Z/(W:ℂ))).re - Real.cos θ| ≤ 28*K/u := by
    rw [←hphase,←Complex.sub_re,show q*(Z/(W:ℂ))-q=q*((Z-(W:ℂ))/(W:ℂ)) by field_simp; ring]
    apply (Complex.abs_re_le_norm _).trans
    rw [norm_mul,hq,one_mul,norm_div,Complex.norm_real,Real.norm_of_nonneg hW.le]
    exact hsmall.trans (div_le_div_of_nonneg_left (by positivity) up hs)
  have errR : ‖R‖/W≤3*K*u := by
    apply (div_le_iff₀ hW).mpr
    rcases realBound with ⟨he,hV⟩|hV
    · have cut := real_cut_bound hn hh hK V hV
      apply cut.trans
      have hrat : 7/((n:ℝ)*h)≤1 := (div_le_one hspos).mpr hs₇
      have hex : h*(2*n-1)=2*u-h := by rw [he]; dsimp [u]; ring
      rw [hex]
      calc
        _ ≤ (K*W)*(3*u) := by gcongr; linarith
        _ = _ := by ring
    · have cut := regular_real_cut_bound hn hh hK V hV
      apply cut.trans
      have rr : 7/((n:ℝ)*h)≤1 := (div_le_one hspos).mpr hs₇
      have H : (1+7/((n:ℝ)*h))^2 ≤ (2:ℝ)^2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
      calc
        _ ≤ K*W*(3*u) := by gcongr; linarith
        _ = _ := by ring
  have expo : Real.exp (-(c*u))≤2/(c*u)^2 := by
    have e := Real.pow_div_factorial_le_exp (c*u) (mul_pos hc up).le 2
    norm_num at e
    rw [Real.exp_neg]
    apply (le_div_iff₀ (by positivity)).mpr
    apply (le_of_mul_le_mul_left (a:=Real.exp (c*u)) ?_ (Real.exp_pos _))
    field_simp
    linarith
  have rr : |b*R.re/W|≤(6*D*K/c^2)/u := by
    rw [abs_div,abs_mul,abs_of_pos hW,mul_div_assoc]
    calc
      _ ≤ (D*Real.exp (-(c*u)))*(‖R‖/W) := by
        gcongr
        exact Complex.abs_re_le_norm _
      _ ≤ (D*(2/(c*u)^2))*(3*K*u) := by gcongr
      _ = _ := by field_simp; ring
  change |(q*(Z/(W:ℂ))).re+b*R.re/W-Real.cos θ|≤_
  rw [add_sub_right_comm]
  exact (abs_add_le _ _).trans ((add_le_add errC rr).trans_eq (by ring))

end BigDescents132.Cut
