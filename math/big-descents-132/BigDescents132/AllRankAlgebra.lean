import BigDescents132.Eventual

/-! Algebra used to make the contour separation and its multiplier estimate effective. -/
namespace BigDescents132.AllRanks
open Complex

/-- The rational branch map for the square roots of the original discriminant. -/
theorem square_root_discriminant {K : Type*} [Field K] {s w : K}
    (h : 1-s*w^4=2*w*(1-s*w^2)) :
    (radicand s).eval (w^2)=0 := by
  simp only [radicand,Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_one,
    Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_C]
  linear_combination (1-s*w^4+2*w*(1-s*w^2))*h

theorem lifted_quartic {K : Type*} [Field K] (p z w : K)
    (f : p^2+4*p*z+z^2+3*p^2*z^2=1) :
    (((p+z)*w-p)^2-1)*(((p+z)*w-z)^2+3*p^2*z^2)=
      (p+z)^4*w^4-2*(p+z)^4*w^3+2*((1-p^2)*z^2*(1+3*p^2))*w-
      (1-p^2)*z^2*(1+3*p^2) := by
  linear_combination (w*(p^2*w+2*p*w*z-2*p*z+w*z^2))*f

theorem reciprocal_complement {K : Type*} [Field K] (p z : K)
    (f : p^2+4*p*z+z^2+3*p^2*z^2=1) :
    (1-p^2)*z^2*(1+3*p^2)+(1-z^2)*p^2*(1+3*z^2)=(p+z)^4 := by
  linear_combination -(p^2+z^2)*f

/-- The exact separation has first order at both ends of the interval. -/
theorem normalized_gap {p S : ℝ} (hp : p∈Set.Ioo 0 1) (hS : 0<S)
    (sq : S^2=1+6*p^2-3*p^4) :
    1-(1+p)^2*(1+3*p^2)/(S+2*p)^2=
      p*(1-p)*(6*(1+p)^2/((2+S)*(S+2*p))) := by
  have h₁ : 0<S+2*p := by linarith [hp.1]
  have h₂ : 0<2+S := by linarith
  field_simp [h₁.ne',h₂.ne']
  linear_combination ((S+2*p)*(S+4*p+2))*sq

private theorem prod_diff (a b : ℂ) :
    ‖a*b-1‖≤‖a‖*‖b-1‖+‖a-1‖ := by
  calc
    _ = ‖a*(b-1)+(a-1)‖ := by congr 1; ring
    _ ≤ _ := (norm_add_le _ _).trans_eq (by rw [norm_mul])

private theorem from_diff {a : ℂ} {h : ℝ} (H : ‖a-1‖≤h) : ‖a‖≤1+h := by
  calc
    ‖a‖=‖1+(a-1)‖ := by ring_nf
    _ ≤ _ := (norm_add_le _ _).trans (by rw [norm_one]; linarith)

/-- Coefficientwise multiplier bound retaining all three individual beta moments. -/
theorem sharp_change {a b c q : ℂ} {S P v : ℝ} (hv : 0≤v) (hs : 0≤S) (hP : 0≤P)
    (ha : ‖a-1‖≤S*v) (hb : ‖b-1‖≤S*v) (hc : ‖c-1‖≤S*v/2)
    (hq : ‖q‖≤P) (dq : ‖q-1‖≤P*S*v) :
    ‖((1+v:ℝ)⁻¹:ℝ) • (q*(a*b*c))-1‖ ≤
      (1+7/2*P*S)*v+2*P*S^2*v^2+P/2*S^3*v^3 := by
  let x := S*v
  have xp : 0≤x := mul_nonneg hs hv
  have af := from_diff ha
  have bf := from_diff hb
  have ab : ‖a*b-1‖≤(1+x)*x+x := by
    exact (prod_diff a b).trans (add_le_add (mul_le_mul af hb (norm_nonneg _) (by positivity)) ha)
  have normab : ‖a*b‖≤(1+x)^2 := by
    rw [norm_mul,pow_two]; exact mul_le_mul af bf (norm_nonneg _) (by positivity)
  have abc : ‖a*b*c-1‖≤(1+x)^2*(x/2)+((1+x)*x+x) :=
    (prod_diff (a*b) c).trans (add_le_add (mul_le_mul normab hc (norm_nonneg _) (by positivity)) ab)
  have qabc := (prod_diff q (a*b*c)).trans (add_le_add (mul_le_mul hq abc (norm_nonneg _) hP) dq)
  have pos : 0<1+v := by linarith
  have eq : ((1+v:ℝ)⁻¹:ℝ) • (q*(a*b*c))-1=
      ((1+v:ℝ)⁻¹:ℝ) • ((q*(a*b*c)-1)-(v:ℂ)) := by
    rw [Complex.real_smul,Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_add,Complex.ofReal_one]
    have ne : (1:ℂ)+(v:ℂ)≠0 := by exact_mod_cast pos.ne'
    field_simp [ne]; ring
  rw [eq,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr pos.le)]
  apply le_trans (mul_le_of_le_one_left (norm_nonneg _) (by rw [inv_le_one₀ pos]; linarith))
  apply (norm_sub_le _ _).trans
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hv]
  dsimp [x] at qabc
  linarith only [qabc]

end BigDescents132.AllRanks
