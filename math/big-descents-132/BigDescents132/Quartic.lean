import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace BigDescents132

open Polynomial
open scoped Polynomial

/-- Radicand of the algebraic generating function in Theorem 2.1, at s = 1 - t. -/
noncomputable def radicand {K : Type*} [CommRing K] (s : K) : K[X] :=
  1 - 4*X + C (6*s)*X^2 - C (4*s^2)*X^3 + C (s^2)*X^4

private theorem radicand_eval {K : Type*} [CommRing K] (s z : K) :
    (radicand s).eval z = 1 - 4*z + 6*s*z^2 - 4*s^2*z^3 + s^2*z^4 := by
  simp [radicand]

private theorem radicand_derivative_eval {K : Type*} [CommRing K] (s z : K) :
    (radicand s).derivative.eval z = -4 + 12*s*z - 12*s^2*z^2 + 4*s^2*z^3 := by
  norm_num [radicand, derivative_sub, derivative_add, derivative_mul, derivative_pow]
  ring

/-- In particular the four branch points never collide on the whole parameter ray s > 1. -/
theorem radicand_simple {s : ℂ} (hzero : s ≠ 0) (hone : s ≠ 1) {z : ℂ}
    (hz : (radicand s).IsRoot z) : ¬ (radicand s).derivative.IsRoot z := by
  intro hd
  change (radicand s).eval z = 0 at hz
  change (radicand s).derivative.eval z = 0 at hd
  rw [radicand_eval] at hz
  rw [radicand_derivative_eval] at hd
  have h : 3 * (s - 1) * z * (1 - s*z) = 0 := by
    linear_combination hz - (z - 1)/4 * hd
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hone
  have hz1 := (mul_eq_zero.mp h).resolve_left (mul_ne_zero (mul_ne_zero (by norm_num) hs1) hz0)
  have heq : z = 1/s := (eq_div_iff hzero).mpr (by linear_combination -hz1)
  rw [heq] at hz
  have heval : s^2 * (1 - 4*(1/s) + 6*s*(1/s)^2 - 4*s^2*(1/s)^3 + s^2*(1/s)^4) = (s-1)^2 := by
    field_simp [hzero]
    ring
  rw [hz, mul_zero] at heval
  have hsq := heval.symm
  exact hs1 (pow_eq_zero hsq)

/-- There is exactly one real critical point. Write u³ = (s−1)/s.
The derivative factors as a linear term times a strictly positive quadratic. -/
theorem one_real_critical_point {s : ℝ} (hs : 1 < s) :
    ∃ c : ℝ, ∀ x : ℝ, (radicand s).derivative.IsRoot x ↔ x = c := by
  have hs0 : 0 < s := by linarith
  have ha : 0 < (s-1)/s := div_pos (sub_pos.mpr hs) hs0
  have hb : (s-1)/s < 1 := (div_lt_one hs0).mpr (by linarith)
  have hc : ContinuousOn (fun x : ℝ => x^3) (Set.Icc 0 1) := (continuous_id.pow 3).continuousOn
  obtain ⟨u, hu, hu₃⟩ := intermediate_value_Ioo (by norm_num : (0:ℝ) ≤ 1) hc
    (show (s-1)/s ∈ Set.Ioo ((0:ℝ)^3) ((1:ℝ)^3) by simpa using And.intro ha hb)
  change u^3 = (s-1)/s at hu₃
  have hrel : s*u^3 = s-1 := by simpa [mul_comm] using (eq_div_iff hs0.ne').mp hu₃
  refine ⟨1+u+u^2, fun x => ?_⟩
  have hf : (radicand s).derivative.eval x = s^2 * (x-1-u-u^2) *
      ((2*(x-1)+u+u^2)^2 + 3*(u*(1-u))^2) := by
    rw [radicand_derivative_eval]
    linear_combination (12*s*(x-1)+4*(2*s-1+s*u^3)) * hrel
  have hq : 0 < (2*(x-1)+u+u^2)^2 + 3*(u*(1-u))^2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _)
      (mul_pos (by norm_num) (sq_pos_of_pos (mul_pos hu.1 (sub_pos.mpr hu.2))))
  change (radicand s).derivative.eval x = 0 ↔ _
  rw [hf, mul_eq_zero, mul_eq_zero]
  simp only [hq.ne', (pow_ne_zero 2 hs0.ne'), false_or, or_false]
  constructor <;> intro h <;> linarith

/-- The radicand has precisely two real zeros for every s > 1, one on
each side of 1. -/
theorem real_branch_points {s : ℝ} (hs : 1 < s) :
    ∃ r ∈ Set.Ioo (1/s) 1, ∃ R ∈ Set.Ioo (1:ℝ) 4,
      ∀ x : ℝ, (radicand s).IsRoot x ↔ x = r ∨ x = R := by
  let p := radicand s
  have hs0 : 0 < s := by linarith
  have hlow : 1/s < 1 := (div_lt_one hs0).mpr hs
  have hpos : 0 < p.eval (1/s) := by
    have he : p.eval (1/s) = ((s-1)/s)^2 := by
      rw [radicand_eval]
      field_simp [hs0.ne']
      ring
    rw [he]
    exact sq_pos_of_pos (div_pos (sub_pos.mpr hs) hs0)
  have hneg : p.eval 1 < 0 := by
    rw [radicand_eval]
    nlinarith [sq_pos_of_pos (sub_pos.mpr hs)]
  have hfour : 0 < p.eval 4 := by rw [radicand_eval]; linarith
  obtain ⟨r, hr, her⟩ := intermediate_value_Ioo' hlow.le p.continuousOn (And.intro hneg hpos)
  obtain ⟨R, hR, heR⟩ := intermediate_value_Ioo (by norm_num : (1:ℝ) ≤ 4) p.continuousOn
    (And.intro hneg hfour)
  obtain ⟨c, hc⟩ := one_real_critical_point hs
  have no_three {a b d : ℝ} (hab : a < b) (hbd : b < d)
      (ha : p.IsRoot a) (hb : p.IsRoot b) (hd : p.IsRoot d) : False := by
    obtain ⟨i, hi, hi'⟩ := exists_deriv_eq_zero hab p.continuousOn (ha.trans hb.symm)
    obtain ⟨j, hj, hj'⟩ := exists_deriv_eq_zero hbd p.continuousOn (hb.trans hd.symm)
    rw [p.deriv] at hi' hj'
    have hij := hi.2.trans hj.1
    rw [(hc i).mp hi', (hc j).mp hj'] at hij
    exact (lt_irrefl c) hij
  refine ⟨r, hr, R, hR, fun x => ⟨?_, ?_⟩⟩
  · intro hx
    rcases lt_trichotomy x r with hl | he | hg
    · exact (no_three hl (hr.2.trans hR.1) hx her heR).elim
    · exact Or.inl he
    · rcases lt_trichotomy x R with hl | he | hg'
      · exact (no_three hg hl her hx heR).elim
      · exact Or.inr he
      · exact (no_three (hr.2.trans hR.1) hg' her heR hx).elim
  · rintro (rfl | rfl)
    · exact her
    · exact heR

/-- Vieta's equations in the proposed three-equal-moduli case force v = 1.
Here v is the square root of R/ρ. -/
theorem vieta_excludes_collision {u v : ℝ} (hv : 1 < v)
    (hp : u * (v + 1/v) = 6)
    (hs : (u + v^2) * (u + 1/v^2) = 16) : False := by
  have hv0 : 0 < v := by linarith
  let z : ℝ := v + 1/v
  have hz : 2 < z := by
    dsimp [z]
    have hpos := div_pos (sq_pos_of_pos (sub_pos.mpr hv)) hv0
    have he : v + 1/v - 2 = (v-1)^2/v := by field_simp; ring
    linarith
  have hu : u*z = 6 := hp
  have h₂ : u^2 + u*(z^2 - 2) + 1 = 16 := by
    dsimp [z]
    convert hs using 1
    field_simp
    ring
  have hzpoly : (z-2)^2*(2*z+3) = 0 := by
    linear_combination (z^2 * h₂ - (u*z + 6 + z*(z^2 - 2)) * hu) / 3
  exact (ne_of_gt (mul_pos (sq_pos_of_pos (sub_pos.mpr hz)) (by linarith))) hzpoly

end BigDescents132
