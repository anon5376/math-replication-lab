import BigDescents132.RootCount
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace BigDescents132

open Polynomial Set
open scoped Polynomial

/-- The sign at the magnitude `a` expected after `k` crossings. -/
def AlternatesAt (p : ℝ[X]) (k : ℕ) (a : ℝ) : Prop :=
  0 < (-1 : ℝ)^k * p.eval (-a)

private theorem sign_change {p : ℝ[X]} {a b : ℝ} {k : ℕ}
    (ha : AlternatesAt p k a) (hb : AlternatesAt p (k+1) b) :
    p.eval (-a) * p.eval (-b) < 0 := by
  unfold AlternatesAt at ha hb
  rw [pow_succ] at hb
  have hsq : (-1 : ℝ)^k * (-1 : ℝ)^k = 1 := by rw [← mul_pow]; norm_num
  have h := mul_pos ha hb
  have he : ((-1 : ℝ)^k * p.eval (-a)) * ((-1 : ℝ)^k * -1 * p.eval (-b)) =
      -(p.eval (-a) * p.eval (-b)) := by
    calc
      _ = - (((-1 : ℝ)^k * (-1 : ℝ)^k) * (p.eval (-a) * p.eval (-b))) := by ring
      _ = _ := by rw [hsq, one_mul]
  linarith only [he ▸ h]

/-- An error strictly smaller than one preserves the sign at each cosine extremum. -/
theorem sign_at_cosine_extremum {p : ℝ[X]} {x phase normalizer : ℝ} {j : ℕ}
    (hn : 0 < normalizer) (hlevel : phase = (j : ℝ))
    (he : |p.eval (-x) / normalizer - Real.cos (phase * Real.pi)| < 1) :
    AlternatesAt p j x := by
  have hc : Real.cos ((j : ℝ) * Real.pi) = (-1 : ℝ)^j := by
    simpa using Real.cos_nat_mul_pi_sub (0 : ℝ) j
  rw [hlevel, hc, abs_lt] at he
  unfold AlternatesAt
  rcases neg_one_pow_eq_or ℝ j with h | h
  · rw [h] at he ⊢
    simpa using (div_pos_iff_of_pos_right hn).mp (show 0 < p.eval (-x)/normalizer by linarith)
  · rw [h] at he ⊢
    have hneg := (div_lt_iff₀ hn).mp (show p.eval (-x)/normalizer < 0 by linarith)
    rw [zero_mul] at hneg
    linarith

/-- A continuous phase, normalized in units of π, crosses its consecutive
integer levels in order. Each crossing plus the two edge samples gives
one more gap than the number of interior levels. -/
theorem phase_grid (p : ℝ[X]) (phase : ℝ → ℝ) {b : ℝ} (count : ℕ) :
    ∀ {a : ℝ} {start : ℕ}, a < b → ContinuousOn phase (Icc a b) →
    phase a < (start + 1 : ℕ) → ((start + count : ℕ) : ℝ) < phase b →
    AlternatesAt p start a → AlternatesAt p (start + count + 1) b →
    (∀ j : ℕ, start < j → j ≤ start + count → ∀ x ∈ Ioo a b,
        phase x = (j : ℝ) → AlternatesAt p j x) →
    Grid p (-a) (-b) (count + 1) := by
  induction count with
  | zero =>
    intro a start hab _ _ _ ha hb _
    exact Grid.cons (neg_lt_neg hab) (sign_change ha (by simpa using hb)) (Grid.nil _)
  | succ count ih =>
    intro a start hab hc hlo hhi ha hb hsign
    have hl : ((start+1 : ℕ) : ℝ) < phase b :=
      lt_of_le_of_lt (by exact_mod_cast (show start+1 ≤ start+(count+1) by omega)) hhi
    obtain ⟨x, hx, hphase⟩ := intermediate_value_Ioo hab.le hc ⟨hlo, hl⟩
    have hxsign := hsign (start+1) (by omega) (by omega) x hx hphase
    apply Grid.cons (neg_lt_neg hx.1) (sign_change ha hxsign)
    apply ih (start := start+1) hx.2 (hc.mono (Icc_subset_Icc hx.1.le le_rfl))
    · rw [hphase]
      exact_mod_cast (Nat.lt_succ_self (start + 1))
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hhi
    · exact hxsign
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb
    · intro j hj hj' y hy hyphase
      exact hsign j (by omega) (by omega) y ⟨hx.1.trans hy.1, hy.2⟩ hyphase

/-- The hypotheses supplied by the small-argument limit, interior cosine
estimate and reciprocal limit in the proposed asymptotic argument. -/
structure PhaseCertificate (p : ℝ[X]) (d : ℕ) where
  left : ℝ
  right : ℝ
  far : ℝ
  start : ℕ
  interior : ℕ
  tail : ℕ
  phase : ℝ → ℝ
  degree_le : p.natDegree ≤ d
  count_eq : start + (interior + 1) + tail = d
  ordered : left < right
  continuous : ContinuousOn phase (Icc left right)
  below_first : phase left < ((start + 1 : ℕ) : ℝ)
  above_last : ((start + interior : ℕ) : ℝ) < phase right
  left_grid : Grid p 0 (-left) start
  left_sign : AlternatesAt p start left
  right_sign : AlternatesAt p (start + interior + 1) right
  normalizer : ℝ → ℝ
  normalizer_pos : ∀ x ∈ Ioo left right, 0 < normalizer x
  middle_error : ∀ x ∈ Ioo left right,
    |p.eval (-x) / normalizer x - Real.cos (phase x * Real.pi)| < 1
  right_grid : Grid p (-right) far tail

theorem PhaseCertificate.sound {p : ℝ[X]} {d : ℕ} (c : PhaseCertificate p d) :
    p.natDegree = d ∧ SimpleNegative p := by
  have hmid := phase_grid p c.phase c.interior c.ordered c.continuous c.below_first
    c.above_last c.left_sign c.right_sign (fun _ _ _ x hx hf =>
      sign_at_cosine_extremum (c.normalizer_pos x hx) hf (c.middle_error x hx))
  have hgrid := (c.left_grid.append hmid).append c.right_grid
  rw [c.count_eq] at hgrid
  have hp : p ≠ 0 := by
    intro h
    have hs := c.left_sign
    simp [AlternatesAt, h] at hs
  exact simpleNegative_of_grid hp hgrid c.degree_le

/-- This is a reduction. Existence of these certificates for unbounded ranks
is the analytic obligation. -/
theorem eventual_of_phase_certificates
    (h : ∃ N : ℕ, ∀ n ≥ N, Nonempty (PhaseCertificate (B n) (expectedDegree n))) :
    EventualSimpleNegative := by
  obtain ⟨N, h⟩ := h
  exact ⟨N, fun n hn => (h n hn).elim fun c => c.sound⟩

end BigDescents132
