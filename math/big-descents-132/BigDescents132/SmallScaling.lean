import BigDescents132.Column
import BigDescents132.Edge
import BigDescents132.Degree
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Exp

namespace BigDescents132
open Finset Filter
open scoped Polynomial Topology

theorem B_eval_nonneg (n : ℕ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ (B n).eval s := by
  rw [B_sum, Polynomial.eval_finset_sum]
  exact sum_nonneg fun w _ => by simp [weight]; positivity

private theorem A_eval_nonneg (k : ℕ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ (A (k+1)).eval s := by
  rw [A, Polynomial.eval_finset_sum]
  exact sum_nonneg fun w _ => by simp [weight]; positivity

private theorem C_eval_le (k : ℕ) {s : ℝ} (hs : 0 ≤ s) : (C (k+1)).eval s ≤ (B (k+1)).eval s := by
  rw [B_eq_A_add_C, Polynomial.eval_add]
  linarith [A_eval_nonneg k hs]

/-- A uniform positive-argument bound obtained directly by induction on the permutation recurrence. -/
theorem positive_eval_bound (N : ℕ) {s : ℝ} (hs : 0 ≤ s) (m : ℕ) (hm : m ≤ N) :
    (B (m+1)).eval s ≤ (m+1:ℝ)*(1+s*(N:ℝ)^2)^(m+1) ∧
    (A (m+1)).eval s ≤ 1+s*(m:ℝ)^2*(1+s*(N:ℝ)^2)^m := by
  let q := 1+s*(N:ℝ)^2
  have hq : 1 ≤ q := by dsimp [q]; linarith [mul_nonneg hs (sq_nonneg (N:ℝ))]
  have hq0 : 0 ≤ q := by linarith
  change _ ≤ (m+1:ℝ)*q^(m+1) ∧ _ ≤ 1+s*(m:ℝ)^2*q^m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero => simpa using hq
    | succ k =>
      have ⟨hB,hA⟩ := ih k (by omega) (by omega)
      have hp : q^k ≤ q^(k+1) := pow_le_pow_right₀ hq (by omega)
      have ha : (A (k+2)).eval s ≤ 1+s*(k+1:ℝ)^2*q^(k+1) := by
        rw [A_recurrence, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
        calc
          _ ≤ (1+s*(k:ℝ)^2*q^k) + s*((k+1:ℝ)*q^(k+1)) :=
            add_le_add hA (mul_le_mul_of_nonneg_left ((C_eval_le k hs).trans hB) hs)
          _ ≤ (1+s*(k:ℝ)^2*q^(k+1)) + s*((k+1:ℝ)*q^(k+1)) := by gcongr
          _ = 1+s*((k:ℝ)^2+(k+1))*q^(k+1) := by ring
          _ ≤ _ := by gcongr; nlinarith [show (0:ℝ) ≤ k by positivity]
      have hsum : (∑ i ∈ range k, (B (i+1)).eval s * (B (k-i)).eval s) ≤
          (k+1:ℝ)^3*q^(k+1) := by
        calc
          _ ≤ ∑ _i ∈ range k, ((k+1:ℝ)^2*q^(k+1)) := by
            apply sum_le_sum
            intro i hi
            have hi' := mem_range.mp hi
            have hj : k-i = (k-i-1)+1 := by omega
            have hiB := (ih i (by omega) (by omega)).1
            have hjB := (ih (k-i-1) (by omega) (by omega)).1
            rw [← hj] at hjB
            have hc : (k-i-1:ℕ) + (1:ℝ) = (k-i:ℕ) := by exact_mod_cast hj.symm
            rw [hc] at hjB
            calc
              _ ≤ ((i+1:ℝ)*q^(i+1)) * (((k-i:ℕ):ℝ)*q^(k-i)) :=
                mul_le_mul hiB hjB (B_eval_nonneg _ hs) (by positivity)
              _ = ((i+1:ℝ)*(k-i:ℕ))*q^(i+1+(k-i)) := by rw [pow_add]; ring
              _ ≤ _ := by
                rw [show i+1+(k-i) = k+1 by omega, pow_two]
                gcongr
                exact_mod_cast (by omega : k-i ≤ k+1)
          _ = (k:ℝ)*((k+1:ℝ)^2*q^(k+1)) := by simp
          _ ≤ (k+1:ℝ)*((k+1:ℝ)^2*q^(k+1)) := by gcongr; linarith
          _ = _ := by ring
      have hb : (B (k+2)).eval s ≤ (k+1+1:ℝ)*q^(k+2) := by
        rw [B_eq_A_add_C, C_recurrence, Polynomial.eval_add, Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_finset_sum]
        simp only [Polynomial.eval_mul]
        calc
          _ ≤ (1+s*(k+1:ℝ)^2*q^(k+1)) + ((k+1:ℝ)*q^(k+1) + s*((k+1:ℝ)^3*q^(k+1))) :=
            add_le_add ha (add_le_add hB (mul_le_mul_of_nonneg_left hsum hs))
          _ ≤ (q^(k+1)+s*(k+1:ℝ)^2*q^(k+1)) + ((k+1:ℝ)*q^(k+1)+s*((k+1:ℝ)^3*q^(k+1))) := by
            gcongr
            exact one_le_pow₀ hq
          _ = ((k+1+1:ℝ)*q^(k+1)) * (1+s*(k+1:ℝ)^2) := by ring
          _ ≤ ((k+1+1:ℝ)*q^(k+1)) * q := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            dsimp [q]
            gcongr
            exact_mod_cast hm
          _ = _ := by rw [pow_succ q (k+1)]; ring
      exact ⟨by simpa using hb, by simpa using ha⟩

theorem scaled_positive_bound {n : ℕ} (hn : 0 < n) {u : ℝ} (hu : 0 ≤ u) :
    (B n).eval (u/(n:ℝ)^3) / n ≤ Real.exp u := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let N : ℝ := (m+1 : ℕ)
  have hn0 : N ≠ 0 := hn'.ne'
  have h := (positive_eval_bound (m+1) (s := u/N^3) (by positivity) m (by omega)).1
  change (B (m+1)).eval (u/N^3) / N ≤ _
  apply (div_le_iff₀ hn').mpr
  have hq : 1+u/N^3*N^2 = 1+u/N := by field_simp; ring
  rw [show ((m+1:ℕ):ℝ) = N by rfl, hq] at h
  calc
    _ ≤ _ := h
    _ ≤ (m+1:ℝ) * (Real.exp (u/N))^(m+1) := by
      gcongr
      simpa [add_comm] using Real.add_one_le_exp (u/N)
    _ = _ := by rw [← Real.exp_nat_mul, show ((m+1:ℕ):ℝ) * (u/N) = u by change N*(u/N) = u; field_simp]
                simp [N, mul_comm]

private theorem coeff_term_le {n k : ℕ} {s : ℝ} (hs : 0 ≤ s) :
    (B n).coeff k * s^k ≤ (B n).eval s := by
  by_cases h : k ∈ (B n).support
  · rw [Polynomial.eval_eq_sum, Polynomial.sum]
    exact single_le_sum (fun i _ => mul_nonneg (B_coeff_nonneg n i) (pow_nonneg hs i)) h
  · rw [not_iff_not.mpr Polynomial.mem_support_iff, not_not] at h
    simpa [h] using B_eval_nonneg n hs

private theorem term_rearrange (n : ℕ) (k : ℕ) (a u : ℝ) :
    a/(n:ℝ)^(3*k+1) * u^k = a*(u/(n:ℝ)^3)^k / n := by
  rw [pow_succ, pow_mul, div_pow]
  ring

private theorem coefficient_majorant {n : ℕ} (hn : 0 < n) (u : ℝ) (k : ℕ) :
    ‖(B n).coeff k / (n:ℝ)^(3*k+1) * u^k‖ ≤ Real.exp (2*|u|) * (1/2:ℝ)^k := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have h := (div_le_div_of_nonneg_right
    (coeff_term_le (n:=n) (k:=k) (s:=2*|u|/(n:ℝ)^3) (by positivity)) hn'.le).trans
    (scaled_positive_bound hn (u:=2*|u|) (by positivity))
  calc
    _ = ((B n).coeff k * (2*|u|/(n:ℝ)^3)^k / n) * (1/2:ℝ)^k := by
      rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg
        (div_nonneg (B_coeff_nonneg n k) (by positivity)), term_rearrange]
      rw [show 2*|u|/(n:ℝ)^3 = 2*(|u|/(n:ℝ)^3) by ring, mul_pow, one_div, inv_pow]
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h (by positivity)

/-- The limiting series on the small scale. -/
noncomputable def smallLimit (u : ℝ) : ℝ :=
  ∑' k : ℕ, ((catalan k : ℝ)/(3*k+1).factorial) * u^k

/-- Pointwise convergence at every real argument, including all fixed sign witnesses. -/
theorem small_endpoint_limit (u : ℝ) : Tendsto
    (fun n : ℕ => (B n).eval (u/(n:ℝ)^3) / n) atTop (𝓝 (smallLimit u)) := by
  have h := tendsto_tsum_of_dominated_convergence
    ((summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1)).mul_left
      (Real.exp (2*|u|)))
    (fun k => (Series.small_coefficient_limit k).mul_const (u^k))
    (eventually_atTop.mpr ⟨1, fun n hn k => coefficient_majorant (by omega) u k⟩)
  apply h.congr'
  filter_upwards with n
  rw [tsum_eq_sum (s := (B n).support) (fun k hk => by
    have hzero := not_ne_iff.mp (fun hnz => hk (Polynomial.mem_support_iff.mpr hnz))
    simp [hzero])]
  rw [Polynomial.eval_eq_sum, Polynomial.sum, div_eq_mul_inv, Finset.sum_mul]
  apply sum_congr rfl
  intro k _
  simpa only [div_eq_mul_inv] using term_rearrange n k ((B n).coeff k) u

theorem smallLimit_neg_nat (x : ℕ) : smallLimit (-(x:ℝ)) = smallEdge x := by
  unfold smallLimit smallEdge
  apply tsum_congr
  intro k
  rw [edgeTerm_eq_catalan]
  push_cast
  rfl

theorem smallLimit_zero : smallLimit 0 = 1 := by
  rw [smallLimit, tsum_eq_single 0]
  · simp
  · intro k hk
    simp [zero_pow hk]

/-- The first four small-edge sign intervals contain four distinct negative
zeros of the actual permutation polynomial at every sufficiently large rank. -/
theorem eventual_small_grid : ∀ᶠ n : ℕ in atTop, Grid (B n) 0 (-1348/(n:ℝ)^3) 4 := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := smallEdge_first_four
  have neg (x : ℕ) (h : smallEdge x < 0) : ∀ᶠ n : ℕ in atTop,
      (B n).eval (-(x:ℝ)/(n:ℝ)^3) < 0 := by
    have e := small_endpoint_limit (-(x:ℝ))
    rw [smallLimit_neg_nat] at e
    filter_upwards [e.eventually_lt_const h, eventually_gt_atTop 0] with n hn hp
    rcases div_neg_iff.mp hn with h | h
    · exact (not_lt_of_ge (Nat.cast_nonneg n) h.2).elim
    · exact h.1
  have pos (x : ℕ) (h : 0 < smallEdge x) : ∀ᶠ n : ℕ in atTop,
      0 < (B n).eval (-(x:ℝ)/(n:ℝ)^3) := by
    have e := small_endpoint_limit (-(x:ℝ))
    rw [smallLimit_neg_nat] at e
    filter_upwards [e.eventually_const_lt h, eventually_gt_atTop 0] with n hn hp
    exact (div_pos_iff_of_pos_right (Nat.cast_pos.mpr hp)).mp hn
  have h₀ := small_endpoint_limit 0
  simp only [zero_div, smallLimit_zero] at h₀
  filter_upwards [h₀.eventually_const_lt (by norm_num : (0:ℝ) < 1), neg _ h₁, pos _ h₂,
    neg _ h₃, pos _ h₄, eventually_gt_atTop 0] with n h0 h1 h2 h3 h4 hn
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hzero := (div_pos_iff_of_pos_right hn').mp h0
  have hpow : 0 < (n:ℝ)^3 := by positivity
  norm_num only [Nat.cast_ofNat] at h1 h2 h3 h4
  have g : Grid (B n) 0 (-1348/(n:ℝ)^3) 4 := by
    exact Grid.cons (div_neg_of_neg_of_pos (by norm_num) hpow) (mul_neg_of_pos_of_neg hzero h1)
      (Grid.cons ((div_lt_div_iff_of_pos_right hpow).mpr (by norm_num)) (mul_neg_of_neg_of_pos h1 h2)
      (Grid.cons ((div_lt_div_iff_of_pos_right hpow).mpr (by norm_num)) (mul_neg_of_pos_of_neg h2 h3)
      (Grid.cons ((div_lt_div_iff_of_pos_right hpow).mpr (by norm_num)) (mul_neg_of_neg_of_pos h3 h4)
        (Grid.nil _))))
  exact g

theorem eventual_four_small_roots : ∀ᶠ n : ℕ in atTop,
    ∃ s : Finset ℝ, s.card = 4 ∧ ∀ x ∈ s, x < 0 ∧ (B n).IsRoot x :=
  eventual_small_grid.mono fun _ h => h.rootsBelow

end BigDescents132
