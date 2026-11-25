import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace BigDescents132

open Finset

private def central (k : ℕ) : ℕ := (2*k).factorial / (k.factorial * k.factorial)

private theorem central_eq (k : ℕ) : central k = (2*k).choose k := by
  rw [Nat.choose_eq_factorial_div_factorial (by omega : k ≤ 2*k), show 2*k-k = k by omega]
  rfl

/-- The k-th term of the proposed small-edge limit at −x, with
Catalan coefficient choose(2k,k)/(k+1). -/
def edgeTerm (x k : ℕ) : ℚ :=
  (central k : ℚ) * (-(x : ℚ))^k / (((k+1) * (3*k+1).factorial : ℕ) : ℚ)

theorem edgeTerm_eq_catalan (x k : ℕ) :
    edgeTerm x k = ((catalan k : ℚ) / (3*k+1).factorial) * (-(x : ℚ))^k := by
  have hc : (2*k).choose k = (k+1)*catalan k := (succ_mul_catalan_eq_centralBinom k).symm
  rw [edgeTerm, central_eq, hc]
  push_cast
  field_simp
  ring

noncomputable def smallEdge (x : ℕ) : ℝ := ∑' k, (edgeTerm x k : ℝ)

def partialEdge (x : ℕ) : ℕ → ℚ
  | 0 => 0
  | k + 1 => partialEdge x k + edgeTerm x k

private theorem partialEdge_cast (x n : ℕ) : (partialEdge x n : ℝ) =
    ∑ k ∈ range n, (edgeTerm x k : ℝ) := by
  induction n with
  | zero => simp [partialEdge]
  | succ n ih => simp [partialEdge, ih, sum_range_succ]

private theorem factorial_majorant (j : ℕ) :
    100 * 2^j * 5392^(j+21) ≤ (3*(j+21)+1).factorial := by
  induction j with
  | zero => decide
  | succ j ih =>
    let k := 3*(j+21)+1
    have hk : 64 ≤ k := by dsimp [k]; omega
    have hfac : 2*5392 ≤ (k+3)*(k+2)*(k+1) := by
      exact (by decide : 2*5392 ≤ 67*66*65).trans
        (Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega))
    calc
      100 * 2^(j+1) * 5392^(j+1+21) =
          (2*5392) * (100 * 2^j * 5392^(j+21)) := by
        rw [show j+1+21 = (j+21)+1 by omega, pow_succ, pow_succ]
        ring
      _ ≤ ((k+3)*(k+2)*(k+1)) * k.factorial := Nat.mul_le_mul hfac ih
      _ = (3*(j+1+21)+1).factorial := by
        rw [show 3*(j+1+21)+1 = k+3 by dsimp [k]; omega]
        rw [Nat.factorial_succ (k+2), Nat.factorial_succ (k+1), Nat.factorial_succ k]
        ring

private theorem edgeTerm_norm (x k : ℕ) : ‖(edgeTerm x k : ℝ)‖ =
    (((2*k).choose k * x^k : ℕ) : ℝ) / (((k+1)*(3*k+1).factorial : ℕ) : ℝ) := by
  simp only [edgeTerm, central_eq, Real.norm_eq_abs, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_natCast, abs_div, abs_mul, abs_pow, abs_neg, Nat.abs_cast,
    Nat.cast_mul, Nat.cast_pow]

private theorem edge_bound (x j : ℕ) (hx : x ≤ 1348) :
    ‖(edgeTerm x (j+21) : ℝ)‖ ≤ (1/100 : ℝ) * (1/2 : ℝ)^j := by
  let k := j + 21
  have hc : (2*k).choose k ≤ 4^k := by
    calc
      (2*k).choose k ≤ 2^(2*k) := (Nat.choose_le_two_pow _ _ (by dsimp [k]; omega)).le
      _ = 4^k := by rw [pow_mul]; norm_num
  have hnum : (2*k).choose k * x^k ≤ 5392^k := calc
    _ ≤ 4^k * 1348^k := Nat.mul_le_mul hc (Nat.pow_le_pow_left hx k)
    _ = _ := by rw [← mul_pow]; rfl
  have hden : (3*k+1).factorial ≤ (k+1) * (3*k+1).factorial :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hnat := ((Nat.mul_le_mul_left (100*2^j) hnum).trans (factorial_majorant j)).trans hden
  have hpos : 0 < (3*k+1).factorial := Nat.factorial_pos _
  change ‖(edgeTerm x k : ℝ)‖ ≤ _
  calc
    _ = (((2*k).choose k * x^k : ℕ) : ℝ) / (((k+1)*(3*k+1).factorial : ℕ) : ℝ) := edgeTerm_norm x k
    _ ≤ 1 / ((100*2^j : ℕ) : ℝ) := by
      apply (div_le_div_iff₀ (Nat.cast_pos.mpr (Nat.mul_pos (Nat.succ_pos _) hpos))
        (Nat.cast_pos.mpr (Nat.mul_pos (by decide) (Nat.pow_pos (by decide))))).mpr
      exact_mod_cast (by simpa only [one_mul, mul_comm] using hnat :
        ((2*k).choose k * x^k) * (100*2^j) ≤ 1 * ((k+1)*(3*k+1).factorial))
    _ = _ := by push_cast; rw [div_pow, one_pow]; ring

/-- A uniform absolute error of 1/50 suffices for the first four witnesses. -/
theorem smallEdge_error (x : ℕ) (hx : x ≤ 1348) :
    |smallEdge x - (partialEdge x 21 : ℝ)| ≤ 1/50 := by
  have hg : HasSum (fun j : ℕ => (1/100 : ℝ)*(1/2 : ℝ)^j) (1/50) := by
    convert (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) < 1)).mul_left (1/100) using 1
    norm_num
  have hs := Summable.of_norm_bounded _ hg.summable (edge_bound x · hx)
  have hfull : Summable (fun k => (edgeTerm x k : ℝ)) := (summable_nat_add_iff 21).mp hs
  have he := hfull.sum_add_tsum_nat_add 21
  have he' : (partialEdge x 21 : ℝ) + (∑' j, (edgeTerm x (j+21) : ℝ)) = smallEdge x := by
    simpa only [partialEdge_cast, smallEdge] using he
  rw [← he']
  simpa [Real.norm_eq_abs] using tsum_of_norm_bounded hg (edge_bound x · hx)

theorem smallEdge_first_four :
    smallEdge 74 < 0 ∧ 0 < smallEdge 271 ∧ smallEdge 672 < 0 ∧ 0 < smallEdge 1348 := by
  have hn (x : ℕ) (hx : x ≤ 1348) (hc : partialEdge x 21 < -(1/50 : ℚ)) : smallEdge x < 0 := by
    have h := (abs_le.mp (smallEdge_error x hx)).2
    have h' : (partialEdge x 21 : ℝ) < -(1/50 : ℝ) := by
      simpa only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using (Rat.cast_lt (K := ℝ)).mpr hc
    linarith
  have hp (x : ℕ) (hx : x ≤ 1348) (hc : (1/50 : ℚ) < partialEdge x 21) : 0 < smallEdge x := by
    have h := (abs_le.mp (smallEdge_error x hx)).1
    have h' : (1/50 : ℝ) < (partialEdge x 21 : ℝ) := by
      simpa only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using (Rat.cast_lt (K := ℝ)).mpr hc
    linarith
  exact ⟨hn 74 (by decide) (by decide +kernel), hp 271 (by decide) (by decide +kernel),
    hn 672 (by decide) (by decide +kernel), hp 1348 (by decide) (by decide +kernel)⟩

end BigDescents132
