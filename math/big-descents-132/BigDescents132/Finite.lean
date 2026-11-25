import BigDescents132.Certificate
import BigDescents132.Ten
import Mathlib.Tactic.IntervalCases

namespace BigDescents132

set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-- Every coefficient at these ranks comes from the defining permutation sum. -/
theorem finite_simple_negative (n : ℕ) (hn : n ≤ 10) :
    (B n).natDegree = expectedDegree n ∧ SimpleNegative (B n) := by
  interval_cases n
  · rw [B_eq_branchRow, show branchRow 0 = [1] by decide +kernel]
    exact checked_row _ ([] : List ℚ) (by decide +kernel) (by decide) (by decide +kernel)
  · rw [B_eq_branchRow, show branchRow 1 = [1] by decide +kernel]
    exact checked_row _ ([] : List ℚ) (by decide +kernel) (by decide) (by decide +kernel)
  · rw [B_eq_branchRow, show branchRow 2 = [2] by decide +kernel]
    exact checked_row _ ([] : List ℚ) (by decide +kernel) (by decide) (by decide +kernel)
  · rw [B_eq_branchRow, show branchRow 3 = [3, 2] by decide +kernel]
    exact checked_row _ ([-2] : List ℚ) (by decide +kernel) (by decide) (by decide +kernel)
  · rw [B_eq_branchRow, show branchRow 4 = [4, 9, 1] by decide +kernel]
    exact checked_row _ ([-1/2, -16] : List ℚ) (by decide +kernel) (by decide) (by decide +kernel)
  · rw [B_eq_branchRow, show branchRow 5 = [5, 25, 12] by decide +kernel]
    exact checked_row _ ([-1/4, -2] : List ℚ) (by decide +kernel) (by decide) (by decide +kernel)
  · rw [B_eq_branchRow, show branchRow 6 = [6, 55, 64, 7] by decide +kernel]
    exact checked_row _ ([-1/4, -1, -16] : List ℚ) (by decide +kernel) (by decide) (by decide +kernel)
  · rw [B_eq_branchRow, show branchRow 7 = [7, 105, 233, 82, 2] by decide +kernel]
    exact checked_row _ ([-1/8, -1/2, -4, -64] : List ℚ) (by decide +kernel) (by decide) (by decide +kernel)
  · rw [B_eq_branchRow, show branchRow 8 = [8, 182, 674, 505, 61] by decide +kernel]
    exact checked_row _ ([-1/16, -1/2, -2, -8] : List ℚ) (by decide +kernel) (by decide) (by decide +kernel)
  · rw [B_eq_branchRow, show branchRow 9 = [9, 294, 1668, 2206, 660, 25] by decide +kernel]
    exact checked_row _ ([-1/16, -1/4, -1, -4, -32] : List ℚ) (by decide +kernel) (by decide) (by decide +kernel)
  · rw [B_ten]
    exact checked_row _ ([-1/32, -1/4, -1/2, -2, -8, -128] : List ℚ) (by decide +kernel) (by decide) (by decide +kernel)

end BigDescents132
