import BigDescents132.RootCount
import Mathlib.Tactic.NormNum

namespace BigDescents132

open Polynomial
open scoped Polynomial

/-- Rational Horner evaluation, in ascending coefficient order. -/
def evalQ (row : List ℕ) (x : ℚ) : ℚ :=
  row.foldr (fun c acc => (c : ℚ) + x * acc) 0

theorem eval_ofRow (row : List ℕ) (x : ℚ) :
    (ofRow row).eval (x : ℝ) = ((evalQ row x : ℚ) : ℝ) := by
  induction row with
  | nil => simp [ofRow, evalQ]
  | cons a t ih => simp [ofRow, evalQ] at ih ⊢; rw [ih]; simp

private theorem degree_cons_le (a : ℕ) (t : List ℕ) :
    (ofRow (a :: t)).natDegree ≤ t.length := by
  induction t generalizing a with
  | nil => simp [ofRow]
  | cons b t ih =>
    apply (natDegree_add_le _ _).trans
    apply max_le
    · simp
    · apply natDegree_mul_le.trans
      simpa [Nat.add_comm] using Nat.succ_le_succ (ih b)

def checks (row : List ℕ) (a : ℚ) : List ℚ → Bool
  | [] => true
  | b :: bs => decide (b < a ∧ evalQ row a * evalQ row b < 0) && checks row b bs

private theorem checks_grid (r : List ℕ) (a : ℚ) (bs : List ℚ)
    (h : checks r a bs = true) : ∃ c, Grid (ofRow r) (a : ℝ) c bs.length := by
  induction bs generalizing a with
  | nil => exact ⟨_, Grid.nil _⟩
  | cons b bs ih =>
    simp only [checks, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨c, hg⟩ := ih b h.2
    refine ⟨c, Grid.cons (by exact_mod_cast h.1.1) ?_ hg⟩
    rw [eval_ofRow, eval_ofRow]
    exact_mod_cast h.1.2

/-- A rational certificate transfers to the real polynomial and proves its exact degree. -/
theorem checked_row (r : List ℕ) (bs : List ℚ) (hzero : evalQ r 0 ≠ 0)
    (bound : r.length - 1 ≤ bs.length) (h : checks r 0 bs = true) :
    (ofRow r).natDegree = bs.length ∧ SimpleNegative (ofRow r) := by
  obtain ⟨c, hg⟩ := checks_grid r 0 bs h
  have hp : ofRow r ≠ 0 := by
    intro he
    have hz := eval_ofRow r 0
    rw [he, eval_zero] at hz
    exact hzero (by exact_mod_cast hz.symm)
  apply simpleNegative_of_grid hp (by simpa using hg)
  cases r with
  | nil => simp [ofRow]
  | cons a t => exact (degree_cons_le a t).trans bound

end BigDescents132
