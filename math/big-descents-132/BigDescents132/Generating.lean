import BigDescents132.Recurrence
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.LinearCombination

namespace BigDescents132.Series
open scoped Polynomial PowerSeries
open Finset

abbrev R := Polynomial ℝ
abbrev S := PowerSeries R
local notation "x" => (PowerSeries.X : S)
local notation "t" => (PowerSeries.C R Polynomial.X : S)

/-- The coefficient of rank n is the literal polynomial B (n+1). -/
noncomputable def total : S := PowerSeries.mk (fun n => B (n+1))
noncomputable def first : S := PowerSeries.mk (fun n => A (n+1))
noncomputable def other : S := PowerSeries.mk (fun n => C (n+1))

theorem total_split : total = first + other := by
  apply PowerSeries.ext
  intro n
  simpa [total, first, other] using B_eq_A_add_C n

theorem first_eq : first = 1 + x * first + x * (t * other) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [first]
  | succ n => simpa [first, other, PowerSeries.coeff_C_mul] using A_recurrence n

theorem other_eq : other = x * total + x * (x * (t * (total * total))) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [other]
  | succ n =>
    cases n with
    | zero => simpa [total, other] using C_recurrence 0
    | succ n =>
      simp only [map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul]
      simp only [PowerSeries.coeff_mul, total, other, PowerSeries.coeff_mk]
      rw [Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => B (i+1) * B (j+1))]
      rw [C_recurrence]
      congr 2
      apply sum_congr rfl
      intro i hi
      have := mem_range.mp hi
      rw [show n+1-i = n-i+1 by omega]

/-- The algebraic generating function, before taking the square root. -/
theorem quadratic :
    ((1-x)^2-t*x^2) * total = 1 + t*x^2*(1-x+t*x)*total^2 := by
  linear_combination (1-x) * total_split + first_eq + (1-x+t*x) * other_eq

/-- The square branch associated to the actual generating function. -/
theorem discriminant :
    ((1-x)^2-t*x^2-2*t*x^2*(1-x+t*x)*total)^2 =
      1-4*x+6*(1-t)*x^2-4*(1-t)^2*x^3+(1-t)^2*x^4 := by
  linear_combination -4*t*x^2*(1-x+t*x)*quadratic

/-- Swap the rank and the big-descent indices in the two-variable series. -/
noncomputable def transpose : S →+* PowerSeries (PowerSeries ℝ) where
  toFun p := PowerSeries.mk fun k => PowerSeries.mk fun n => (PowerSeries.coeff R n p).coeff k
  map_zero' := by apply PowerSeries.ext; intro k; apply PowerSeries.ext; intro n; simp
  map_one' := by
    apply PowerSeries.ext; intro k; apply PowerSeries.ext; intro n
    cases n <;> cases k <;> simp [Polynomial.coeff_one]
  map_add' p q := by apply PowerSeries.ext; intro k; apply PowerSeries.ext; intro n; simp
  map_mul' p q := by
    apply PowerSeries.ext; intro k; apply PowerSeries.ext; intro n
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul, Polynomial.coeff_mul,
      Polynomial.finset_sum_coeff, map_sum]
    rw [sum_comm]

@[simp] theorem coeff_transpose (p : S) (k n : ℕ) :
    PowerSeries.coeff ℝ n (PowerSeries.coeff _ k (transpose p)) =
      (PowerSeries.coeff R n p).coeff k := by simp [transpose]

@[simp] theorem transpose_rank : transpose x = PowerSeries.C _ PowerSeries.X := by
  apply PowerSeries.ext; intro k; apply PowerSeries.ext; intro n
  rw [coeff_transpose]
  cases n with
  | zero => cases k <;> simp [PowerSeries.coeff_C]
  | succ n => cases n <;> cases k <;> simp [PowerSeries.coeff_C, PowerSeries.coeff_X, Polynomial.coeff_one]

@[simp] theorem transpose_weight : transpose t = PowerSeries.X := by
  apply PowerSeries.ext; intro k; apply PowerSeries.ext; intro n
  rw [coeff_transpose]
  cases k with
  | zero => cases n <;> simp [PowerSeries.coeff_C, PowerSeries.coeff_X, Polynomial.coeff_X]
  | succ k => cases k <;> cases n <;> simp [PowerSeries.coeff_C, PowerSeries.coeff_X, Polynomial.coeff_X]

end BigDescents132.Series
