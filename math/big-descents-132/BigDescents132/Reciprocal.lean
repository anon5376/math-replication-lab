import BigDescents132.Degree
import BigDescents132.Generating
import Mathlib.Combinatorics.Enumerative.Catalan

namespace BigDescents132.Series
open Polynomial Finset Set
open scoped Polynomial PowerSeries

/-- Index the row of rank m+1 by the nonnegative defect 2m-3k. -/
noncomputable def defectRow (m : ℕ) : Polynomial ℝ :=
  (B (m+1)).sum (fun k a => Polynomial.monomial (2*m-3*k) a)

private theorem defect_nonneg (m : ℕ) {k : ℕ} (hk : k ∈ (B (m+1)).support) : 3*k ≤ 2*m := by
  have h := Polynomial.le_natDegree_of_ne_zero (mem_support_iff.mp hk)
  rw [degree_all] at h
  unfold expectedDegree at h
  omega

theorem defectRow_eval (m : ℕ) {v : ℝ} (hv : v ≠ 0) :
    (defectRow m).eval v = v^(2*m) * (B (m+1)).eval (v⁻¹^3) := by
  rw [defectRow, eval_sum, eval_eq_sum (p:=B (m+1))]
  simp only [Polynomial.sum, Finset.mul_sum, eval_monomial]
  apply sum_congr rfl
  intro k hk
  rw [pow_sub₀ _ hv (defect_nonneg m hk), ← pow_mul, inv_pow]
  ring

noncomputable def defectTotal : S := PowerSeries.mk defectRow

theorem defect_specialize {v : ℝ} (hv : v ≠ 0) :
    PowerSeries.map (evalRingHom v) defectTotal =
      PowerSeries.rescale (v^2) (PowerSeries.map (evalRingHom (v⁻¹^3)) total) := by
  apply PowerSeries.ext
  intro m
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_rescale, PowerSeries.coeff_mk, total,
    defectTotal, coe_evalRingHom, defectRow_eval m hv, pow_mul]

local notation "x" => (PowerSeries.X : S)
local notation "v₀" => (PowerSeries.C R Polynomial.X : S)

private theorem regrade {K : Type*} [CommRing K] (v u r y : K) (hu : u*v^3=1)
    (hq : ((1-v^2*r)^2-u*(v^2*r)^2)*y = 1+u*(v^2*r)^2*(1-v^2*r+u*(v^2*r))*y^2) :
    ((1-r*v^2)^2-r^2*v)*y = 1+(r^2*v*(1-r*v^2)+r^3)*y^2 := by
  have e : u*(v^2*r)^2 = r^2*v := by linear_combination r^2*v*hu
  rw [e] at hq
  linear_combination hq + r^3*y^2*hu

/-- After reversing the grading the quadratic is regular at v=0. -/
theorem defect_quadratic :
    ((1-x*v₀^2)^2-x^2*v₀)*defectTotal =
      1+(x^2*v₀*(1-x*v₀^2)+x^3)*defectTotal^2 := by
  apply PowerSeries.ext
  intro m
  apply Polynomial.eq_of_infinite_eval_eq
  refine (Set.Ioi_infinite (0:ℝ)).mono ?_
  intro v hv
  have hv' : v ≠ 0 := (Set.mem_Ioi.mp hv).ne'
  change (PowerSeries.coeff R m _).eval v = (PowerSeries.coeff R m _).eval v
  change (evalRingHom v) (PowerSeries.coeff R m _) = (evalRingHom v) (PowerSeries.coeff R m _)
  rw [← PowerSeries.coeff_map, ← PowerSeries.coeff_map]
  apply congrArg
  simp only [map_add, map_mul, map_sub, map_pow, map_one, PowerSeries.map_X,
    PowerSeries.map_C, coe_evalRingHom, eval_X, defect_specialize hv']
  let Xr := (PowerSeries.X : PowerSeries ℝ)
  let cv := PowerSeries.C ℝ v
  have h := congrArg (PowerSeries.rescale (v^2))
    (congrArg (PowerSeries.map (evalRingHom (v⁻¹^3))) quadratic)
  have rc (c : ℝ) : PowerSeries.rescale (v^2) (PowerSeries.C ℝ c) = PowerSeries.C ℝ c := by
    apply PowerSeries.ext; intro n
    cases n <;> simp [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  simp only [map_add, map_mul, map_sub, map_pow, map_one, PowerSeries.map_X, PowerSeries.map_C,
    coe_evalRingHom, eval_X, PowerSeries.rescale_X, rc] at h
  have rel : PowerSeries.C ℝ (v⁻¹)^3 * cv^3 = 1 := by
    dsimp [cv]
    rw [← map_pow, ← map_pow, ← map_mul, inv_pow, inv_mul_cancel₀ (pow_ne_zero 3 hv'), map_one]
  exact regrade cv ((PowerSeries.C ℝ v⁻¹)^3) Xr _ rel h

theorem defect_read (m k : ℕ) (h : 3*k ≤ 2*m) :
    (defectRow m).coeff (2*m-3*k) = (B (m+1)).coeff k := by
  simp only [defectRow, coeff_sum, Polynomial.sum, finset_sum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i hi hne
    have := defect_nonneg m hi
    split
    · omega
    · rfl
  · intro h
    simp [Polynomial.not_mem_support_iff.mp h]

/-- The zero-defect series obeys the Catalan equation with rank step three. -/
noncomputable def topSeries : PowerSeries ℝ := PowerSeries.map (evalRingHom 0) defectTotal

theorem top_catalan_equation :
    topSeries = 1 + PowerSeries.X^3 * (topSeries * topSeries) := by
  have h := congrArg (PowerSeries.map (evalRingHom (0:ℝ))) defect_quadratic
  simpa [topSeries, coe_evalRingHom, pow_two] using h

private theorem top_coeff_vanish (m : ℕ) (hm : m%3 ≠ 0) : PowerSeries.coeff ℝ m topSeries = 0 := by
  simp only [topSeries, PowerSeries.coeff_map, defectTotal, PowerSeries.coeff_mk, coe_evalRingHom,
    defectRow, eval_sum, Polynomial.sum, eval_finset_sum, eval_monomial]
  apply sum_eq_zero
  intro k hk
  have := defect_nonneg m hk
  simp [zero_pow (by omega : 2*m-3*k ≠ 0)]

theorem top_coeff_catalan (m : ℕ) : PowerSeries.coeff ℝ (3*m) topSeries = catalan m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    have eqn := congrArg (PowerSeries.coeff ℝ (3*m)) top_catalan_equation
    cases m with
    | zero => simpa using eqn
    | succ k =>
      rw [show 3*(k+1)=3*k+3 by omega, map_add, PowerSeries.coeff_X_pow_mul,
        PowerSeries.coeff_one, if_neg (by omega), zero_add, PowerSeries.coeff_mul] at eqn
      rw [show 3*(k+1)=3*k+3 by omega, eqn, catalan_succ', Nat.cast_sum]
      symm
      apply Finset.sum_of_injOn (fun ij : ℕ × ℕ => (3*ij.1,3*ij.2))
      · intro a _ b _ he
        have h1 := congrArg Prod.fst he
        have h2 := congrArg Prod.snd he
        exact Prod.ext (by simpa using h1) (by simpa using h2)
      · rintro ⟨a,b⟩ hab
        exact Finset.mem_antidiagonal.mpr (by dsimp; have := Finset.mem_antidiagonal.mp hab; omega)
      · rintro ⟨a,b⟩ hab hi
        have hab' := Finset.mem_antidiagonal.mp hab
        by_cases ha : a%3=0
        · have hb : b%3=0 := by dsimp at hab'; omega
          exfalso
          apply hi
          exact ⟨(a/3,b/3), Finset.mem_antidiagonal.mpr (by dsimp at *; omega),
            Prod.ext (by dsimp; omega) (by dsimp; omega)⟩
        · simp [top_coeff_vanish a ha]
      · rintro ⟨a,b⟩ hab
        have := Finset.mem_antidiagonal.mp hab
        simp only [Prod.fst, Prod.snd] at this ⊢
        rw [ih a (by omega), ih b (by omega), Nat.cast_mul]

/-- At rank 3m+1 the leading coefficient is exactly Catalan(m). -/
theorem leading_coefficient_mod_one (m : ℕ) : (B (3*m+1)).coeff (2*m) = catalan m := by
  have ht := top_coeff_catalan m
  simp only [topSeries, PowerSeries.coeff_map, defectTotal, PowerSeries.coeff_mk, coe_evalRingHom,
    ← coeff_zero_eq_eval_zero] at ht
  have h := defect_read (3*m) (2*m) (by omega)
  rw [show 2*(3*m)-3*(2*m)=0 by omega] at h
  exact h.symm.trans ht

end BigDescents132.Series
