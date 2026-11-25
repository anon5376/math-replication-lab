import BigDescents132.Generating
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Analysis.SpecialFunctions.Choose

namespace BigDescents132.Series
open Finset Filter
open scoped Polynomial PowerSeries Topology
abbrev Stream := PowerSeries ℝ
local notation "z" => (PowerSeries.X : Stream)
local notation "T" => (PowerSeries.X : PowerSeries Stream)
local notation "cst" => PowerSeries.C Stream

/-- Multiply column k by (1-x)^(3k+2). All the resulting columns are polynomials. -/
noncomputable def normalized : PowerSeries Stream :=
  cst ((1-z)^2) * PowerSeries.rescale ((1-z)^3) (transpose total)

theorem normalized_eq : normalized =
    1 + T * (cst (z^2*(1-z)) * normalized) +
      T * (cst (z^2) * (normalized * normalized)) +
      T * (T * (cst (z^3*(1-z)^2) * (normalized * normalized))) := by
  have rc : PowerSeries.rescale ((1-z)^3) (cst z) = cst z := by
    apply PowerSeries.ext; intro n
    cases n <;> simp [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  have h := congrArg (PowerSeries.rescale ((1-z)^3)) (congrArg transpose quadratic)
  simp only [map_mul, map_add, map_sub, map_one, map_pow, transpose_rank, transpose_weight,
    rc, PowerSeries.rescale_X] at h
  unfold normalized
  simp only [map_mul, map_pow, map_sub, map_one] at h ⊢
  linear_combination h

/-- A polynomial numerator with the specified value at the singular point x=1. -/
private def Lifts (f : Stream) (a : ℝ) : Prop :=
  ∃ p : Polynomial ℝ, (p : Stream) = f ∧ p.eval 1 = a

private theorem lift_zero : Lifts 0 0 := ⟨0, by simp, by simp⟩
private theorem lift_one : Lifts 1 1 := ⟨1, by simp, by simp⟩
private theorem lift_mul {f g : Stream} {a b : ℝ} (h : Lifts f a) (h' : Lifts g b) :
    Lifts (f*g) (a*b) := by
  obtain ⟨p,rfl,rfl⟩ := h
  obtain ⟨q,rfl,rfl⟩ := h'
  exact ⟨p*q, by simp, by simp⟩

private theorem lift_add {f g : Stream} {a b : ℝ} (h : Lifts f a) (h' : Lifts g b) :
    Lifts (f+g) (a+b) := by
  obtain ⟨p,rfl,rfl⟩ := h
  obtain ⟨q,rfl,rfl⟩ := h'
  exact ⟨p+q, by simp, by simp⟩

private theorem lift_sum {ι : Type*} (s : Finset ι) (f : ι → Stream) (a : ι → ℝ)
    (h : ∀ i ∈ s, Lifts (f i) (a i)) : Lifts (∑ i ∈ s, f i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lift_zero
  | insert i s hi ih =>
    simp only [sum_insert hi]
    exact lift_add (h _ (mem_insert_self _ _)) (ih (fun x hx => h x (mem_insert_of_mem hx)))

private theorem lifts_normalized (n : ℕ) :
    Lifts (PowerSeries.coeff Stream n normalized) (catalan n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have sq (k : ℕ) (hk : k < n) :
        Lifts (PowerSeries.coeff Stream k (normalized * normalized)) (catalan (k+1)) := by
      rw [PowerSeries.coeff_mul, catalan_succ', Nat.cast_sum]
      simp only [Nat.cast_mul]
      apply lift_sum
      intro ij hij
      have := Finset.mem_antidiagonal.mp hij
      exact lift_mul (ih ij.1 (by omega)) (ih ij.2 (by omega))
    have eqn := congrArg (PowerSeries.coeff Stream n) normalized_eq
    cases n with
    | zero => simpa [eqn] using lift_one
    | succ k =>
      simp only [map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_one, Nat.succ_ne_zero, if_false, zero_add] at eqn
      rw [eqn]
      have h₁ : Lifts (z^2*(1-z)) 0 :=
        ⟨Polynomial.X^2*(1-Polynomial.X), by simp, by simp⟩
      have h₂ : Lifts (z^2) 1 := ⟨Polynomial.X^2, by simp, by simp⟩
      have h₃ : Lifts (z^3*(1-z)^2) 0 :=
        ⟨Polynomial.X^3*(1-Polynomial.X)^2, by simp, by simp⟩
      have last : Lifts (PowerSeries.coeff Stream k
          (T * (cst (z^3*(1-z)^2) * (normalized * normalized)))) 0 := by
        cases k with
        | zero => simpa using lift_zero
        | succ j =>
          simpa only [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul, zero_mul]
            using lift_mul h₃ (sq j (by omega))
      simpa only [zero_mul, one_mul, zero_add, add_zero]
        using lift_add (lift_add (lift_mul h₁ (ih k (by omega))) (lift_mul h₂ (sq k (by omega)))) last

noncomputable def geom : Stream := PowerSeries.mk 1

/-- The exact ordinary generating function of column k has a pole of order 3k+2
with numerator evaluating to the Catalan number at 1. -/
theorem column_rational (k : ℕ) : ∃ p : Polynomial ℝ,
    p.eval 1 = catalan k ∧
    PowerSeries.coeff Stream k (transpose total) = (p : Stream) * geom^(3*k+2) := by
  obtain ⟨p,hp,hval⟩ := lifts_normalized k
  refine ⟨p,hval,?_⟩
  rw [hp, normalized, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale]
  have h : geom * (1-z) = 1 := PowerSeries.mk_one_mul_one_sub_eq_one ℝ
  have hpow := congrArg (fun v : Stream => v^(3*k+2)) h
  simp only [mul_pow, one_pow] at hpow
  calc
    _ = (geom^(3*k+2) * (1-z)^(3*k+2)) * PowerSeries.coeff Stream k (transpose total) := by
      rw [hpow, one_mul]
    _ = _ := by rw [pow_add (1-z), pow_mul (1-z)]
                generalize 1-z = u
                ring

private theorem linear_ratio (a i : ℕ) : Tendsto
    (fun n : ℕ => ((n+a : ℕ) : ℝ) / ((n+i+1 : ℕ) : ℝ)) atTop (𝓝 1) := by
  have h := (tendsto_natCast_div_add_atTop ((i:ℝ)+1-a)).comp (tendsto_add_atTop_nat a)
  convert h using 1
  ext n
  dsimp
  push_cast
  ring_nf

private theorem choose_ratio (d i : ℕ) : Tendsto
    (fun n : ℕ => ((n+d).choose d : ℝ) / ((n+i+1 : ℕ) : ℝ)^d) atTop (𝓝 (1/(d.factorial:ℝ))) := by
  have asc (j : ℕ) : Tendsto (fun n : ℕ =>
      ((n+1).ascFactorial j : ℝ) / ((n+i+1 : ℕ) : ℝ)^j) atTop (𝓝 1) := by
    induction j with
    | zero => simp
    | succ j ih =>
      have h := (linear_ratio (1+j) i).mul ih
      convert h using 1
      · ext n
        simp only [Nat.ascFactorial_succ, Nat.cast_mul, pow_succ, Nat.add_assoc]
        ring
      · norm_num
  have h := (asc d).div_const (d.factorial : ℝ)
  convert h using 1
  ext n
  rw [Nat.ascFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have hf : (d.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- Transfer the coefficient asymptotics of a finite numerator times (1-x)^(-d-1). -/
theorem transfer_polynomial (p : Polynomial ℝ) (d : ℕ) : Tendsto
    (fun n : ℕ => PowerSeries.coeff ℝ n ((p : Stream) * geom^(d+1)) / ((n+1 : ℕ) : ℝ)^d)
    atTop (𝓝 (p.eval 1 / (d.factorial : ℝ))) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa [add_mul, add_div] using hp.add hq
  | monomial i a =>
    rw [← tendsto_add_atTop_iff_nat i]
    have h := (choose_ratio d i).const_mul a
    convert h using 1
    · ext n
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_C,
        Polynomial.coe_pow, Polynomial.coe_X]
      rw [show PowerSeries.C ℝ a * z^i * geom^(d+1) =
        PowerSeries.C ℝ a * (geom^(d+1) * z^i) by ring,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow, geom,
        PowerSeries.mk_one_pow_eq_mk_choose_add, PowerSeries.coeff_mk, Nat.add_comm d n]
      ring
    · simp [div_eq_mul_inv]

/-- Every fixed coefficient of the literal permutation polynomial has its
Catalan leading asymptotic at the small endpoint. -/
theorem small_coefficient_limit (k : ℕ) : Tendsto
    (fun n : ℕ => (B n).coeff k / (n:ℝ)^(3*k+1))
    atTop (𝓝 ((catalan k:ℝ) / (3*k+1).factorial)) := by
  obtain ⟨p,hval,h⟩ := column_rational k
  rw [← hval, ← tendsto_add_atTop_iff_nat 1]
  have ht := transfer_polynomial p (3*k+1)
  simp only [show 3*k+1+1 = 3*k+2 by omega, ← h, coeff_transpose, total, PowerSeries.coeff_mk] at ht
  exact ht

end BigDescents132.Series
