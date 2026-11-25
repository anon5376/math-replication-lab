import BigDescents132.Recurrence
import BigDescents132.RootCount

namespace BigDescents132
open Polynomial Finset
open scoped Polynomial

private def NN (p : Polynomial ℝ) := ∀ k, 0 ≤ p.coeff k

private theorem nn_sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℝ)
    (h : ∀ i ∈ s, NN (f i)) : NN (∑ i ∈ s, f i) := by
  intro k
  rw [finset_sum_coeff]
  exact sum_nonneg fun i hi => h i hi k

private theorem nn_mul {p q : Polynomial ℝ} (hp : NN p) (hq : NN q) : NN (p*q) := by
  intro k
  rw [coeff_mul]
  exact sum_nonneg fun ij _ => mul_nonneg (hp ij.1) (hq ij.2)

private theorem nn_weight (w : List ℕ) : NN (weight w) := by
  intro k
  simp only [weight, coeff_X_pow]
  split <;> norm_num

theorem B_coeff_nonneg (n k : ℕ) : 0 ≤ (B n).coeff k := by
  rw [B_sum]
  exact nn_sum _ _ (fun w _ => nn_weight w) k

private theorem nn_A (m : ℕ) : NN (A (m+1)) := by
  rw [A]
  exact nn_sum _ _ (fun w _ => nn_weight w)

private theorem nn_C (m : ℕ) : NN (BigDescents132.C (m+1)) := by
  rw [BigDescents132.C]
  exact nn_sum _ _ (fun w _ => nn_weight w)

private theorem nn_X : NN (X : Polynomial ℝ) := by
  intro k
  rw [coeff_X]
  split <;> norm_num

private theorem deg_mono {p q : Polynomial ℝ} (hp : NN p) (h : ∀ k, p.coeff k ≤ q.coeff k) :
    p.natDegree ≤ q.natDegree := by
  by_cases he : p = 0
  · simp [he]
  by_contra! hlt
  have hk := h p.natDegree
  rw [coeff_eq_zero_of_natDegree_lt hlt] at hk
  have hz := (hp _).antisymm' hk
  exact he (leadingCoeff_eq_zero.mp (by simpa using hz))

private theorem deg_plus {p q : Polynomial ℝ} (hp : NN p) (hq : NN q) :
    (p+q).natDegree = max p.natDegree q.natDegree := by
  apply (natDegree_add_le p q).antisymm
  apply max_le
  · exact deg_mono hp (fun k => by rw [coeff_add]; linarith [hq k])
  · exact deg_mono hq (fun k => by rw [coeff_add]; linarith [hp k])

theorem constant_terms (m : ℕ) : (B (m+1)).eval 0 = m+1 ∧ (A (m+1)).eval 0 = 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have ha : (A (m+2)).eval 0 = 1 := by simp [A_recurrence, ih.2]
    refine ⟨?_,ha⟩
    rw [B_eq_A_add_C, eval_add, ha, C_recurrence]
    simp [ih.1]
    ring

private theorem C_ne (m : ℕ) : BigDescents132.C (m+2) ≠ 0 := by
  intro he
  have h := congrArg (Polynomial.eval 0) (C_recurrence m)
  rw [he, eval_zero] at h
  simp [constant_terms] at h
  linarith [show (0:ℝ) ≤ m by positivity]

/-- Degree of the complementary class from rank 2 onwards. -/
def otherDegree (n : ℕ) := (2*n-3)/3

private theorem degrees (n : ℕ) : (B n).natDegree = expectedDegree n ∧
    (BigDescents132.C n).natDegree = otherDegree n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [BigDescents132.C, expectedDegree, otherDegree]
    | 1 => simp [expectedDegree, otherDegree]
    | 2 => norm_num [B_eq_A_add_C, A_recurrence, C_recurrence, expectedDegree, otherDegree]
    | m+3 =>
      let S := ∑ i ∈ range (m+1), B (i+1) * B (m+1-i)
      have hSnn : NN S := nn_sum _ _ (fun i _ => nn_mul (B_coeff_nonneg _) (B_coeff_nonneg _))
      have inS (k : ℕ) : (B (m+1)).coeff k ≤ S.coeff k := by
        dsimp [S]
        rw [finset_sum_coeff]
        simpa using (single_le_sum (f:=fun i => (B (i+1)*B (m+1-i)).coeff k)
          (fun i _ => nn_mul (B_coeff_nonneg _) (B_coeff_nonneg _) k) (show 0 ∈ range (m+1) by simp))
      have sdeg : S.natDegree = expectedDegree (m+1) := by
        apply le_antisymm
        · apply natDegree_sum_le_of_forall_le
          intro i hi
          have hi' := mem_range.mp hi
          apply natDegree_mul_le.trans
          rw [(ih (i+1) (by omega)).1, (ih (m+1-i) (by omega)).1]
          unfold expectedDegree
          omega
        · rw [← (ih (m+1) (by omega)).1]
          exact deg_mono (B_coeff_nonneg _) inS
      have hsne : S ≠ 0 := by
        intro he
        have hc := inS 0
        rw [he, coeff_zero, coeff_zero_eq_eval_zero, (constant_terms m).1] at hc
        linarith [show (0:ℝ) ≤ m by positivity]
      have cdeg : (BigDescents132.C (m+3)).natDegree = otherDegree (m+3) := by
        rw [C_recurrence]
        change (B (m+2)+X*S).natDegree = _
        rw [deg_plus (B_coeff_nonneg _) (nn_mul nn_X hSnn), natDegree_mul X_ne_zero hsne,
          natDegree_X, sdeg, (ih (m+2) (by omega)).1]
        unfold otherDegree expectedDegree
        omega
      have hap : (A (m+2)).natDegree ≤ expectedDegree (m+2) := by
        have h := (ih (m+2) (by omega)).1
        rw [B_eq_A_add_C, deg_plus (nn_A _) (nn_C _)] at h
        exact h ▸ le_max_left _ _
      refine ⟨?_, cdeg⟩
      rw [B_eq_A_add_C, deg_plus (nn_A _) (nn_C _), cdeg, A_recurrence,
        deg_plus (nn_A _) (nn_mul nn_X (nn_C _)), natDegree_mul X_ne_zero (C_ne m),
        natDegree_X, (ih (m+2) (by omega)).2]
      simp only [show m+1+1=m+2 by omega] at *
      unfold expectedDegree otherDegree at *
      omega

theorem degree_all (n : ℕ) : (B n).natDegree = expectedDegree n := (degrees n).1

theorem other_degree_all (n : ℕ) : (BigDescents132.C n).natDegree = otherDegree n := (degrees n).2

end BigDescents132
