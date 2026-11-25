import BigDescents132.PositiveFormula

namespace BigDescents132.Series
open Finset

def reducedTerm (n k m h : ℕ) : ℝ :=
  if m≤k ∧ k-m≤m+h ∧ 2*m+h+(k-m)≤n then
    (catalan m:ℝ)*((2*m+h).choose (2*m):ℝ)*((m+h).choose (k-m):ℝ)*
      ((k+(n-(2*m+h+(k-m)))).choose k:ℝ) else 0

theorem reduced_formula (n k : ℕ) : (B (n+1)).coeff k =
    ∑ mh∈range (n+1) ×ˢ range (n+1), reducedTerm n k mh.1 mh.2 := by
  rw [positive_coefficient_formula,Finset.sum_product]
  apply sum_congr rfl
  intro m _
  apply sum_congr rfl
  intro h _
  by_cases H : m≤k ∧ k-m≤m+h ∧ 2*m+h+(k-m)≤n
  · rw [Finset.sum_eq_single_of_mem (k-m) (mem_range.mpr (by omega))]
    · simp [reducedTerm,H,show m+(k-m)=k by omega,H.2.2]
    · intro b _ hb
      simp [show m+b ≠ k by omega]
  · rw [Finset.sum_eq_zero]
    · simp only [reducedTerm,if_neg H]
    · intro b hb
      have := mem_range.mp hb
      simp [show ¬(2*m+h+b≤n ∧ m+b=k) by omega]

/-- The finite set of (ℓ,h) with a=δ-h-2ℓ nonnegative. -/
def defectIndices (δ : ℕ) : Finset (ℕ × ℕ) :=
  (range (δ+1) ×ˢ range (δ+1)).filter fun lh => lh.2+2*lh.1≤δ

@[simp] theorem mem_defectIndices (δ l h : ℕ) :
    (l,h)∈defectIndices δ ↔ h+2*l≤δ := by simp [defectIndices]; omega

/-- A fixed defect diagonal is a finite sum indexed independently of p. -/
theorem diagonal_formula (p δ : ℕ) :
    (B (3*p+2*δ+1)).coeff (2*p+δ) =
      ∑ lh∈defectIndices δ, let l := lh.1; let h := lh.2; let a := δ-h-2*l
        (catalan (p+a+l):ℝ) * ((2*p+δ+a).choose h:ℝ) *
          ((p+a+l+h).choose a:ℝ) * ((2*p+δ+l).choose l:ℝ) := by
  rw [reduced_formula]
  symm
  apply Finset.sum_of_injOn (fun lh : ℕ × ℕ => (p+(δ-lh.2-2*lh.1)+lh.1,lh.2))
  · rintro ⟨l,h⟩ H ⟨l',h'⟩ H' eq
    have h₁ := congrArg Prod.fst eq
    have h₂ := congrArg Prod.snd eq
    have a := (mem_defectIndices δ l h).mp H
    have b := (mem_defectIndices δ l' h').mp H'
    exact Prod.ext (by dsimp at h₁ h₂; omega) (by simpa using h₂)
  · rintro ⟨l,h⟩ H
    have := (mem_defectIndices δ l h).mp H
    exact Finset.mem_product.mpr ⟨mem_range.mpr (by dsimp; omega),mem_range.mpr (by dsimp; omega)⟩
  · rintro ⟨m,h⟩ _ hn
    dsimp only [Prod.fst,Prod.snd] at *
    unfold reducedTerm
    split
    · rename_i H
      exfalso
      apply hn
      let l := p+δ-m-h
      have hl : h+2*l≤δ := by dsimp [l]; omega
      refine ⟨(l,h),(mem_defectIndices δ l h).mpr hl,Prod.ext ?_ rfl⟩
      dsimp [l]; omega
    · rfl
  · rintro ⟨l,h⟩ H
    have hδ := (mem_defectIndices δ l h).mp H
    let a := δ-h-2*l
    change (catalan (p+a+l):ℝ)*_ * _ * _ = reducedTerm _ _ (p+a+l) h
    have hsum : a+h+2*l=δ := by dsimp [a]; omega
    have H' : p+a+l ≤ 2*p+δ ∧ 2*p+δ-(p+a+l) ≤ p+a+l+h ∧
        2*(p+a+l)+h+(2*p+δ-(p+a+l))≤3*p+2*δ := by omega
    simp only [reducedTerm,if_pos H']
    have e₁ : (2*p+δ+a).choose h = (2*(p+a+l)+h).choose (2*(p+a+l)) := by
      rw [show 2*p+δ+a=2*(p+a+l)+h by omega]
      exact Nat.choose_symm_of_eq_add (by omega)
    have e₂ : (p+a+l+h).choose a=(p+a+l+h).choose (2*p+δ-(p+a+l)) :=
      Nat.choose_symm_of_eq_add (by omega)
    have e₃ : (2*p+δ+l).choose l =
        (2*p+δ+(3*p+2*δ-(2*(p+a+l)+h+(2*p+δ-(p+a+l))))).choose (2*p+δ) := by
      rw [show 3*p+2*δ-(2*(p+a+l)+h+(2*p+δ-(p+a+l)))=l by omega]
      exact Nat.choose_symm_of_eq_add (by omega)
    rw [e₁,e₂,e₃]

end BigDescents132.Series
