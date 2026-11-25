import BigDescents132.Maximum

namespace BigDescents132
open Polynomial
open scoped Polynomial
open Maximum

def wordSet (n : ℕ) := (words n).toFinset
@[simp] theorem mem_wordSet {n : ℕ} {w : List ℕ} : w ∈ wordSet n ↔ w ∈ words n := by
  simp [wordSet]

noncomputable def weight (w : List ℕ) : ℝ[X] := X ^ bigDescents w

theorem B_sum (n : ℕ) : B n = ∑ w ∈ wordSet n, weight w :=
  (List.sum_toFinset weight (words_nodup n)).symm

/-- Nonempty avoiders whose first entry is the maximum. -/
noncomputable def A : ℕ → ℝ[X]
  | 0 => 0
  | m+1 => ∑ w ∈ (wordSet (m+1)).filter (fun w => w.head? = some m), weight w

/-- Nonempty avoiders whose first entry differs from the maximum. -/
noncomputable def C : ℕ → ℝ[X]
  | 0 => 0
  | m+1 => ∑ w ∈ (wordSet (m+1)).filter (fun w => w.head? ≠ some m), weight w

theorem B_eq_A_add_C (m : ℕ) : B (m+1) = A (m+1) + C (m+1) := by
  rw [B_sum, A, C, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : w.head? = some m <;> simp [h]

theorem wordSet_zero : wordSet 0 = {[]} := rfl
theorem wordSet_one : wordSet 1 = {[0]} := rfl
@[simp] theorem B_zero : B 0 = 1 := by simp [B_sum, wordSet_zero, weight, bigDescents]
@[simp] theorem A_one : A 1 = 1 := by simp [A, wordSet_one, Finset.sum_filter, weight, bigDescents]
@[simp] theorem C_one : C 1 = 0 := by simp [C, wordSet_one, Finset.sum_filter]
@[simp] theorem B_one : B 1 = 1 := by rw [B_eq_A_add_C 0, A_one, C_one, add_zero]

namespace Maximum
/-- The literal weighted sum with the maximum at zero-based position i. -/
noncomputable def fiber (m i : ℕ) : ℝ[X] :=
  ∑ w ∈ (wordSet (m+1)).filter (fun w => w.idxOf m = i), weight w

theorem B_fibers (m : ℕ) : B (m+1) = ∑ i ∈ Finset.range (m+1), fiber m i := by
  rw [B_sum]
  symm
  apply Finset.sum_fiberwise_of_maps_to
  intro w hw
  have h := mem_wordSet.mp hw
  have hm : m ∈ w := (word_iff.mp h).1.mem_iff.mpr (List.mem_range.mpr (by omega))
  exact Finset.mem_range.mpr (length_word h ▸ List.idxOf_lt_length_iff.mpr hm)

theorem fiber_front (m : ℕ) : fiber m 0 = A (m+1) := by
  unfold fiber A
  congr 1
  ext w
  simp only [Finset.mem_filter, mem_wordSet, and_congr_right_iff]
  intro hw
  cases w with
  | nil => have := length_word hw; simp at this
  | cons a t =>
    by_cases h : a=m
    · simp [h]
    · simp [h, List.idxOf_cons_ne t h]

theorem fiber_pairs (i j : ℕ) : fiber (i+j) i =
    ∑ u ∈ wordSet i, ∑ v ∈ wordSet j, weight (join i j u v) := by
  calc
    _ = ∑ p ∈ wordSet i ×ˢ wordSet j, weight (join i j p.1 p.2) := by
      symm
      apply Finset.sum_bij (fun p _ => join i j p.1 p.2)
      · rintro ⟨u,v⟩ h
        obtain ⟨hu,hv⟩ := Finset.mem_product.mp h
        exact Finset.mem_filter.mpr ⟨mem_wordSet.mpr (join_mem (mem_wordSet.mp hu)
          (mem_wordSet.mp hv)), cut_join (mem_wordSet.mp hu)⟩
      · rintro ⟨u,v⟩ h ⟨u',v'⟩ h' he
        have hinj := join_inj (mem_wordSet.mp (Finset.mem_product.mp h).1)
          (mem_wordSet.mp (Finset.mem_product.mp h').1) he
        exact Prod.ext hinj.1 hinj.2
      · intro w hw
        obtain ⟨hw,hi⟩ := Finset.mem_filter.mp hw
        obtain ⟨u,hu,v,hv,he⟩ := decompose (mem_wordSet.mp hw) hi
        exact ⟨(u,v), Finset.mem_product.mpr ⟨mem_wordSet.mpr hu,mem_wordSet.mpr hv⟩, he.symm⟩
      · intro _ _; rfl
    _ = _ := Finset.sum_product _ _ _

theorem fiber_last (i : ℕ) : fiber i i = B i := by
  have h := fiber_pairs i 0
  simp only [Nat.add_zero, wordSet_zero, Finset.sum_singleton] at h
  rw [h, B_sum]
  apply Finset.sum_congr rfl
  intro u hu
  simp [weight, drops_join (mem_wordSet.mp hu), bigDescents]

theorem fiber_interior (i j : ℕ) :
    fiber (i+1+(j+1)) (i+1) = X * (B (i+1) * B (j+1)) := by
  rw [fiber_pairs, B_sum, B_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  simp only [weight, drops_interior (mem_wordSet.mp hu) (mem_wordSet.mp hv), pow_add, pow_one]
  ring

end Maximum

theorem A_recurrence (k : ℕ) : A (k+2) = A (k+1) + X * C (k+1) := by
  rw [← fiber_front, ← Nat.zero_add (k+1), fiber_pairs]
  simp only [wordSet_zero, Finset.sum_singleton, join, List.map_nil, List.nil_append, Nat.zero_add]
  rw [A, C, Finset.sum_filter, Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases h : v.head? = some k <;>
    simp [weight, drops_front (mem_wordSet.mp hv), h, pow_add]

/-- At rank k+2 the interior left block has length i+1, for 0 ≤ i < k. -/
theorem C_recurrence (k : ℕ) : C (k+2) =
    B (k+1) + X * ∑ i ∈ Finset.range k, B (i+1) * B (k-i) := by
  have h := B_fibers (k+1)
  rw [B_eq_A_add_C, Finset.sum_range_succ', fiber_front, Finset.sum_range_succ] at h
  have hc : C (k+2) = fiber (k+1) (k+1) + ∑ i ∈ Finset.range k, fiber (k+1) (i+1) := by
    apply add_left_cancel (a := A (k+2))
    rw [h]
    ring
  rw [hc, fiber_last, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hr : k-i = (k-i-1)+1 := by omega
  have hlen : k+1 = i+1+((k-i-1)+1) := by omega
  conv_lhs => rw [hlen, fiber_interior]
  rw [← hr]

end BigDescents132
