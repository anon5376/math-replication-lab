import BigDescents132.PositiveFormula
import Mathlib.Data.Nat.Choose.Vandermonde

namespace BigDescents132.AllRanks
open Finset
open scoped PowerSeries

/-- Coefficient of the geometric series of order a+1. -/
def seriesBin (a u : ℕ) := (a+u).choose a

theorem seriesBin_convolution (a b n : ℕ) :
    ∑ v∈range (n+1), seriesBin a v * seriesBin b (n-v) = seriesBin (a+b+1) n := by
  let G : PowerSeries ℤ := PowerSeries.mk 1
  have coeff (x i : ℕ) : PowerSeries.coeff ℤ i (G^(x+1))=seriesBin x i := by
    rw [show G^(x+1)=PowerSeries.mk (fun j => ((x+j).choose x:ℤ)) from
      PowerSeries.mk_one_pow_eq_mk_choose_add ℤ x,PowerSeries.coeff_mk]
    rfl
  have p : G^(a+1)*G^(b+1)=G^((a+b+1)+1) := by rw [←pow_add];congr 1;omega
  have H := congrArg (PowerSeries.coeff ℤ n) p
  rw [PowerSeries.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at H
  simp only [coeff] at H
  exact_mod_cast H

private theorem window (n j t : ℕ) (f : ℕ → ℕ) (H : j+t≤n) :
    ∑ h∈range (n+1), (if j≤h ∧ h≤j+t then f (h-j) else 0) =
    ∑ v∈range (t+1), f v := by
  let F := fun h => if j≤h ∧ h≤j+t then f (h-j) else 0
  change ∑ h∈range (n+1), F h=_
  have eq : ∑ h∈range (j+(t+1)), F h=∑ h∈range (n+1), F h := by
    apply sum_subset (Finset.range_mono (by omega))
    intro h _ hh
    have := mt mem_range.mpr hh
    simp [F, show ¬(j≤h ∧ h≤j+t) by omega]
  rw [←eq,Finset.sum_range_add]
  have zero : ∑ h∈range j, F h=0 := sum_eq_zero fun h hh => by
    have lt := mem_range.mp hh
    simp [F, not_le.mpr lt]
  rw [zero,zero_add]
  apply sum_congr rfl
  intro v hv
  have := mem_range.mp hv
  simp [F, show j≤j+v ∧ j+v≤j+t by omega]

private theorem nest_choose (m h j : ℕ) (le : j≤h) :
    seriesBin m h*h.choose j=seriesBin m j*seriesBin (m+j) (h-j) := by
  have H:=Nat.choose_mul (n:=m+h) (k:=m+j) (s:=m) (by omega) (by omega)
  simp only [show m+h-m=h by omega,show m+j-m=j by omega] at H
  unfold seriesBin
  rw [show m+j+(h-j)=m+h by omega]
  simpa only [mul_comm] using H.symm

private theorem marked_convolution (n m b j : ℕ) :
    ∑ h∈range (n+1), (if 2*m+h+b≤n then
        seriesBin (2*m) h*h.choose j*seriesBin (m+b) (n-(2*m+h+b)) else 0) =
    seriesBin (2*m) j*(n+1+m).choose (2*m+j+(m+b)+1) := by
  by_cases bound : 2*m+j+b≤n
  · let t:=n-(2*m+j+b)
    let f:=fun v => seriesBin (2*m) j*seriesBin (2*m+j) v*seriesBin (m+b) (t-v)
    have w := window n j t f (by dsimp [t];omega)
    calc
      _ = ∑ h∈range (n+1), (if j≤h ∧ h≤j+t then f (h-j) else 0) := by
        apply sum_congr rfl
        intro h _
        by_cases hj : j≤h
        · by_cases hn : 2*m+h+b≤n
          · rw [if_pos hn,if_pos ⟨hj,by dsimp [t];omega⟩,nest_choose _ _ _ hj]
            dsimp [f,t]
            rw [show n-(2*m+h+b)=n-(2*m+j+b)-(h-j) by omega]
          · rw [if_neg hn,if_neg (by dsimp [t];omega)]
        · simp [hj,Nat.choose_eq_zero_of_lt (by omega : h<j)]
      _ = ∑ v∈range (t+1), f v := w
      _ = seriesBin (2*m) j*seriesBin (2*m+j+(m+b)+1) t := by
        rw [←seriesBin_convolution,Finset.mul_sum]
        apply sum_congr rfl
        intro v _
        dsimp [f];ring
      _ = _ := by unfold seriesBin;rw [show 2*m+j+(m+b)+1+t=n+1+m by dsimp [t];omega]
  · rw [Nat.choose_eq_zero_of_lt (by omega : n+1+m<2*m+j+(m+b)+1),mul_zero]
    apply sum_eq_zero
    intro h _
    split_ifs with hh
    · rw [Nat.choose_eq_zero_of_lt (by omega : h<j)];simp
    · rfl

private theorem binomial_layer (n m b : ℕ) :
    ∑ h∈range (n+1), (if 2*m+h+b≤n then
        seriesBin (2*m) h*(m+h).choose b*seriesBin (m+b) (n-(2*m+h+b)) else 0) =
      ∑ i∈range (b+1), m.choose i*seriesBin (2*m) (b-i)*
        (n+1+m).choose (2*m+(b-i)+(m+b)+1) := by
  calc
    _ = ∑ h∈range (n+1), ∑ i∈range (b+1), m.choose i*
        (if 2*m+h+b≤n then seriesBin (2*m) h*h.choose (b-i)*seriesBin (m+b) (n-(2*m+h+b)) else 0) := by
      apply sum_congr rfl
      intro h _
      by_cases H : 2*m+h+b≤n
      · simp only [if_pos H,Nat.add_choose_eq m h b,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
          Finset.mul_sum,Finset.sum_mul]
        apply sum_congr rfl
        intro i _
        ring
      · simp [H]
    _ = _ := by
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro i _
      rw [←Finset.mul_sum,marked_convolution];ring

/-- A computable fixed-column binomial formula. The first argument is the rank. -/
def binomialCount (N k : ℕ) : ℕ :=
  ∑ m∈range (k+1), ∑ i∈range (k-m+1), catalan m*m.choose i*seriesBin (2*m) (k-m-i)*
    (N+m).choose (2*m+(k-m-i)+k+1)

private theorem select_mark (n k m h : ℕ) :
    (∑ b∈range (m+h+1), if 2*m+h+b≤n ∧ m+b=k then
      catalan m*seriesBin (2*m) h*(m+h).choose b*seriesBin (m+b) (n-(2*m+h+b)) else 0) =
    if m≤k then catalan m*(if 2*m+h+(k-m)≤n then seriesBin (2*m) h*
      (m+h).choose (k-m)*seriesBin (m+(k-m)) (n-(2*m+h+(k-m))) else 0) else 0 := by
  by_cases mk : m≤k
  · rw [if_pos mk,Finset.sum_eq_single (k-m)]
    · simp only [show m+(k-m)=k by omega,and_true]
      split_ifs <;> ring
    · intro b _ ne
      rw [if_neg (by omega)]
    · intro hbad
      have hn := mt mem_range.mpr hbad
      rw [Nat.choose_eq_zero_of_lt (by omega : m+h<k-m)]
      simp
  · rw [if_neg mk]
    exact sum_eq_zero fun b _ => if_neg (by omega)

theorem coefficient_eq_binomialCount (n k : ℕ) :
    (B (n+1)).coeff k=(binomialCount (n+1) k:ℝ) := by
  rw [Series.positive_coefficient_formula]
  let old (m h b : ℕ) := if 2*m+h+b≤n ∧ m+b=k then
      catalan m*seriesBin (2*m) h*(m+h).choose b*seriesBin (m+b) (n-(2*m+h+b)) else 0
  have castold : ∀ m h b, (old m h b:ℝ)=
      if 2*m+h+b≤n ∧ m+b=k then (catalan m:ℝ)*((2*m+h).choose (2*m):ℝ)*((m+h).choose b:ℝ)*
         ((m+b+(n-(2*m+h+b))).choose (m+b):ℝ) else 0 := by
    intro m h b;unfold old seriesBin;split_ifs <;>norm_cast
  simp_rw [←castold]
  let F := fun m => ∑ i∈range (k-m+1), catalan m*m.choose i*seriesBin (2*m) (k-m-i)*
    (n+1+m).choose (2*m+(k-m-i)+k+1)
  have eq : (∑ m∈range (n+1),∑ h∈range (n+1),∑ b∈range (m+h+1),old m h b) =
      ∑ m∈range (n+1), (if m≤k then F m else 0) := by
    apply sum_congr rfl
    intro m _
    simp only [old,select_mark]
    by_cases mk : m≤k
    · simp only [if_pos mk,←Finset.mul_sum,binomial_layer]
      dsimp [F]
      rw [Finset.mul_sum]
      apply sum_congr rfl;intro i _
      rw [show m+(k-m)=k by omega];ring
    · simp [mk]
  have pad : ∑ m∈range (n+1), (if m≤k then F m else 0) = ∑ m∈range (k+1), F m := by
    let T:=range ((max n k)+1)
    let f := fun m => if m≤k then F m else 0
    have no (m : ℕ) (big : n<m) (mk : m≤k) : F m=0 := by
      apply sum_eq_zero;intro i _
      rw [Nat.choose_eq_zero_of_lt (by omega : n+1+m<2*m+(k-m-i)+k+1)];simp
    have a : ∑ m∈range (n+1),f m=∑ m∈T,f m := by
      apply sum_subset (range_mono (by omega))
      intro m _ hm
      by_cases mk : m≤k
      · exact (if_pos mk).trans (no m (by have := mt mem_range.mpr hm;omega) mk)
      · exact if_neg mk
    have b : ∑ m∈range (k+1),f m=∑ m∈T,f m := by
      apply sum_subset (range_mono (by omega))
      intro m _ hm;exact if_neg (by have := mt mem_range.mpr hm;omega)
    apply (a.trans b.symm).trans
    apply sum_congr rfl;intro m hm
    exact if_pos (by have := mem_range.mp hm;omega)
  exact_mod_cast eq.trans pad

end BigDescents132.AllRanks
