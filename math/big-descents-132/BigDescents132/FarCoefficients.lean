import BigDescents132.Diagonals
import Mathlib.Analysis.SpecialFunctions.Choose

namespace BigDescents132.Series
open Finset Filter
open scoped Topology

theorem catalan_positive (n : ℕ) : 0<catalan n := by
  by_contra! h
  have H := succ_mul_catalan_eq_centralBinom n
  rw [show catalan n=0 by omega,mul_zero] at H
  exact (Nat.centralBinom_pos n).ne' H.symm

theorem catalan_ratio (n : ℕ) :
    (catalan (n+1):ℝ)/(catalan n:ℝ)=(4*n+2)/((n:ℝ)+2) := by
  have hp : (0:ℝ)<catalan n := by exact_mod_cast catalan_positive n
  have H := Nat.succ_mul_centralBinom_succ n
  rw [←succ_mul_catalan_eq_centralBinom (n+1),←succ_mul_catalan_eq_centralBinom n] at H
  have h : ((n:ℝ)+1)*(((n:ℝ)+1+1)*(catalan (n+1):ℝ)) =
      2*(2*(n:ℝ)+1)*(((n:ℝ)+1)*(catalan n:ℝ)) := by exact_mod_cast H
  have e : ((n:ℝ)+1)*(((n:ℝ)+2)*catalan (n+1)) =
      ((n:ℝ)+1)*((4*(n:ℝ)+2)*catalan n) := by linear_combination h
  have e' := mul_left_cancel₀ (show (n:ℝ)+1≠0 by positivity) e
  apply (div_eq_div_iff hp.ne' (by positivity)).mpr
  linarith only [e']

theorem catalan_uniform_le (p q m : ℕ) (hm : m≤p+q) :
    (catalan m:ℝ)≤(catalan p:ℝ)*4^q := by
  have step (i : ℕ) : (catalan i:ℝ)≤(catalan (i+1):ℝ) ∧
      (catalan (i+1):ℝ)≤(catalan i:ℝ)*4 := by
    have cpos : (0:ℝ)<catalan i := by exact_mod_cast catalan_positive i
    have e := catalan_ratio i
    have den : 0<(i:ℝ)+2 := by positivity
    have h₁ : 1≤(catalan (i+1):ℝ)/catalan i := by rw [e]; apply (le_div_iff₀ den).mpr; linarith
    have h₂ : (catalan (i+1):ℝ)/catalan i≤4 := by rw [e]; apply (div_le_iff₀ den).mpr; linarith
    exact ⟨by simpa using (le_div_iff₀ cpos).mp h₁,by simpa [mul_comm] using (div_le_iff₀ cpos).mp h₂⟩
  have mono : Monotone (fun i:ℕ => (catalan i:ℝ)) := monotone_nat_of_le_succ fun i => (step i).1
  apply (mono hm).trans
  clear hm m
  induction q with
  | zero => simp
  | succ q ih =>
    rw [pow_succ,←mul_assoc]
    exact (step (p+q)).2.trans (mul_le_mul_of_nonneg_right ih (by norm_num))

private theorem linear_scale (a b : ℝ) : Tendsto
    (fun n:ℕ => (a*n+b)/((n:ℝ)+1)) atTop (𝓝 a) := by
  have h := (tendsto_const_nhds (x:=a) (f:=atTop (α:=ℕ))).add
    (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (b-a))
  convert h using 1
  · ext n
    dsimp
    field_simp
    ring
  · simp

theorem catalan_shift_limit (k : ℕ) : Tendsto
    (fun n : ℕ => (catalan (n+k):ℝ)/(catalan n:ℝ)) atTop (𝓝 ((4:ℝ)^k)) := by
  have ratio : Tendsto (fun n : ℕ => (catalan (n+1):ℝ)/(catalan n:ℝ)) atTop (𝓝 4) := by
    have h := (linear_scale 4 (-2)).comp (tendsto_add_atTop_nat 1)
    apply h.congr'
    filter_upwards with n
    rw [catalan_ratio]
    dsimp
    push_cast
    ring
  induction k with
  | zero =>
    simp [show ∀ n:ℕ, (catalan n:ℝ)≠0 by intro n; exact_mod_cast (catalan_positive n).ne',tendsto_const_nhds]
  | succ k ih =>
    have h := ih.mul (ratio.comp (tendsto_add_atTop_nat k))
    rw [pow_succ]
    apply h.congr'
    filter_upwards with n
    dsimp
    rw [show n+(k+1)=n+k+1 by omega]
    have C (i : ℕ) : (catalan i:ℝ)≠0 := by exact_mod_cast (catalan_positive i).ne'
    field_simp [C]
    ring

private theorem affine_choose (A B k : ℕ) (hA : 0<A) : Tendsto
    (fun p:ℕ => ((A*p+B).choose k:ℝ)/((p:ℝ)+1)^k) atTop (𝓝 ((A:ℝ)^k/k.factorial)) := by
  have asc (r : ℕ) : Tendsto (fun p:ℕ => ((A*p+B).descFactorial r:ℝ)/((p:ℝ)+1)^r)
      atTop (𝓝 ((A:ℝ)^r)) := by
    induction r with
    | zero => simp [tendsto_const_nhds]
    | succ r ih =>
      rw [pow_succ]
      apply (ih.mul (linear_scale A ((B:ℝ)-r))).congr'
      filter_upwards [eventually_ge_atTop r] with p hp
      have hr : r≤A*p+B := by nlinarith [Nat.mul_le_mul_right p hA]
      dsimp
      rw [Nat.cast_mul,Nat.cast_sub hr,Nat.cast_add,Nat.cast_mul,pow_succ]
      field_simp
      ring
  have h := (asc k).div_const (k.factorial:ℝ)
  apply h.congr'
  filter_upwards with p
  rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
  field_simp
  ring

private theorem div_sum {α : Type*} (s : Finset α) (f : α → ℝ) (v : ℝ) :
    (∑ i∈s, f i)/v = ∑ i∈s, f i/v := by simp only [div_eq_mul_inv,Finset.sum_mul]

private theorem diag_term_limit (δ l h a : ℕ) (hs : a+h+2*l=δ) : Tendsto
    (fun p:ℕ =>
      (catalan (p+a+l):ℝ)*((2*p+δ+a).choose h:ℝ)*((p+a+l+h).choose a:ℝ)*
        ((2*p+δ+l).choose l:ℝ) / ((catalan p:ℝ)*((p:ℝ)+1)^δ))
    atTop (𝓝 (if l=0 then (4:ℝ)^a*2^h/((h.factorial:ℝ)*a.factorial) else 0)) := by
  have ht := ((((catalan_shift_limit (a+l)).mul (affine_choose 2 (δ+a) h (by decide))).mul
    (affine_choose 1 (a+l+h) a (by decide))).mul (affine_choose 2 (δ+l) l (by decide))).mul
    (tendsto_one_div_add_atTop_nhds_zero_nat.pow l)
  convert ht using 1
  · ext p
    dsimp
    simp only [one_mul,Nat.add_assoc]
    rw [←hs, show a+h+2*l=a+h+l+l by omega]
    simp only [pow_add,div_eq_mul_inv,mul_inv_rev,inv_pow,one_mul]
    ring
  · by_cases hl : l=0
    · subst l
      simp
      ring
    · simp [hl,zero_pow hl]

private theorem diag_weights (δ : ℕ) :
    (∑ lh∈defectIndices δ, if lh.1=0 then
      (4:ℝ)^(δ-lh.2-2*lh.1)*2^lh.2/((lh.2.factorial:ℝ)*(δ-lh.2-2*lh.1).factorial) else 0) =
      (6:ℝ)^δ/δ.factorial := by
  have h : (∑ j∈range (δ+1),
      (4:ℝ)^(δ-j)*2^j / ((j.factorial:ℝ)*(δ-j).factorial)) =
      ∑ lh∈defectIndices δ, if lh.1=0 then
        (4:ℝ)^(δ-lh.2-2*lh.1)*2^lh.2/((lh.2.factorial:ℝ)*(δ-lh.2-2*lh.1).factorial) else 0 := by
    apply Finset.sum_of_injOn (fun j : ℕ => (0,j))
    · intro j _ k _ he
      exact congrArg Prod.snd he
    · intro j hj
      simpa using Nat.le_of_lt_succ (mem_range.mp hj)
    · rintro ⟨l,j⟩ H hn
      have hj := (mem_defectIndices _ _ _).mp H
      by_cases hl : l=0
      · subst l
        exact False.elim (hn ⟨j,mem_range.mpr (by omega),rfl⟩)
      · simp [hl]
    · intro j _
      simp
  rw [←h,show (6:ℝ)=2+4 by norm_num,add_pow,div_sum]
  apply sum_congr rfl
  intro j hj
  have hle := Nat.le_of_lt_succ (mem_range.mp hj)
  have hc : ((δ.choose j:ℕ):ℝ)*j.factorial*(δ-j).factorial=δ.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hle
  field_simp
  linear_combination ((4:ℝ)^(δ-j)*2^j)*hc.symm

/-- All fixed defect diagonals have their Catalan and factorial asymptotic. -/
theorem diagonal_limit (δ : ℕ) : Tendsto
    (fun p : ℕ => (B (3*p+2*δ+1)).coeff (2*p+δ) /
        ((catalan p:ℝ)*((p:ℝ)+1)^δ)) atTop (𝓝 ((6:ℝ)^δ/δ.factorial)) := by
  simp_rw [diagonal_formula,div_sum]
  rw [←diag_weights]
  apply tendsto_finset_sum
  rintro ⟨l,h⟩ H
  have hsum := (mem_defectIndices _ _ _).mp H
  exact diag_term_limit δ l h (δ-h-2*l) (by omega)

private theorem normalize_ratio (u v c d q r N : ℝ) (e k : ℕ)
    (hc : c≠0) (hd : d≠0) (hq : q≠0) (hr : r≠0) (hN : N≠0) :
    u/(v*N^k) = u/(c*q^(e+k))/(v/(d*r^e))*(d/c)⁻¹*(q/r)^e*(q/N)^k := by
  by_cases hv : v=0
  · simp [hv]
  · rw [pow_add]
    field_simp
    ring

/-- Fixed reversed coefficients on every residue class, with the exact
normalization of the reciprocal endpoint series. -/
theorem reciprocal_coefficient_limit (e : Fin 3) (j : ℕ) : Tendsto
    (fun p : ℕ => let n := 3*p+2*e.val+1; let d := 2*p+e.val
      (B n).coeff (d-j) / ((B n).coeff d * (n:ℝ)^(3*j)))
    atTop (𝓝 ((e.val.factorial:ℝ) / (2^j*(e.val+3*j).factorial))) := by
  let δ := e.val+3*j
  rw [←tendsto_add_atTop_iff_nat (2*j)]
  have top := (diagonal_limit e.val).comp (tendsto_add_atTop_nat (2*j))
  have low := diagonal_limit δ
  have cat := (catalan_shift_limit (2*j)).inv₀ (by positivity)
  have fac : Tendsto (fun p:ℕ => ((p:ℝ)+1)/((p:ℝ)+2*j+1)) atTop (𝓝 1) := by
    have h := (linear_scale 1 (2*(j:ℝ)+1)).inv₀ (by norm_num)
    convert h using 1
    · ext p
      dsimp
      rw [inv_div]
      congr 1
      ring
    · norm_num
  have fac' : Tendsto (fun p:ℕ => ((p:ℝ)+1)/(3*(p:ℝ)+2*δ+1)) atTop (𝓝 (1/3)) := by
    have h := (linear_scale 3 (2*(δ:ℝ)+1)).inv₀ (by norm_num)
    convert h using 1
    · ext p
      dsimp
      rw [inv_div]
      congr 1
      ring
    · norm_num
  have topPos : 0<(6:ℝ)^e.val/e.val.factorial := by positivity
  have H := ((((low.div top topPos.ne').mul cat).mul (fac.pow e.val)).mul (fac'.pow (3*j)))
  convert H using 1
  · ext p
    dsimp [Function.comp_def]
    have en : 3*(p+2*j)+2*e.val+1=3*p+2*δ+1 := by dsimp [δ]; omega
    have ek : 2*(p+2*j)+e.val-j=2*p+δ := by dsimp [δ]; omega
    rw [en,ek]
    push_cast
    have Cp (i : ℕ) : (catalan i:ℝ)≠0 := by exact_mod_cast (catalan_positive i).ne'
    have ne₁ : (p:ℝ)+1≠0 := by positivity
    have ne₂ : (p:ℝ)+2*j+1≠0 := by positivity
    exact normalize_ratio _ _ _ _ _ _ _ e.val (3*j) (Cp p) (Cp _) ne₁ ne₂ (by positivity)
  · dsimp [δ]
    rw [pow_add,pow_mul,pow_mul,pow_mul]
    norm_num
    have hp : (16:ℝ)^j*27^j=2^j*216^j := by rw [←mul_pow,←mul_pow]; norm_num
    field_simp
    linear_combination ((e.val.factorial:ℝ)*(e.val+3*j).factorial*6^e.val)*hp

end BigDescents132.Series
