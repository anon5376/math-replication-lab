import BigDescents132.FarCoefficients
import BigDescents132.Degree
import BigDescents132.FarSigns
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Polynomial.Reverse

namespace BigDescents132.Series
open Finset Filter
open scoped Topology

private abbrev valid (n k m h : ℕ) := m≤k ∧ k-m≤m+h ∧ 2*m+h+(k-m)≤n

private def contributing (n k : ℕ) : Finset (ℕ × ℕ) :=
  (range (n+1) ×ˢ range (n+1)).filter fun mh => decide (valid n k mh.1 mh.2)

private theorem contrib_iff (n k : ℕ) (u : ℕ × ℕ) :
    u∈contributing n k ↔ u∈range (n+1) ×ˢ range (n+1) ∧ valid n k u.1 u.2 := by
  simp [contributing]

private theorem contrib_sum (n k : ℕ) : (B (n+1)).coeff k =
    ∑ mh∈contributing n k, reducedTerm n k mh.1 mh.2 := by
  rw [reduced_formula]
  symm
  apply Finset.sum_subset (filter_subset _ _)
  intro i hi hn
  have h : ¬valid n k i.1 i.2 := fun e => hn ((contrib_iff _ _ _).mpr ⟨hi,e⟩)
  simp only [reducedTerm,if_neg h]

private theorem contrib_card {n k δ : ℕ} (he : 2*n=3*k+δ) :
    (contributing n k).card≤(δ+1)^2 := by
  have h : (contributing n k).card ≤ (range (δ+1) ×ˢ range (δ+1)).card := by
    apply Finset.card_le_card_of_injOn (fun mh : ℕ × ℕ => (n-k-mh.1-mh.2,mh.2))
    · rintro ⟨m,h⟩ hm
      obtain ⟨u,v,w⟩ := ((contrib_iff _ _ _).mp hm).2
      exact mem_product.mpr ⟨mem_range.mpr (by dsimp at *; omega),mem_range.mpr (by dsimp at *; omega)⟩
    · rintro ⟨m,h⟩ hm ⟨m',h'⟩ hm' eq
      obtain ⟨u,v,w⟩ := ((contrib_iff _ _ _).mp hm).2
      obtain ⟨u',v',w'⟩ := ((contrib_iff _ _ _).mp hm').2
      have h₁ := congrArg Prod.fst eq
      have h₂ := congrArg Prod.snd eq
      exact Prod.ext (by dsimp at *; omega) (by simpa using h₂)
  simpa [pow_two] using h

private theorem term_envelope {n k δ p q m h : ℕ} (he : 2*n=3*k+δ)
    (hm : n-k≤p+q) (hv : valid n k m h) {A : ℝ} (hA : 0<A) :
    reducedTerm n k m h*A^δ ≤ (catalan p:ℝ)*4^q*((n:ℝ)+1)^δ*
      (Real.exp A)^2*Real.exp (A^2) := by
  obtain ⟨u,v,w⟩ := hv
  let a := m+h-(k-m)
  let l := n-(2*m+h+(k-m))
  have eq : a+h+2*l=δ := by dsimp [a,l]; omega
  let N := (n:ℝ)+1
  have hN : 1≤N := by dsimp [N]; linarith
  have hN0 := le_trans (by norm_num : (0:ℝ)≤1) hN
  have choose (d i:ℕ) (hi : i≤n) : (i.choose d:ℝ)≤N^d/d.factorial := by
    apply (Nat.choose_le_pow_div d i).trans
    gcongr
    exact (show (i:ℝ)≤n by exact_mod_cast hi).trans (by dsimp [N]; linarith)
  have bh : ((2*m+h).choose (2*m):ℝ)≤N^h/h.factorial := by
    rw [Nat.choose_symm_of_eq_add (n:=2*m+h) (a:=2*m) (b:=h) rfl]
    exact choose _ _ (by omega)
  have ba : ((m+h).choose (k-m):ℝ)≤N^a/a.factorial := by
    rw [Nat.choose_symm_of_eq_add (n:=m+h) (a:=k-m) (b:=a) (by dsimp [a]; omega)]
    exact choose _ _ (by omega)
  have bl : ((k+l).choose k:ℝ)≤N^l/l.factorial := by
    rw [Nat.choose_symm_of_eq_add (n:=k+l) (a:=k) (b:=l) rfl]
    exact choose _ _ (by dsimp [l]; omega)
  have bc := catalan_uniform_le p q m (by omega)
  have hb : A^δ=A^h*A^a*(A^2)^l := by rw [←pow_mul,←pow_add,←pow_add]; congr 1; omega
  have pn : N^(h+a+l)≤N^δ := pow_le_pow_right₀ hN (by omega)
  have hi : 0≤Real.exp A := (Real.exp_pos _).le
  have fc (j : ℕ) : 0≤(j.factorial:ℝ) := by positivity
  rw [reducedTerm,if_pos (show m≤k ∧ _ from ⟨u,v,w⟩)]
  change ((catalan m:ℝ)*_ * _ * ((k+l).choose k:ℝ))*A^δ≤_
  calc
    _ ≤ ((catalan p:ℝ)*4^q)*(N^h/h.factorial)*(N^a/a.factorial)*(N^l/l.factorial)*A^δ := by gcongr
    _ = ((catalan p:ℝ)*4^q)*N^(h+a+l)*(A^h/h.factorial)*(A^a/a.factorial)*((A^2)^l/l.factorial) := by
      rw [hb]; simp [pow_add]; ring
    _ ≤ ((catalan p:ℝ)*4^q)*N^δ*(Real.exp A)*(Real.exp A)*Real.exp (A^2) := by
      gcongr <;> first | exact Real.pow_div_factorial_le_exp A hA.le _ | exact Real.pow_div_factorial_le_exp (A^2) (sq_nonneg A) _
    _ = _ := by dsimp [N]; ring

/-- Uniform envelope in the defect, valid even when the reversed index moves
with the rank. A is an arbitrary positive exponential weight. -/
theorem coefficient_envelope {n k δ p q : ℕ} (he : 2*n=3*k+δ) (hm : n-k≤p+q)
    {A : ℝ} (hA : 0<A) :
    (B (n+1)).coeff k*A^δ ≤ ((δ+1:ℕ):ℝ)^2*(catalan p:ℝ)*4^q*((n:ℝ)+1)^δ*
      (Real.exp A)^2*Real.exp (A^2) := by
  let K := (catalan p:ℝ)*4^q*((n:ℝ)+1)^δ*(Real.exp A)^2*Real.exp (A^2)
  rw [contrib_sum,Finset.sum_mul]
  calc
    _ ≤ ∑ _∈contributing n k, K := by
      apply sum_le_sum
      intro i hi
      exact term_envelope he hm ((contrib_iff _ _ _).mp hi).2 hA
    _ = ((contributing n k).card:ℝ)*K := by simp
    _ ≤ ((δ+1:ℕ):ℝ)^2*K := mul_le_mul_of_nonneg_right (by exact_mod_cast contrib_card he) (by dsimp [K]; positivity)
    _ = _ := by dsimp [K]; ring

private def rank (p : ℕ) (e : Fin 3) := 3*p+2*e.val+1
private def deg (p : ℕ) (e : Fin 3) := 2*p+e.val

private theorem row_degree (p : ℕ) (e : Fin 3) : (B (rank p e)).natDegree=deg p e := by
  rw [degree_all]
  unfold expectedDegree rank deg
  have := e.isLt
  omega

private theorem top_rank_limit (e : Fin 3) : Tendsto
    (fun p:ℕ => (B (rank p e)).coeff (deg p e)/((catalan p:ℝ)*(rank p e:ℝ)^e.val))
    atTop (𝓝 ((2:ℝ)^e.val/e.val.factorial)) := by
  have hn : Tendsto (fun p:ℕ => (rank p e:ℝ)/((p:ℝ)+1)) atTop (𝓝 3) := by
    have ht := (tendsto_const_nhds (x:=(3:ℝ)) (f:=atTop (α:=ℕ))).add
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2*e.val-2:ℝ))
    convert ht using 1
    · ext p
      dsimp [rank]; push_cast; field_simp; ring
    · simp
  have H := (diagonal_limit e.val).div (hn.pow e.val) (by positivity)
  convert H using 1
  · ext p
    dsimp [deg,rank]
    push_cast
    have hp : (catalan p:ℝ)≠0 := by exact_mod_cast (catalan_positive p).ne'
    field_simp [hp]
    ring
  · have eq : (6:ℝ)^e.val=2^e.val*3^e.val := by rw [←mul_pow]; norm_num
    rw [eq]
    field_simp
    ring

private noncomputable def scaledTerm (p : ℕ) (e : Fin 3) (j : ℕ) (y : ℝ) :=
  (B (rank p e)).reverse.coeff j / ((B (rank p e)).coeff (deg p e)*(rank p e:ℝ)^(3*j))*y^j

private theorem term_limit (e : Fin 3) (j : ℕ) (y : ℝ) :
    Tendsto (fun p:ℕ => scaledTerm p e j y) atTop
      (𝓝 ((e.val.factorial:ℝ)*(y/2)^j/(3*j+e.val).factorial)) := by
  have H := (reciprocal_coefficient_limit e j).mul_const (y^j)
  have heq : (e.val.factorial:ℝ)*(y/2)^j/(3*j+e.val).factorial =
      (e.val.factorial:ℝ)/(2^j*(e.val+3*j).factorial)*y^j := by
    rw [Nat.add_comm (3*j) e.val,div_pow]; ring
  rw [heq]
  apply H.congr'
  filter_upwards [eventually_ge_atTop j] with p hp
  have hd : j≤deg p e := by dsimp [deg]; omega
  simp only [scaledTerm,Polynomial.coeff_reverse,row_degree,Polynomial.revAt_le hd]
  rfl

private theorem scalar_majorant {C L P N E A Y c : ℝ} {e j : ℕ}
    (cpos : 0<c) (hp : 0<P) (hN : 0<N) (hA : 1≤A) (hY : 0≤Y) (hE : 0≤E) (hC : 0≤C)
    (top : c*P*N^e≤L)
    (env : C*A^(e+3*j) ≤ (9*4^j)*P*(4:ℝ)^(e+j)*N^(e+3*j)*E) :
    C/(L*N^(3*j))*Y^j≤(9*4^e*E/c)*(16*Y/A^3)^j := by
  have hApos : 0<A := by linarith
  have hL : 0<L := lt_of_lt_of_le (by positivity) top
  have eA : A^(e+3*j)=A^e*(A^3)^j := by rw [pow_add,pow_mul]
  have eN : N^(e+3*j)=N^e*N^(3*j) := pow_add _ _ _
  have e4 : (4:ℝ)^(e+j)=4^e*4^j := pow_add _ _ _
  have e16 : (16:ℝ)^j=4^j*4^j := by rw [←mul_pow]; norm_num
  have hAe : 1≤A^e := one_le_pow₀ hA
  have pp : C*(A^3)^j≤C*A^(e+3*j) := by
    rw [eA]; nlinarith only [mul_nonneg (mul_nonneg hC (pow_nonneg (by positivity : 0≤A^3) j)) (sub_nonneg.mpr hAe)]
  have ep := pp.trans env
  rw [eN,e4] at ep
  have eq' : C*(A^3)^j*c≤9*4^e*E*(4^j*4^j)*(L*N^(3*j)) := by
    calc
      _ ≤ ((9*4^j)*P*(4^e*4^j)*(N^e*N^(3*j))*E)*c := mul_le_mul_of_nonneg_right ep cpos.le
      _ = (9*4^e*E*(4^j*4^j)*N^(3*j))*(c*P*N^e) := by ring
      _ ≤ (9*4^e*E*(4^j*4^j)*N^(3*j))*L := by gcongr
      _ = _ := by ring
  have hlast := mul_le_mul_of_nonneg_right eq' (pow_nonneg hY j)
  rw [div_pow,mul_pow,e16]
  apply (le_of_mul_le_mul_right (a:=c*(A^3)^j*(L*N^(3*j))) ?_ (by positivity))
  convert hlast using 1 <;> field_simp <;> ring

private theorem reversed_majorant (e : Fin 3) (y : ℝ) :
    ∃ K : ℝ, ∀ᶠ p : ℕ in atTop, ∀ j, ‖scaledTerm p e j y‖≤K*(1/2:ℝ)^j := by
  let c := (2:ℝ)^e.val/e.val.factorial/2
  have hc : 0<c := by dsimp [c]; positivity
  have htop := (top_rank_limit e).eventually_const_lt (show c < (2:ℝ)^e.val/e.val.factorial by
    have : 0<(2:ℝ)^e.val/e.val.factorial := by positivity
    dsimp [c]; linarith)
  let A := 32*(|y|+1)
  have hA : 1≤A := by dsimp [A]; linarith [abs_nonneg y]
  have Apos : 0<A := by linarith
  let E := Real.exp A^2*Real.exp (A^2)
  have hE : 0≤E := by dsimp [E]; positivity
  let K := 9*4^e.val*E/c
  refine ⟨K,?_⟩
  filter_upwards [htop] with p hp
  intro j
  let N := rank p e
  let d := deg p e
  have Npos : 0<(N:ℝ) := by dsimp [N,rank]; positivity
  have Ppos : 0<(catalan p:ℝ) := by exact_mod_cast catalan_positive p
  have top' : c*(catalan p:ℝ)*(N:ℝ)^e.val ≤ (B N).coeff d := by
    have ht := (lt_div_iff₀ (show 0<(catalan p:ℝ)*(N:ℝ)^e.val by positivity)).mp hp
    linarith only [ht,show c*((catalan p:ℝ)*(N:ℝ)^e.val)=c*(catalan p:ℝ)*(N:ℝ)^e.val by ring]
  by_cases hj : j≤d
  · let n := 3*p+2*e.val
    let δ := e.val+3*j
    have hN : N=n+1 := rfl
    have he : 2*n=3*(d-j)+δ := by dsimp [n,d,deg,δ] at *; omega
    have hm : n-(d-j)≤p+(e.val+j) := by dsimp [n,d,deg] at *; omega
    have henv := coefficient_envelope (n:=n) (k:=d-j) (p:=p) (q:=e.val+j) he hm Apos
    have hcount : ((δ+1:ℕ):ℝ)^2 ≤ 9*4^j := by
      have h₁ : δ+1≤3*2^j := by
        have := e.isLt
        have H : j < 2^j := Nat.lt_two_pow_self
        dsimp [δ]; omega
      have h₂ : ((δ+1:ℕ):ℝ)≤3*(2:ℝ)^j := by exact_mod_cast h₁
      calc
        _ ≤ (3*(2:ℝ)^j)^2 := pow_le_pow_left₀ (by positivity) h₂ 2
        _ = _ := by rw [mul_pow,←pow_mul,mul_comm j 2,pow_mul]; norm_num
    have env : (B N).coeff (d-j)*A^(e.val+3*j)≤
        (9*4^j)*(catalan p:ℝ)*(4:ℝ)^(e.val+j)*(N:ℝ)^(e.val+3*j)*E := by
      apply henv.trans
      dsimp only [E]
      simp only [hN,Nat.cast_add,Nat.cast_one] at hcount ⊢
      rw [show (9*4^j)*(catalan p:ℝ)*4^(e.val+j)*((n:ℝ)+1)^(e.val+3*j)*
        (Real.exp A^2*Real.exp (A^2)) =
        (9*4^j)*(catalan p:ℝ)*4^(e.val+j)*((n:ℝ)+1)^(e.val+3*j)*Real.exp A^2*Real.exp (A^2) by ring]
      gcongr
    have sm := scalar_majorant hc Ppos Npos hA (abs_nonneg y) hE (B_coeff_nonneg N (d-j)) top' env
    have Hbase : 16*|y|/A^3≤1/2 := by
      have h₃ : A≤A^3 := by simpa using (pow_le_pow_right₀ hA (by decide : 1≤3))
      apply (div_le_iff₀ (pow_pos Apos 3)).mpr
      dsimp [A] at h₃ ⊢; linarith
    have hp₀ : 0≤(B N).coeff d := B_coeff_nonneg N d
    have hc₀ : 0≤(B N).coeff (d-j) := B_coeff_nonneg N (d-j)
    rw [scaledTerm,Polynomial.coeff_reverse,row_degree,Polynomial.revAt_le hj,Real.norm_eq_abs,abs_mul,abs_pow]
    change |(B N).coeff (d-j)/((B N).coeff d*(N:ℝ)^(3*j))| * |y|^j≤_
    rw [abs_of_nonneg (div_nonneg hc₀ (by positivity))]
    exact sm.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) Hbase j) (by positivity))
  · have H := (B N).reverse_natDegree_le.trans_lt (show (B N).natDegree<j by rw [row_degree]; exact Nat.lt_of_not_ge hj)
    rw [scaledTerm,Polynomial.coeff_eq_zero_of_natDegree_lt H,zero_div,zero_mul,norm_zero]
    dsimp [K]; positivity

/-- The pointwise reciprocal limit for the actual polynomial reverse. At y=0
this convention also gives the normalized leading coefficient exactly. -/
theorem far_endpoint_limit (e : Fin 3) (y : ℝ) : Tendsto
    (fun p : ℕ => let n:=3*p+2*e.val+1; let d:=2*p+e.val
      (B n).reverse.eval (y/(n:ℝ)^3)/(B n).coeff d)
    atTop (𝓝 (BigDescents132.Far.farLimit e.val y)) := by
  obtain ⟨K,hK⟩ := reversed_majorant e y
  have H := tendsto_tsum_of_dominated_convergence
    ((summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).mul_left K)
    (fun j => term_limit e j y) hK
  apply H.congr'
  filter_upwards with p
  let n:=rank p e
  let d:=deg p e
  let f:=(B n).reverse
  change (∑' j : ℕ, f.coeff j/((B n).coeff d*(n:ℝ)^(3*j))*y^j) = f.eval (y/(n:ℝ)^3)/(B n).coeff d
  rw [tsum_eq_sum (s:=f.support) (fun j hj => by simp [Polynomial.not_mem_support_iff.mp hj])]
  rw [Polynomial.eval_eq_sum,Polynomial.sum,div_eq_mul_inv,Finset.sum_mul]
  apply sum_congr rfl
  intro j _
  rw [div_pow,←pow_mul]
  ring

end BigDescents132.Series
