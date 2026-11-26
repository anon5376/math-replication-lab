import BigDescents132.EndpointBinomial
import BigDescents132.Degree
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecificLimits.Basic

namespace BigDescents132.AllRanks
open Finset

private theorem centered_descending (N m r : ℕ) (hr : 2*m+1≤r) :
    (N+m).descFactorial r≤N^r := by
  induction m generalizing r with
  | zero => simpa using Nat.descFactorial_le_pow N r
  | succ m ih =>
    obtain ⟨t,rt⟩ : ∃ t, r=t+2 := ⟨r-2,by omega⟩
    subst r
    have ord : 2*m+1≤t := by omega
    have mid := ih t ord
    have ends : (N+m+1)*(N+m-t)≤N^2 := by
      by_cases h : t≤N+m
      · have E : N+m-t+t=N+m := Nat.sub_add_cancel h
        have o : N+m-t+(m+1)≤N := by omega
        have z := Nat.mul_le_mul_left (N+m+1) o
        nlinarith only [z,Nat.mul_le_mul_left (m+1) (show N≤N+m+1 by omega)]
      · simp [Nat.sub_eq_zero_of_le (by omega : N+m≤t)]
    rw [Nat.add_succ,Nat.succ_descFactorial_succ,Nat.descFactorial_succ,pow_succ,pow_succ]
    calc
      _ = ((N+m+1)*(N+m-t))*(N+m).descFactorial t := by ring
      _ ≤ N^2*N^t := Nat.mul_le_mul ends mid
      _ = _ := by ring

private theorem choose_scale (N m r d : ℕ) (hr : 2*m+1≤r) (rd : r≤d) (dn : d≤2*N) :
    d.factorial*(N+m).choose r ≤ N^d*2^(d-r) := by
  let v:=d-r
  have add : r+v=d := by dsimp [v];omega
  have fac : d.factorial≤r.factorial*(2*N)^v := by
    have h:=Nat.factorial_mul_descFactorial (n:=d) (k:=v) (by dsimp [v];omega)
    rw [show d-v=r by dsimp [v];omega] at h
    rw [←h]
    exact Nat.mul_le_mul_left _ ((Nat.descFactorial_le_pow d v).trans (Nat.pow_le_pow_left dn v))
  have cent : r.factorial*(N+m).choose r≤N^r := by
    rw [←Nat.descFactorial_eq_factorial_mul_choose]
    exact centered_descending N m r hr
  calc
    _ ≤ (r.factorial*(2*N)^v)*(N+m).choose r := Nat.mul_le_mul_right _ fac
    _ = (r.factorial*(N+m).choose r)*(2*N)^v := by ring
    _ ≤ N^r*(2*N)^v := Nat.mul_le_mul_right _ cent
    _ = _ := by rw [mul_pow,←add,pow_add];dsimp [v];rw [Nat.add_sub_cancel_left];ring

private theorem choose_two (n k : ℕ) : n.choose k≤2^n := by
  cases n with
  | zero => cases k <;> simp
  | succ n => exact (Nat.choose_succ_le_two_pow n k).trans (Nat.pow_le_pow_right (by decide) (by omega))

private theorem catalan_four (m : ℕ) : catalan m≤4^m := by
  rw [catalan_eq_centralBinom_div]
  apply (Nat.div_le_self _ _).trans
  calc
    _ ≤ 2^(2*m) := choose_two _ _
    _ = _ := by rw [pow_mul];norm_num

private theorem coefficient_term (N k m i j : ℕ) (indices : m+i+j=k) (dn : 3*k+1≤2*N) :
    (3*k+1).factorial*(catalan m*m.choose i*seriesBin (2*m) j*
      (N+m).choose (2*m+j+k+1)) ≤ N^(3*k+1)*(16^m*m.choose i*4^(i+j)) := by
  let d:=3*k+1
  let r:=2*m+j+k+1
  have sc:=choose_scale N m r d (by dsimp [r];omega) (by dsimp [r,d];omega) dn
  have de : d-r=2*i+j := by dsimp [r,d];omega
  rw [de] at sc
  have b := choose_two (2*m+j) (2*m)
  calc
    _ = (d.factorial*(N+m).choose r)*(catalan m*m.choose i*seriesBin (2*m) j) := by dsimp [d,r];ring
    _ ≤ (N^d*2^(2*i+j))*(4^m*m.choose i*2^(2*m+j)) :=
      Nat.mul_le_mul sc (Nat.mul_le_mul (Nat.mul_le_mul_right _ (catalan_four m)) b)
    _ = _ := by
      rw [show (16:ℕ)=2^4 by decide,show (4:ℕ)=2^2 by decide]
      simp only [pow_add,pow_mul,←pow_mul]
      subst k
      dsimp [d]
      ring_nf

private theorem partial_binomial (m b : ℕ) :
    ∑ i∈range (b+1), (m.choose i:ℝ)*(1/5:ℝ)^i≤(6/5:ℝ)^m := by
  let f:=fun i => (m.choose i:ℝ)*(1/5:ℝ)^i
  have full : ∑ i∈range (m+1), f i=(6/5:ℝ)^m := by
    rw [show (6/5:ℝ)=1/5+1 by norm_num,add_pow]
    apply sum_congr rfl;intro i _;simp [f,mul_comm]
  rw [←full]
  change ∑ i∈range (b+1),f i≤_
  by_cases h : b≤m
  · exact sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun i _ _ => by dsimp [f];positivity)
  · apply le_of_eq
    symm
    apply sum_subset (range_mono (by omega))
    intro i _ hi
    have := mt mem_range.mpr hi
    have lt : m < i := by omega
    have zero : m.choose i = 0 := Nat.choose_eq_zero_of_lt lt
    simp [f,zero]

private theorem layer_bound (k m : ℕ) (h : m≤k) :
    (∑ i∈range (k-m+1), (16:ℝ)^m*(m.choose i:ℝ)*4^(k-m)) ≤
      20^k*(24/25:ℝ)^m := by
  let b:=k-m
  have mb : m+b=k := by dsimp [b];omega
  have ds : (4:ℝ)^b=(20:ℝ)^b*(1/5:ℝ)^b := by rw [←mul_pow];norm_num
  calc
    _ ≤ ∑ i∈range (b+1), (16^m*20^b)*((m.choose i:ℝ)*(1/5:ℝ)^i) := by
      apply sum_le_sum;intro i hi
      have ib : i≤b := by have := mem_range.mp hi;omega
      have pp := pow_le_pow_of_le_one (by norm_num : (0:ℝ)≤1/5) (by norm_num : (1/5:ℝ)≤1) ib
      change (16:ℝ)^m*(m.choose i:ℝ)*4^b≤_
      rw [ds]
      nlinarith only [mul_le_mul_of_nonneg_left pp (by positivity : 0≤(16:ℝ)^m*20^b*(m.choose i:ℝ))]
    _ = (16^m*20^b)*(∑ i∈range (b+1), (m.choose i:ℝ)*(1/5:ℝ)^i) := (Finset.mul_sum ..).symm
    _ ≤ (16^m*20^b)*(6/5:ℝ)^m := mul_le_mul_of_nonneg_left (partial_binomial m b) (by positivity)
    _ = _ := by
      rw [←mb,pow_add]
      calc
        _ = (16*(6/5:ℝ))^m*20^b := by rw [mul_pow];ring
        _ = (20*(24/25:ℝ))^m*20^b := by norm_num
        _ = _ := by rw [mul_pow];ring

/-- A uniform factorial envelope for the coefficients of the literal permutation polynomial. -/
theorem endpoint_envelope (N k : ℕ) (hN : 0<N) :
    (B N).coeff k*((3*k+1).factorial:ℝ) ≤ (N:ℝ)^(3*k+1)*(25*20^k) := by
  by_cases h : k≤expectedDegree N
  · obtain ⟨n,hn⟩:=Nat.exists_eq_succ_of_ne_zero hN.ne'
    have dn : 3*k+1≤2*N := by unfold expectedDegree at h;omega
    have eq : (B N).coeff k=(binomialCount N k:ℝ) := hn ▸ coefficient_eq_binomialCount n k
    rw [eq,binomialCount,Nat.cast_sum,Finset.sum_mul]
    calc
      _ ≤ (∑ m∈range (k+1), (N:ℝ)^(3*k+1)*(20^k*(24/25:ℝ)^m)) := by
        apply sum_le_sum;intro m hm
        have mk : m≤k := by have := mem_range.mp hm;omega
        rw [Nat.cast_sum,Finset.sum_mul]
        apply le_trans _ (mul_le_mul_of_nonneg_left (layer_bound k m mk) (by positivity))
        rw [Finset.mul_sum]
        apply sum_le_sum;intro i hi
        have ik : i≤k-m := by have := mem_range.mp hi;omega
        have H:=coefficient_term N k m i (k-m-i) (by omega) dn
        rw [show i+(k-m-i)=k-m by omega,mul_comm (3*k+1).factorial] at H
        exact_mod_cast H
      _ = ((N:ℝ)^(3*k+1)*20^k)*∑ m∈range (k+1),(24/25:ℝ)^m := by
        rw [Finset.mul_sum];apply sum_congr rfl;intro m _;ring
      _ ≤ _ := by
        have g:=geom_sum_mul_neg (24/25:ℝ) (k+1)
        have pos : 0≤(24/25:ℝ)^(k+1) := by positivity
        have bd : (∑ m∈range (k+1),(24/25:ℝ)^m)≤25 := by linarith only [g,pos]
        nlinarith only [mul_le_mul_of_nonneg_left bd (by positivity : 0≤(N:ℝ)^(3*k+1)*20^k)]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [degree_all];omega),zero_mul];positivity

end BigDescents132.AllRanks
