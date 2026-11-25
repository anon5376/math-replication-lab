import BigDescents132.Generating
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

namespace BigDescents132.Series
open Finset Polynomial
open scoped PowerSeries Polynomial
local notation "x" => (PowerSeries.X : S)
local notation "t" => (PowerSeries.C R Polynomial.X : S)
noncomputable local instance (priority := high) : Algebra R S :=
  @MvPowerSeries.instAlgebra Unit R R _ _ (Algebra.id R)
local notation "cc" => PowerSeries.constantCoeff R
local notation "cf" => PowerSeries.coeff R

private theorem sub_ok (q : S) (h : cc q=0) : MvPowerSeries.HasSubst (fun _ : Unit => q) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => h

private noncomputable def plug (q : S) (h : cc q=0) : S →+* S :=
  (MvPowerSeries.substAlgHom (R:=R) (sub_ok q h)).toRingHom

private theorem plug_x (q : S) (h : cc q=0) : plug q h x=q := by
  exact MvPowerSeries.substAlgHom_X (R:=R) (sub_ok q h) ()

private theorem plug_c (q : S) (h : cc q=0) (r : R) :
    plug q h (PowerSeries.C R r) = PowerSeries.C R r := by
  exact (MvPowerSeries.substAlgHom (R:=R) (sub_ok q h)).commutes r

private theorem plug_cut (q : S) (h : cc q=0) (n : ℕ) (f : S) :
    x^n ∣ plug q h f - ∑ i∈range n, PowerSeries.C R (cf i f)*q^i := by
  have dv : x^n ∣ f-(PowerSeries.trunc n f : S) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [map_sub,PowerSeries.coeff_coe_trunc_of_lt hm,sub_self]
  obtain ⟨p,hp⟩ := dv
  have hpoly : plug q h (PowerSeries.trunc n f : S) = ∑ i∈range n, PowerSeries.C R (cf i f)*q^i := by
    clear hp p
    induction n with
    | zero => simp [PowerSeries.trunc]
    | succ n ih =>
      rw [PowerSeries.trunc_succ,Polynomial.coe_add,map_add,ih,sum_range_succ,
        ← Polynomial.C_mul_X_pow_eq_monomial,Polynomial.coe_mul,Polynomial.coe_C,
        Polynomial.coe_pow,Polynomial.coe_X,map_mul,map_pow,plug_c,plug_x]
  obtain ⟨u,hu⟩ := PowerSeries.X_dvd_iff.mpr h
  refine ⟨u^n*plug q h p,?_⟩
  have hp' := congrArg (plug q h) hp
  rw [map_sub,map_mul,map_pow,plug_x,hpoly] at hp'
  calc
    _ = q^n*plug q h p := hp'
    _ = _ := by rw [show q^n=x^n*u^n by rw [hu,mul_pow],mul_assoc]

private theorem plug_coeff (q : S) (h : cc q=0) (n : ℕ) (f g : S) :
    cf n (g*plug q h f) =
    ∑ i∈range (n+1), cf n (PowerSeries.C R (cf i f) * g * q^i) := by
  obtain ⟨u,hu⟩ := plug_cut q h (n+1) f
  have hu' : x^(n+1) ∣ g*plug q h f - g*(∑ i∈range (n+1), PowerSeries.C R (cf i f)*q^i) :=
    ⟨g*u, by linear_combination g*hu⟩
  have H := PowerSeries.X_pow_dvd_iff.mp hu' n (by omega)
  rw [map_sub,sub_eq_zero,Finset.mul_sum,map_sum] at H
  rw [H]
  apply sum_congr rfl
  intro i _
  congr 1
  ring

private noncomputable def Gm : S := PowerSeries.mk 1
private noncomputable def P : S := x*(1+t*x*Gm)
private theorem pc : cc P=0 := by simp [P]
private noncomputable def J : S := plug P pc Gm
private noncomputable def M : S := t*x*P*Gm*J^2
private theorem mc : cc M=0 := by simp [M]
private noncomputable def catSeries : S := PowerSeries.mk fun m => (catalan m:R)

private theorem cat_eq : catSeries=1+x*(catSeries*catSeries) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [catSeries]
  | succ n =>
    rw [map_add,PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_mul]
    simp [catSeries,catalan_succ']

private theorem geom_unit : Gm*(1-x)=1 := PowerSeries.mk_one_mul_one_sub_eq_one R
private theorem j_unit : J*(1-P)=1 := by
  have h := congrArg (plug P pc) geom_unit
  simpa only [map_mul,map_sub,map_one,plug_x,J] using h

/-- Catalan generating function for the literal polynomial rows, with
nonnegative auxiliary series P=x(1+t x/(1-x)) and J=1/(1-P). -/
private theorem total_catalan : total=Gm*J*plug M mc catSeries := by
  let H := plug M mc catSeries
  have he : H=1+M*(H*H) := by
    have e := congrArg (plug M mc) cat_eq
    simpa only [map_add,map_one,map_mul,plug_x] using e
  let cand := Gm*J*H
  have eP : (1-x)*P=x*(1-x+t*x) := by
    unfold P
    linear_combination t*x^2*geom_unit
  have eJ : (1-x)*(1-P) = (1-x)^2-t*x^2 := by linear_combination -eP
  have eG : ((1-x)^2-t*x^2)*(Gm*J)=1 := by rw [←eJ,show (1-x)*(1-P)*(Gm*J)=(Gm*(1-x))*(J*(1-P)) by ring,geom_unit,j_unit,one_mul]
  have eM : M=t*x^2*(1-x+t*x)*(Gm*J)^2 := by
    unfold M
    have h : P = x*(1-x+t*x)*Gm := by
      calc P = (Gm*(1-x))*P := by rw [geom_unit, one_mul]
           _ = Gm*((1-x)*P) := by ring
           _ = _ := by rw [eP]; ring
    rw [h]; ring
  have cand_eq : ((1-x)^2-t*x^2)*cand = 1+t*x^2*(1-x+t*x)*cand^2 := by
    dsimp [cand]
    rw [← mul_assoc,eG,one_mul]
    linear_combination he + (H^2)*eM
  have product : (((1-x)^2-t*x^2)-t*x^2*(1-x+t*x)*(total+cand))*(total-cand) = 0 := by
    linear_combination quadratic - cand_eq
  have nonzero : (((1-x)^2-t*x^2)-t*x^2*(1-x+t*x)*(total+cand))≠0 := by
    intro h
    have H := congrArg (PowerSeries.constantCoeff R) h
    simp at H
  exact sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_left nonzero)

private noncomputable def outerWeight (m : ℕ) : S :=
  (catalan m:S)*t^m*x^m*P^m*Gm^(m+1)

private theorem first_expansion (n : ℕ) : B (n+1) =
    ∑ m∈range (n+1), cf n (outerWeight m * J^(2*m+1)) := by
  rw [show B (n+1)=cf n total by simp [total],total_catalan,plug_coeff]
  apply sum_congr rfl
  intro m _
  apply congrArg
  simp only [catSeries,PowerSeries.coeff_mk,map_natCast,outerWeight,M,mul_pow,pow_add,pow_one,pow_mul]
  ring

private theorem second_expansion (n m : ℕ) : cf n (outerWeight m*J^(2*m+1)) =
    ∑ h∈range (n+1), cf n (((catalan m * (2*m+h).choose (2*m) : ℕ):S) *
      t^m*x^(2*m+h)*Gm^(m+1)*(1+t*x*Gm)^(m+h)) := by
  change cf n (outerWeight m*(plug P pc Gm)^(2*m+1))=_
  rw [←map_pow,plug_coeff]
  apply sum_congr rfl
  intro h _
  apply congrArg
  rw [show Gm^(2*m+1)=PowerSeries.mk (fun j => ((2*m+j).choose (2*m):R)) from
    PowerSeries.mk_one_pow_eq_mk_choose_add R (2*m)]
  simp only [PowerSeries.coeff_mk,map_natCast,Nat.cast_mul,outerWeight,P,mul_pow,pow_add,pow_mul]
  ring

private theorem expand_power (n m h : ℕ) (K : ℕ) :
    cf n ((K:S)*t^m*x^(2*m+h)*Gm^(m+1)*(1+t*x*Gm)^(m+h)) =
      ∑ b∈range (m+h+1), cf n (((K*(m+h).choose b:ℕ):S)*
        t^(m+b)*x^(2*m+h+b)*Gm^(m+b+1)) := by
  rw [add_comm (1:S),add_pow,Finset.mul_sum,map_sum]
  apply sum_congr rfl
  intro b _
  apply congrArg
  simp only [Nat.cast_mul,one_pow,mul_one,mul_pow,pow_add,pow_one,pow_mul]
  ring

private theorem extract_term (n d k K i : ℕ) :
    (cf n ((K:S)*t^k*x^d*Gm^(k+1))).coeff i =
      if d≤n ∧ k=i then (K:ℝ)*(k+(n-d)).choose k else 0 := by
  rw [show (K:S)*t^k*x^d*Gm^(k+1) =
    x^d*(PowerSeries.C R ((K:R)*(Polynomial.X:R)^k)*Gm^(k+1)) by simp; ring]
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs with hd hk
  · obtain ⟨_,rfl⟩ := hk
    rw [PowerSeries.coeff_C_mul, Gm, PowerSeries.mk_one_pow_eq_mk_choose_add,PowerSeries.coeff_mk]
    rw [show (K:R)*Polynomial.X^k*((k+(n-d)).choose k:R) =
       Polynomial.C ((K:ℝ)*((k+(n-d)).choose k:ℝ))*Polynomial.X^k by simp; ring]
    rw [Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,if_pos rfl,mul_one]
  · rw [PowerSeries.coeff_C_mul, Gm, PowerSeries.mk_one_pow_eq_mk_choose_add,PowerSeries.coeff_mk]
    have hki : k≠i := by tauto
    rw [show (K:R)*Polynomial.X^k*((k+(n-d)).choose k:R) =
       Polynomial.C ((K:ℝ)*((k+(n-d)).choose k:ℝ))*Polynomial.X^k by simp; ring]
    simp only [Polynomial.coeff_C_mul,Polynomial.coeff_X_pow,if_neg hki.symm,mul_zero]
  · tauto
  · simp

/-- A positive finite coefficient formula. Here n is one less than the rank,
b chooses the marked factors, and n-(2m+h+b) is the last nonnegative index. -/
theorem positive_coefficient_formula (n k : ℕ) :
    (B (n+1)).coeff k =
      ∑ m∈range (n+1), ∑ h∈range (n+1), ∑ b∈range (m+h+1),
        if 2*m+h+b≤n ∧ m+b=k then
          (catalan m:ℝ)*((2*m+h).choose (2*m):ℝ)*((m+h).choose b:ℝ)*
            ((m+b+(n-(2*m+h+b))).choose (m+b):ℝ) else 0 := by
  rw [first_expansion,Polynomial.finset_sum_coeff]
  apply sum_congr rfl
  intro m _
  rw [second_expansion,Polynomial.finset_sum_coeff]
  apply sum_congr rfl
  intro h _
  rw [expand_power,Polynomial.finset_sum_coeff]
  apply sum_congr rfl
  intro b _
  rw [extract_term]
  simp

end BigDescents132.Series
