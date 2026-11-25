import BigDescents132.FarCoefficients
import BigDescents132.Degree
import BigDescents132.RegularBranch
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery

namespace BigDescents132.Series
open Polynomial Finset Filter Set Complex
open scoped Topology

/-- This specialization recovers the Catalan count of the avoiders. -/
theorem at_one_catalan (n : ℕ) : (B n).eval 1=catalan n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      cases n with
      | zero => simp
      | succ k =>
        rw [B_eq_A_add_C (k+1),A_recurrence,C_recurrence]
        simp only [eval_add,eval_mul,eval_X,one_mul,eval_finset_sum]
        rw [←eval_add,←B_eq_A_add_C k,ih (k+1) (by omega),catalan_succ' (k+1),Nat.cast_sum]
        rw [Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => ((catalan i*catalan j:ℕ):ℝ))]
        conv_rhs => rw [sum_range_succ',sum_range_succ]
        simp only [Nat.sub_zero,Nat.add_sub_add_right,Nat.sub_self,catalan_zero,Nat.cast_mul,Nat.cast_one,mul_one,one_mul]
        have hsum : ∑ i∈range k, (B (i+1)).eval 1 * (B (k-i)).eval 1 =
            ∑ i∈range k, (catalan (i+1):ℝ)*(catalan (k-i):ℝ) := by
          apply sum_congr rfl
          intro i hi
          have := mem_range.mp hi
          rw [ih (i+1) (by omega),ih (k-i) (by omega)]
        rw [hsum]
        ring

private noncomputable def boundBase (t : ℝ) := 4*max 1 |t|

private theorem boundBase_pos (t : ℝ) : 0<boundBase t := by
  unfold boundBase
  positivity

theorem row_geometric_bound (n : ℕ) (t : ℝ) : |(B n).eval t|≤(boundBase t)^n := by
  let M := max 1 |t|
  have hm : 1≤M := le_max_left _ _
  have hp (k) (hk : k∈(B n).support) : k≤n := by
    have h := le_natDegree_of_ne_zero (mem_support_iff.mp hk)
    rw [degree_all,expectedDegree] at h
    omega
  have h₁ := at_one_catalan n
  rw [eval_eq_sum, Polynomial.sum] at h₁
  simp only [one_pow,mul_one] at h₁
  rw [eval_eq_sum,Polynomial.sum,←Real.norm_eq_abs]
  calc
    _ ≤ ∑ k∈(B n).support, ‖(B n).coeff k*t^k‖ := norm_sum_le _ _
    _ ≤ ∑ k∈(B n).support, (B n).coeff k*M^n := by
      apply sum_le_sum
      intro k hk
      rw [Real.norm_eq_abs,abs_mul,abs_pow,abs_of_nonneg (B_coeff_nonneg _ _)]
      apply mul_le_mul_of_nonneg_left _ (B_coeff_nonneg _ _)
      exact (pow_le_pow_left₀ (abs_nonneg t) (le_max_right 1 _) _).trans (pow_le_pow_right₀ hm (hp k hk))
    _ ≤ _ := by
      rw [←Finset.sum_mul, h₁,boundBase,mul_pow]
      gcongr
      simpa using catalan_uniform_le 0 n n (by omega)

noncomputable def seriesValue (t : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (Complex.ofReal ((B (n+1)).eval t))*z^n

private theorem norm_term (t : ℝ) (z : ℂ) (n : ℕ) :
    ‖(Complex.ofReal ((B (n+1)).eval t))*z^n‖ ≤ boundBase t*(boundBase t*‖z‖)^n := by
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,mul_pow]
  calc
    _ ≤ boundBase t^(n+1)*‖z‖^n := by gcongr; exact row_geometric_bound _ _
    _ = _ := by rw [pow_succ]; ring

private theorem row_summable {t : ℝ} {z : ℂ} (h : boundBase t*‖z‖<1) :
    Summable (fun n:ℕ => ‖(Complex.ofReal ((B (n+1)).eval t))*z^n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_term _ _)
    ((summable_geometric_of_lt_one (mul_nonneg (boundBase_pos _).le (norm_nonneg _)) h).mul_left _)

private theorem seriesValue_zero (t : ℝ) : seriesValue t 0=1 := by
  unfold seriesValue
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

private theorem seriesValue_continuousAt (t : ℝ) : ContinuousAt (seriesValue t) 0 := by
  have hK := boundBase_pos t
  have hv : ∀ᶠ z : ℂ in 𝓝 0, boundBase t*‖z‖≤1/2 :=
    ((show ContinuousAt (fun z : ℂ => boundBase t*‖z‖) 0 by fun_prop).tendsto.eventually_lt_const
      (by norm_num : boundBase t*‖(0:ℂ)‖ < 1/2)).mono fun _ h => h.le
  have H := tendsto_tsum_of_dominated_convergence
    ((summable_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)).mul_left (boundBase t))
    (fun n:ℕ => (show ContinuousAt (fun z : ℂ => (Complex.ofReal ((B (n+1)).eval t))*z^n) 0 by fun_prop).tendsto)
    (hv.mono fun z hz n => (norm_term t z n).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hK.le (norm_nonneg _)) hz _) hK.le))
  exact H

private noncomputable def term (z : ℂ) (f : PowerSeries ℂ) (n : ℕ) : ℂ :=
  PowerSeries.coeff ℂ n f*z^n

private def Represents (z : ℂ) (f : PowerSeries ℂ) (a : ℂ) : Prop :=
  Summable (fun n : ℕ => ‖term z f n‖) ∧ HasSum (term z f) a

private theorem finite_rep {g : ℕ → ℂ} {i : ℕ} (hn : ∀ n, n≠i → g n=0) :
    Summable (fun n : ℕ => ‖g n‖) ∧ HasSum g (g i) := by
  refine ⟨summable_of_ne_finset_zero (s:={i}) (fun n h => ?_),hasSum_single i hn⟩
  rw [hn n (by simpa using h),norm_zero]

private theorem rep_c (z v : ℂ) : Represents z (PowerSeries.C ℂ v) v := by
  have h := finite_rep (g:=term z (PowerSeries.C ℂ v)) (i:=0) (fun n hn => by
    simp [term,PowerSeries.coeff_C,hn])
  simpa only [term,PowerSeries.coeff_zero_C,pow_zero,mul_one] using h
private theorem rep_one (z : ℂ) : Represents z 1 1 := by simpa using rep_c z 1
private theorem rep_X (z : ℂ) : Represents z PowerSeries.X z := by
  have h := finite_rep (g:=term z PowerSeries.X) (i:=1) (fun n hn => by
    simp [term,PowerSeries.coeff_X,hn])
  simpa [term,PowerSeries.coeff_X,Represents] using h

private theorem rep_add {z a b : ℂ} {f g : PowerSeries ℂ} (hf : Represents z f a) (hg : Represents z g b) :
    Represents z (f+g) (a+b) := by
  have e (i:ℕ) : term z (f+g) i=term z f i+term z g i := by simp [term,add_mul]
  rw [Represents,funext e]
  refine ⟨?_,hf.2.add hg.2⟩
  exact (hf.1.add hg.1).of_nonneg_of_le (fun i => norm_nonneg _) (fun i => norm_add_le (term z f i) (term z g i))

private theorem rep_neg {z a : ℂ} {f : PowerSeries ℂ} (hf : Represents z f a) : Represents z (-f) (-a) := by
  have e (i:ℕ) : term z (-f) i= - term z f i := by simp [term]
  rw [Represents,funext e]
  simp only [norm_neg]
  exact ⟨hf.1,hf.2.neg⟩

private theorem rep_sub {z a b : ℂ} {f g : PowerSeries ℂ} (hf : Represents z f a) (hg : Represents z g b) :
    Represents z (f-g) (a-b) := by simpa [sub_eq_add_neg] using rep_add hf (rep_neg hg)

private theorem rep_mul {z a b : ℂ} {f g : PowerSeries ℂ} (hf : Represents z f a) (hg : Represents z g b) :
    Represents z (f*g) (a*b) := by
  have e (i:ℕ) : term z (f*g) i=∑ ij∈antidiagonal i, term z f ij.1*term z g ij.2 := by
    simp only [term,PowerSeries.coeff_mul,Finset.sum_mul]
    apply sum_congr rfl
    intro ij hj
    rw [←Finset.mem_antidiagonal.mp hj,pow_add]
    ring
  rw [Represents,funext e]
  have hn := summable_norm_sum_mul_antidiagonal_of_summable_norm hf.1 hg.1
  refine ⟨hn,?_⟩
  rw [←hf.2.tsum_eq,←hg.2.tsum_eq,tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf.1 hg.1]
  exact hn.of_norm.hasSum

private theorem rep_pow {z a : ℂ} {f : PowerSeries ℂ} (hf : Represents z f a) (k : ℕ) :
    Represents z (f^k) (a^k) := by
  induction k with
  | zero => simpa using rep_one z
  | succ k ih => simpa only [pow_succ] using rep_mul ih hf

/-- The absolutely convergent series of literal rows satisfies the quadratic
equation on an explicit disk. -/
theorem local_quadratic (t : ℝ) (z : ℂ) (h : 4*max 1 |t| * ‖z‖<1) :
    ((1-z)^2-(t:ℂ)*z^2)*seriesValue t z =
      1+(t:ℂ)*z^2*(1-z+(t:ℂ)*z)*(seriesValue t z)^2 := by
  let ϕ := Complex.ofRealHom.comp (Polynomial.evalRingHom t)
  let f := PowerSeries.map ϕ total
  have hr : Represents z f (seriesValue t z) := by
    change Summable _ ∧ HasSum _ _
    have he (n : ℕ) : term z f n = (Complex.ofReal ((B (n+1)).eval t))*z^n := by
      simp [term,f,ϕ,total]
    rw [funext he]
    exact ⟨row_summable h,(row_summable h).of_norm.hasSum⟩
  have eq := congrArg (PowerSeries.map ϕ) quadratic
  simp only [map_mul,map_pow,map_add,map_sub,map_one,PowerSeries.map_X,PowerSeries.map_C] at eq
  have par : ϕ Polynomial.X=(t:ℂ) := by simp [ϕ]
  rw [par] at eq
  have X := rep_X z
  have T := rep_c z (t:ℂ)
  have O := rep_one z
  have L := rep_mul (rep_sub (rep_pow (rep_sub O X) 2) (rep_mul T (rep_pow X 2))) hr
  have R := rep_add O (rep_mul (rep_mul (rep_mul T (rep_pow X 2)) (rep_add (rep_sub O X) (rep_mul T X))) (rep_pow hr 2))
  rw [show f=PowerSeries.map ϕ total from rfl] at L R
  rw [eq] at L
  exact L.2.unique R.2

/-- As a complex analytic germ at the origin the series of the literal
permutation rows agrees with the rationalized square-root branch. -/
theorem series_eq_regular_near_zero (t : ℝ) :
    ∀ᶠ z : ℂ in 𝓝 0, seriesValue t z=Branch.regularBranch (1-(t:ℂ)) z := by
  let s : ℂ := 1-(t:ℂ)
  let W := fun z : ℂ => Branch.linearFactor s z-2*Branch.quadraticFactor s z*seriesValue t z
  have cont : ContinuousAt W 0 := by
    dsimp [W,Branch.linearFactor,Branch.quadraticFactor]
    exact (show ContinuousAt (fun z : ℂ => 1-2*z+s*z^2) 0 by fun_prop).sub
      ((show ContinuousAt (fun z : ℂ => 2*((1-s)*z^2*(1-s*z))) 0 by fun_prop).mul (seriesValue_continuousAt t))
  have w0 : W 0=1 := by simp [W,Branch.linearFactor,Branch.quadraticFactor]
  have realpos := (Complex.continuous_re.continuousAt.comp cont).tendsto.eventually_const_lt
    (show 0<(W 0).re by rw [w0]; norm_num)
  have disk := (show ContinuousAt (fun z : ℂ => 4*max 1 |t| * ‖z‖) 0 by fun_prop).tendsto.eventually_lt_const
    (show 4*max 1 |t| * ‖(0:ℂ)‖<1 by norm_num)
  filter_upwards [realpos,disk] with z hw hd
  have h := local_quadratic t z hd
  have hD : Branch.linearFactor s z=(1-z)^2-(t:ℂ)*z^2 := by dsimp [Branch.linearFactor,s]; ring
  have hN : Branch.quadraticFactor s z=(t:ℂ)*z^2*(1-z+(t:ℂ)*z) := by dsimp [Branch.quadraticFactor,s]; ring
  rw [←hD,←hN] at h
  have eq : (radicand s).eval z=(W z)^2 := by
    rw [Branch.square_identity]; dsimp [W]
    linear_combination 4*Branch.quadraticFactor s z*h
  have he : (Branch.linearFactor s z+W z)*seriesValue t z=2 := by
    dsimp [W]; linear_combination 2*h
  have hn : Branch.linearFactor s z+W z≠0 := by intro hc; rw [hc,zero_mul] at he; norm_num at he
  change seriesValue t z=Branch.regularBranch s z
  rw [Branch.regularBranch,eq,Complex.sq_cpow_two_inv hw]
  exact (eq_div_iff hn).mpr (mul_comm _ _ |>.trans he)



open scoped NNReal ENNReal

/-- Any analytic representative of the literal row generating germ computes its
coefficients on every sufficiently small positive-radius circle. -/
theorem cauchy_coefficient_of_germ (t : ℝ) {f : ℂ → ℂ}
    (h : seriesValue t =ᶠ[𝓝 0] f) :
    ∃ ε : ℝ, 0<ε ∧ ∀ r∈Set.Ioo 0 ε, ∀ n : ℕ, Complex.ofReal ((B (n+1)).eval t) =
      (2*Real.pi*I:ℂ)⁻¹ * ∮ z in C((0:ℂ),r), z⁻¹^(n+1)*f z := by
  let a := fun n : ℕ => Complex.ofReal ((B (n+1)).eval t)
  let p := FormalMultilinearSeries.ofScalars ℂ a
  let s : ℝ≥0 := ⟨(boundBase t)⁻¹,(inv_pos.mpr (boundBase_pos t)).le⟩
  have sp : 0<s := show (0:ℝ)<(boundBase t)⁻¹ from inv_pos.mpr (boundBase_pos t)
  have leR : (s:ℝ≥0∞)≤p.radius := by
    apply p.le_radius_of_bound (boundBase t)
    intro n
    simp only [p,FormalMultilinearSeries.ofScalars_norm,a,Complex.norm_real,Real.norm_eq_abs]
    calc
      _ ≤ boundBase t^(n+1)*(s:ℝ)^n := mul_le_mul_of_nonneg_right (row_geometric_bound _ _) (by positivity)
      _ = _ := by
        change boundBase t^(n+1)*(boundBase t)⁻¹^n = _
        rw [pow_succ',mul_assoc,←mul_pow,mul_inv_cancel₀ (boundBase_pos t).ne',one_pow,mul_one]
  have pR : 0<p.radius := (show (0:ℝ≥0∞)<s by exact_mod_cast sp).trans_le leR
  have eqsum : p.sum=seriesValue t := by
    funext z
    exact FormalMultilinearSeries.ofScalars_sum_eq a z
  have hp := (p.hasFPowerSeriesOnBall pR).hasFPowerSeriesAt
  rw [eqsum] at hp
  have hf := hp.congr h
  obtain ⟨R,Rpos,hR⟩ := Metric.mem_nhds_iff.mp hf.analyticAt.eventually_analyticAt
  refine ⟨R,Rpos,fun rad hrad n => ?_⟩
  let r : ℝ≥0 := ⟨rad,hrad.1.le⟩
  have rpos : 0<r := hrad.1
  have hd : DifferentiableOn ℂ f (Metric.closedBall 0 (r:ℝ)) := by
    intro z hz
    exact (hR (Metric.closedBall_subset_ball hrad.2 hz)).differentiableAt.differentiableWithinAt
  have eqp := hf.eq_formalMultilinearSeries (hd.hasFPowerSeriesOnBall rpos).hasFPowerSeriesAt
  have e := congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ => q n (fun _ => (1:ℂ))) eqp
  change (FormalMultilinearSeries.ofScalars ℂ a n (fun _ => (1:ℂ))) =
    cauchyPowerSeries f 0 r n (fun _ => (1:ℂ)) at e
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq,one_pow,smul_eq_mul,mul_one,
    cauchyPowerSeries_apply,sub_zero,one_div,pow_succ, mul_assoc] using e


/-- The coefficient integral on a single positive-radius circle at the origin.
Its integrand is the rationalized algebraic germ, and its coefficient is the
literal big-descent polynomial. -/
theorem cauchy_coefficient (t : ℝ) : ∃ r : ℝ, 0<r ∧ ∀ n : ℕ,
    Complex.ofReal ((B (n+1)).eval t) =
      (2*Real.pi*I:ℂ)⁻¹ * ∮ z in C((0:ℂ),r),
        z⁻¹^(n+1)*Branch.regularBranch (1-(t:ℂ)) z := by
  obtain ⟨ε,hε,h⟩ := cauchy_coefficient_of_germ t (series_eq_regular_near_zero t)
  exact ⟨ε/2,by positivity,h _ ⟨by positivity,by linarith⟩⟩

end BigDescents132.Series
