import BigDescents132.CutMoments
import BigDescents132.FarCoefficients
import BigDescents132.FarSigns
import BigDescents132.SmallScaling
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace BigDescents132.Peak
open Real Set MeasureTheory Filter
open scoped Topology

noncomputable def density (v : ℝ) := v^(-1/2:ℝ)*Real.sqrt (1-v^3)
noncomputable def gammaHalf := Real.Gamma (3/2)

theorem gamma_value : gammaHalf=Real.sqrt Real.pi/2 := by
  rw [gammaHalf,show (3/2:ℝ)=1/2+1 by norm_num,Real.Gamma_add_one (by norm_num),Real.Gamma_one_half_eq]; ring

private theorem beta_value (k : ℕ) :
    Real.Gamma ((k:ℝ)+1/2)*gammaHalf/Real.Gamma ((k:ℝ)+2)=
      Real.pi/2*(catalan k:ℝ)/4^k := by
  induction k with
  | zero =>
    norm_num [gamma_value,Real.Gamma_one_half_eq,Real.Gamma_two]
    nlinarith [Real.sq_sqrt Real.pi_pos.le]
  | succ k ih =>
    have hC := (div_eq_div_iff (by exact_mod_cast (Series.catalan_positive k).ne') (by positivity)).mp (Series.catalan_ratio k)
    have cn : (4:ℝ)^k≠0 := by positivity
    have s0 : Real.Gamma ((k:ℝ)+2)≠0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
    have n0 : (k:ℝ)+2≠0 := by positivity
    rw [Nat.cast_succ,show (k:ℝ)+1+1/2=(k+1/2)+1 by ring,
      show (k:ℝ)+1+2=(k+2)+1 by ring,Real.Gamma_add_one (by positivity),Real.Gamma_add_one n0,pow_succ]
    field_simp [cn,s0,n0] at ih ⊢
    linear_combination (4*(2*(k:ℝ)+1))*ih -2*Real.pi*Real.Gamma ((k:ℝ)+2)*hC

private theorem cube_image : (fun x : ℝ => x^3) '' Ioo 0 1=Ioo 0 1 := by
  ext x; constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨pow_pos hy.1 _,pow_lt_one₀ hy.1.le hy.2 (by decide)⟩
  · intro hx
    let y := x^((3:ℝ)⁻¹)
    have h : y^3=x := Real.rpow_inv_natCast_pow hx.1.le (by decide)
    refine ⟨y,⟨Real.rpow_pos_of_pos hx.1 _,?_⟩,h⟩
    by_contra! ge
    have bad : 1≤y^3 := one_le_pow₀ ge
    rw [h] at bad; exact (not_le.mpr hx.2) bad

private theorem power_weight {v : ℝ} (hv : v∈Ioo 0 1) (k : ℕ) :
    |3*v^2| • Cut.betaWeight ((k:ℝ)+1/2) (3/2) (v^3) =
      3*(density v*v^(3*k+1)) := by
  have vp := hv.1
  rw [abs_of_nonneg (by positivity : 0≤3*v^2),smul_eq_mul,Cut.betaWeight,density,Real.sqrt_eq_rpow]
  rw [←Real.rpow_natCast v 3,←Real.rpow_mul vp.le]
  rw [show (3/2:ℝ)-1=1/2 by norm_num]
  simp only [Real.rpow_natCast]
  have w : v^2*v^((3:ℝ)*((k:ℝ)+1/2-1))=v^(-1/2:ℝ)*v^(3*k+1) := by
    rw [←Real.rpow_natCast v 2,←Real.rpow_natCast v (3*k+1),←Real.rpow_add vp,←Real.rpow_add vp]
    congr 1; push_cast; ring
  linear_combination 3*((1-v^3)^(1/2:ℝ))*w

/-- After the substitution x=v³ the kth beta moment equals π C_k/(6 · 4^k). -/
theorem catalan_moment (k : ℕ) :
    IntegrableOn (fun v : ℝ => density v*v^(3*k+1)) (Ioo 0 1) ∧
    (∫ v in Ioo (0:ℝ) 1, density v*v^(3*k+1))=Real.pi/6*(catalan k:ℝ)/4^k := by
  obtain ⟨hi,he⟩ := Cut.unit_beta (by positivity : 0<(k:ℝ)+1/2) (by norm_num : 0<(3/2:ℝ))
  have D (x : ℝ) (_ : x∈Ioo (0:ℝ) 1) :
      HasDerivWithinAt (fun v : ℝ => v^3) (3*x^2) (Ioo 0 1) x := by
    simpa using (hasDerivAt_pow 3 x).hasDerivWithinAt (s:=Ioo 0 1)
  have inj : InjOn (fun x:ℝ => x^3) (Ioo 0 1) := (Odd.strictMono_pow (by decide : Odd 3)).injective.injOn
  rw [←cube_image] at hi he
  rw [integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo D inj] at hi
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo D inj] at he
  have H := (integrableOn_congr_fun (fun x hx => power_weight hx k) measurableSet_Ioo).mp hi
  have ih := H.const_mul (1/3:ℝ)
  refine ⟨ih.congr (ae_restrict_of_forall_mem measurableSet_Ioo (fun x _ => by dsimp; ring)),?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioo (fun x hx => power_weight hx k),integral_const_mul,
    show (k:ℝ)+1/2+3/2=k+2 by ring] at he
  change 3*_ = Real.Gamma ((k:ℝ)+1/2)*gammaHalf/Real.Gamma ((k:ℝ)+2) at he
  rw [beta_value] at he
  linear_combination (1/3:ℝ)*he

theorem density_nonneg {v : ℝ} (hv : 0≤v) : 0≤density v :=
  mul_nonneg (Real.rpow_nonneg hv _) (Real.sqrt_nonneg _)

theorem density_le {v : ℝ} (hv : v∈Ioo 0 1) : density v≤v^(-1/2:ℝ) := by
  unfold density
  apply mul_le_of_le_one_right (Real.rpow_nonneg hv.1.le _)
  exact (Real.sqrt_le_one).mpr (sub_le_self _ (pow_nonneg hv.1.le _))

theorem density_integrable : IntegrableOn density (Ioo (0:ℝ) 1) := by
  have h : IntegrableOn (fun v : ℝ => v^(-1/2:ℝ)) (Ioo 0 1) := (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).mpr (by norm_num)
  apply h.mono' (by apply Measurable.aestronglyMeasurable; unfold density; fun_prop)
  exact ae_restrict_of_forall_mem measurableSet_Ioo fun v hv => by rw [Real.norm_of_nonneg (density_nonneg hv.1.le)]; exact density_le hv

noncomputable def osc (x : ℝ) := 2*Real.exp (x/2)*Real.cos (Real.sqrt 3*x/2-Real.pi/3)-Real.exp (-x)

set_option maxHeartbeats 900000 in
/-- The third-roots-of-unity filter integrated against the Catalan density. -/
theorem smallLimit_integral {q : ℝ} (qp : 0<q) :
    smallLimit (-q^3/4)=2/(Real.pi*q)*∫ v in Ioo (0:ℝ) 1, density v*osc (q*v) := by
  let a := fun k : ℕ => 3*(-1:ℝ)^k*q^(3*k+1)/(3*k+1).factorial
  let F := fun (k : ℕ) (v : ℝ) => a k*(density v*v^(3*k+1))
  have fi k : IntegrableOn (F k) (Ioo 0 1) := (catalan_moment k).1.const_mul _
  have mon k : (catalan k:ℝ)≤4^k := by simpa using Series.catalan_uniform_le 0 k k (by omega)
  have inj : Function.Injective (fun k : ℕ => 3*k+1) := fun i j h => by dsimp at h; omega
  have sub : Summable (fun k : ℕ => q^(3*k+1)/(↑(3*k+1).factorial:ℝ)) :=
    (NormedSpace.expSeries_div_hasSum_exp ℝ q).summable.comp_injective inj
  have fn : Summable (fun k : ℕ => ∫ v in Ioo (0:ℝ) 1, ‖F k v‖) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg (fun _ => norm_nonneg _)) (f:=fun k : ℕ =>
      (3*(Real.pi/6))*(q^(3*k+1)/(3*k+1).factorial)) (fun k => ?_) (sub.mul_left _)
    have eq := setIntegral_congr_fun (s:=Ioo (0:ℝ) 1) (μ:=volume) measurableSet_Ioo (f:=fun v : ℝ => ‖F k v‖) (g:=fun v =>
      (3*q^(3*k+1)/(3*k+1).factorial)*(density v*v^(3*k+1)))
      (fun v hv => by simp only [F,a,Real.norm_eq_abs,abs_mul,abs_div,abs_pow,abs_neg,abs_one,one_pow,
        Nat.abs_cast,abs_of_pos qp,abs_of_nonneg (density_nonneg hv.1.le),abs_of_pos hv.1]; norm_num)
    rw [eq,integral_const_mul,(catalan_moment k).2]
    have div : (catalan k:ℝ)/4^k≤1 := (div_le_one (by positivity)).mpr (mon k)
    calc
      _ = (3*(Real.pi/6)*(q^(3*k+1)/(3*k+1).factorial))*((catalan k:ℝ)/4^k) := by ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) div
  have sum := (hasSum_integral_of_summable_integral_norm fi fn).mul_left (2/(Real.pi*q))
  have filt (v : ℝ) : ∑' k, F k v=density v*osc (q*v) := by
    have t := (Far.filtered_exp (1:Fin 3) (q*v)).mul_left (density v)
    have qq : (∑' k, F k v)=_ := (tsum_congr (fun k => show F k v= _ from by
      dsimp [F,a]; rw [Nat.mul_comm 3 k,mul_pow]; ring)).trans t.tsum_eq
    rw [qq]
    congr 1
    norm_num [osc]
    ring
  rw [show (fun (x : ℝ) => ∑' k, F k x)=(fun v => density v*osc (q*v)) from funext filt] at sum
  unfold smallLimit
  rw [←sum.tsum_eq]
  apply tsum_congr
  intro k
  simp only [F,integral_const_mul,(catalan_moment k).2,a]
  rw [show (-q^3/4:ℝ)=(-1)*(q^3/4) by ring,mul_pow,div_pow]
  rw [show q^(3*k+1)=q*(q^3)^k by rw [pow_succ,pow_mul]; ring]
  field_simp [qp.ne',Real.pi_ne_zero]; ring

end BigDescents132.Peak
