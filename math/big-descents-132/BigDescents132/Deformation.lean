import BigDescents132.Outer
import Mathlib.MeasureTheory.Integral.ExpDecay

namespace BigDescents132.Slit
open Complex Filter Set MeasureTheory Asymptotics
open scoped ComplexConjugate Topology

/-- Both oriented neighborhoods at any positive radius are genuine approach
filters. The paths are straight transverse segments. -/
private theorem radial_neBot {a : ℂ} (ha : a≠0) (x : ℝ) :
    (𝓝[leftSide a] (radial a x)).NeBot ∧ (𝓝[rightSide a] (radial a x)).NeBot := by
  let r := radial a x
  let P := fun (t : ℝ) => r+a*(t:ℂ)*I
  have h : Continuous P := by dsimp [P]; fun_prop
  have sgn (t : ℝ) : (P t/a).im=t := by
    have e : P t/a=((Real.exp x/‖a‖:ℝ):ℂ)+(t:ℂ)*I := by
      dsimp [P,r,radial]; field_simp [ha]; ring
    rw [e]; simp
  have left : Tendsto P (𝓝[>] (0:ℝ)) (𝓝[leftSide a] r) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨by simpa [P] using (h.continuousAt (x:=0)).continuousWithinAt (s:=Ioi 0) |>.tendsto,?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0<(P t/a).im
    rwa [sgn]
  have right : Tendsto P (𝓝[<] (0:ℝ)) (𝓝[rightSide a] r) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨by simpa [P] using (h.continuousAt (x:=0)).continuousWithinAt (s:=Iio 0) |>.tendsto,?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    change (P t/a).im<0
    rwa [sgn]
  exact ⟨left.neBot,right.neBot⟩

private theorem weighted_integrable {s : ℝ} (g : Points s) (n : ℕ) {a : ℂ} (ha : a≠0)
    {J : ℝ → ℂ} (jump : ∀ x, HasJump g.branch a (radial a x) (J x))
    (hcont : Continuous (weighted n a J)) (b : ℝ) :
    IntegrableOn (weighted n a J) (Ioi b) := by
  obtain ⟨C,hC,bnd⟩ := g.outer_bound
  apply (integrable_norm_iff hcont.aestronglyMeasurable).mp
  apply integrable_of_isBigO_exp_neg (b:=1) zero_lt_one hcont.norm.continuousOn
  apply IsBigO.of_bound (2*C)
  filter_upwards [Real.tendsto_exp_atTop.eventually_gt_atTop 2] with x hx
  obtain ⟨L,R,hl,hr,hj⟩ := jump x
  obtain ⟨nl,nr⟩ := radial_neBot ha x
  have positive := Real.exp_pos x
  have mag (S : Set ℂ) [NeBot (𝓝[S] (radial a x))] (v : ℂ)
      (lim : Tendsto g.branch (𝓝[S] (radial a x)) (𝓝 v)) : ‖v‖≤C/(Real.exp x) := by
    rw [←radial_norm ha x]
    have normlim := (continuous_norm.continuousAt (x:=radial a x)).continuousWithinAt (s:=S) |>.tendsto
    apply le_of_tendsto_of_tendsto lim.norm (tendsto_const_nhds.div normlim (by rw [radial_norm ha]; exact positive.ne'))
    filter_upwards [normlim.eventually_const_lt (by simpa [radial_norm ha] using hx)] with z hz
    exact bnd z hz.le
  have lbd := mag _ _ hl
  have rbd := mag _ _ hr
  have bj : ‖J x‖≤2*C/Real.exp x := by rw [←hj]; exact (norm_sub_le L R).trans ((add_le_add lbd rbd).trans_eq (by ring))
  simp only [Real.norm_eq_abs,abs_norm,neg_one_mul,Real.exp_neg,abs_of_pos (inv_pos.mpr positive)]
  rw [weighted,norm_mul,norm_pow,norm_inv,radial_norm ha]
  have ip : (Real.exp x)⁻¹^n≤1 := pow_le_one₀ (inv_nonneg.mpr positive.le)
    ((inv_le_one₀ positive).mpr (by linarith))
  exact (mul_le_of_le_one_left (norm_nonneg _) ip).trans (bj.trans_eq (by ring))

theorem Points.cut_integrable {s : ℝ} (g : Points s) (n : ℕ) (a : ℝ) :
    IntegrableOn (weighted n g.r g.realJump) (Ioi a) ∧
    IntegrableOn (weighted n g.u (g.complexJump g.u)) (Ioi a) ∧
    IntegrableOn (weighted n (conj g.u) (g.complexJump (conj g.u))) (Ioi a) := by
  obtain ⟨hr,hu,hl⟩ := g.jump_continuous n
  exact ⟨weighted_integrable g n (ofReal_ne_zero.mpr g.rpos.ne') g.all_real_jumps hr a,
    weighted_integrable g n g.u_ne (g.all_complex_jumps (Or.inl rfl)) hu a,
    weighted_integrable g n g.cu_ne (g.all_complex_jumps (Or.inr rfl)) hl a⟩

/-- The outer circle vanishes and each radial integral converges absolutely.
This limit deforms an arbitrary coefficient circle to the actual three jumps. -/
theorem Points.circle_from_cuts {s : ℝ} (g : Points s) (n : ℕ) (a : ℝ) :
    (∮ z in C((0:ℂ),Real.exp a), z⁻¹^(n+1)*g.branch z)=
    (∫ x in Ioi a, weighted n g.r g.realJump x)+
      (∫ x in Ioi a, weighted n g.u (g.complexJump g.u) x)+
      (∫ x in Ioi a, weighted n (conj g.u) (g.complexJump (conj g.u)) x) := by
  obtain ⟨hr,hu,hl⟩ := g.cut_integrable n a
  have hj := ((intervalIntegral_tendsto_integral_Ioi a hr tendsto_id).add
    (intervalIntegral_tendsto_integral_Ioi a hu tendsto_id)).add (intervalIntegral_tendsto_integral_Ioi a hl tendsto_id)
  have H := (g.outer_vanishes n).add hj
  simp only [zero_add] at H
  exact tendsto_nhds_unique tendsto_const_nhds (H.congr (fun b => (g.annular_deformation n a b).symm))

private theorem all_if_zero {f : ℝ → ℂ} (a : ℝ) (hf : IntegrableOn f (Ioi a))
    (zero : ∀ x≤a, f x=0) : (∫ x in Ioi a, f x)=∫ x, f x := by
  have e : EqOn f 0 (Iic a) := zero
  have int : IntegrableOn f (Iic a) := (integrableOn_congr_fun e measurableSet_Iic).mpr integrableOn_zero
  have full : Integrable f := by simpa using (int.union hf)
  have complement : ∫ x in (Ioi a)ᶜ, f x=0 := by rw [compl_Ioi,setIntegral_congr_fun measurableSet_Iic e]; simp
  have res := integral_add_compl (s:=Ioi a) measurableSet_Ioi full
  rwa [complement,add_zero] at res

noncomputable def wholeCut (n : ℕ) (a : ℂ) (J : ℝ → ℂ) := ∫ x : ℝ, weighted n a J x

/-- Exact convergent three-cut identity for the literal permutation polynomial,
with the positive Cauchy sign on all three outward radial integrals. -/
theorem Points.coefficient_from_cuts {s : ℝ} (g : Points s) (n : ℕ) :
    Complex.ofReal ((B (n+1)).eval (1-s))=(2*Real.pi*I:ℂ)⁻¹ *
      (wholeCut n g.r g.realJump+wholeCut n g.u (g.complexJump g.u)+
        wholeCut n (conj g.u) (g.complexJump (conj g.u))) := by
  obtain ⟨ε,ep,circle⟩ := g.coefficient
  let r := min ε ‖g.u‖/2
  have rpos : 0<r := by dsimp [r]; exact div_pos (lt_min ep (norm_pos_iff.mpr g.u_ne)) (by norm_num)
  have re : r<ε := by dsimp [r]; have := min_le_left ε ‖g.u‖; linarith
  have ru : r<‖g.u‖ := by dsimp [r]; have := min_le_right ε ‖g.u‖; linarith [norm_pos_iff.mpr g.u_ne]
  let a := Real.log r
  have ea : Real.exp a=r := Real.exp_log rpos
  rw [circle r ⟨rpos,re⟩ n,←ea,g.circle_from_cuts]
  obtain ⟨hr,hu,hl⟩ := g.cut_integrable n a
  have small (x : ℝ) (hx : x≤a) := ((Real.exp_le_exp.mpr hx).trans_eq ea).trans_lt ru
  have zero {u : ℂ} (h : ‖u‖=‖g.u‖) (x : ℝ) (hx : x≤a) : weighted n u (g.complexJump u) x=0 := by
    have ne : excess u x<0 := sub_neg.mpr ((div_lt_one (h ▸ norm_pos_iff.mpr g.u_ne)).mpr (h ▸ small x hx))
    simp [weighted,Points.complexJump,not_le.mpr ne]
  rw [all_if_zero a hr (fun x hx => by simp [weighted,Points.realJump,not_le.mpr ((small x hx).trans g.dominant)]),
    all_if_zero a hu (zero rfl),all_if_zero a hl (zero (by simp))]
  rfl

end BigDescents132.Slit
