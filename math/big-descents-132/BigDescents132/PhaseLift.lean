import BigDescents132.UniformInterior
import BigDescents132.Phase

namespace BigDescents132.Slit
open Complex Set
open scoped Topology ComplexConjugate

noncomputable def orientation (z : ℂ) := z/(‖z‖:ℂ)

private theorem orient_mul (z w : ℂ) : orientation (z*w)=orientation z*orientation w := by
  simp [orientation,norm_mul]; ring
private theorem orient_div (z w : ℂ) : orientation (z/w)=orientation z/orientation w := by
  simp [orientation,norm_div]; ring
private theorem orient_inv (z : ℂ) : orientation z⁻¹=(orientation z)⁻¹ := by simp [orientation,div_eq_mul_inv,mul_comm]
private theorem orient_pow (z : ℂ) (n : ℕ) : orientation (z^n)=(orientation z)^n := by simp [orientation,div_pow]
private theorem orient_pos {r : ℝ} (hr : 0<r) : orientation (r:ℂ)=1 := by simp [orientation,Real.norm_of_nonneg hr.le,hr.ne']
private theorem orient_neg {r : ℝ} (hr : r<0) : orientation (r:ℂ)= -1 := by simp [orientation,Real.norm_of_nonpos hr.le,hr.ne]
private theorem orient_exp (z : ℂ) : orientation (Complex.exp z)=direction z.im := by
  unfold orientation
  rw [Complex.norm_exp,exp_polar]
  field_simp
private theorem orient_arg {z : ℂ} (h : z≠0) : orientation z=direction z.arg := by
  unfold orientation direction
  apply (div_eq_iff (ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h))).mpr
  rw [mul_comm,Complex.norm_mul_exp_arg_mul_I]
private theorem circle_add (a b : ℝ) : direction (a+b)=direction a*direction b := by simp [direction,add_mul,Complex.exp_add]
private theorem circle_nat (n : ℕ) (a : ℝ) : direction ((n:ℝ)*a)=direction a^n := by
  simp only [direction,Complex.ofReal_mul,Complex.ofReal_natCast,mul_assoc,Complex.exp_nat_mul]
private theorem circle_neg (a : ℝ) : direction (-a)=(direction a)⁻¹ := by simp [direction,Complex.exp_neg]
private theorem orient_root {a z : ℂ} (h : argFactor a z∈slitPlane) :
    orientation (radical a z)=direction ((argFactor a z).arg/2) := by
  rw [radical,Complex.cpow_def_of_ne_zero (Complex.slitPlane_ne_zero h),orient_exp]
  congr 1; simp [Complex.mul_im,Complex.log_im]; ring

noncomputable def Points.phaseOffset {s : ℝ} (g : Points s) :=
  Real.pi+((argFactor g.r g.u).arg+(argFactor g.R g.u).arg+(argFactor (conj g.u) g.u).arg)/2-
    g.u.arg-(1-(s:ℂ)*g.u).arg

noncomputable def phase (p : Param) (N : ℕ) :=
  (N:ℝ)*(pointsAt p).u.arg-(pointsAt p).phaseOffset

theorem Points.pole_slit {s : ℝ} (g : Points s) : 1-(s:ℂ)*g.u ∈ slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
  have s0 := zero_lt_one.trans g.parameter
  simp [Complex.mul_im,s0.ne',g.upper.ne']

theorem Points.cos_phase {s : ℝ} (g : Points s) (N : ℕ) :
    Real.cos ((N:ℝ)*g.u.arg-g.phaseOffset)=Real.cos (g.complexWeight N).arg := by
  obtain ⟨hr,hR,hu⟩ := ray_arguments g g.upper.ne' (v:=0) le_rfl
  simp only [Complex.ofReal_zero,add_zero,mul_one] at hr hR hu
  have hpi : direction Real.pi= -1 := by simp [direction]
  have h2 : orientation (2:ℂ)=1 := by simpa using orient_pos (by norm_num : 0<(2:ℝ))
  have hs : orientation (1-(s:ℂ))= -1 := by simpa using orient_neg (sub_neg.mpr g.parameter)
  let θ := g.u.arg
  have dirs : orientation (g.complexWeight N)=direction (g.phaseOffset-(N:ℝ)*θ) := by
    simp only [Points.complexWeight,weight,amplitude,Points.rayOther,orient_mul,orient_div,orient_pow,orient_inv,
      orient_root hr,orient_root hR,orient_root hu,h2,orient_pos Real.pi_pos,hs,orient_arg g.u_ne,orient_arg g.spole_ne]
    rw [Points.phaseOffset,add_div,add_div]
    simp only [direction_sub,circle_add,hpi,circle_nat,θ]
    ring
  have z := congrArg Complex.re ((orient_arg (g.complexWeight_ne N)).symm.trans dirs)
  simp only [direction,Complex.exp_re,Complex.mul_I_re,Complex.ofReal_im,neg_zero,Real.exp_zero,one_mul,Complex.mul_I_im,Complex.ofReal_re] at z
  rw [show (N:ℝ)*g.u.arg-g.phaseOffset= -(g.phaseOffset-(N:ℝ)*θ) by dsimp [θ]; ring,Real.cos_neg,z]

theorem phase_continuous (N : ℕ) : Continuous (fun p : Param => phase p N) := by
  obtain ⟨r,R,u⟩ := points_continuous
  have sC := Complex.continuous_ofReal.comp (continuous_subtype_val (p:=fun x : ℝ => 1<x))
  have rc := Complex.continuous_ofReal.comp r
  have Rc := Complex.continuous_ofReal.comp R
  have cu := Complex.continuous_conj.comp u
  have K {f : Param → ℂ} (cf : Continuous f) (roots : ∀ p, f p∈slitPlane) :
      Continuous (fun p => (f p).arg) := continuous_iff_continuousAt.mpr fun p => (Complex.continuousAt_arg (roots p)).comp cf.continuousAt
  have data (p : Param) := ray_arguments (pointsAt p) (pointsAt p).upper.ne' (v:=0) le_rfl
  simp only [Complex.ofReal_zero,add_zero,mul_one] at data
  have a := K u (fun p => Complex.mem_slitPlane_iff.mpr (Or.inr (pointsAt p).upper.ne'))
  have b := K (continuous_const.sub (u.div rc (fun p => ofReal_ne_zero.mpr (pointsAt p).rpos.ne'))) (fun p => (data p).1)
  have c := K (continuous_const.sub (u.div Rc (fun p => ofReal_ne_zero.mpr (pointsAt p).Rpos.ne'))) (fun p => (data p).2.1)
  have d := K (continuous_const.sub (u.div cu (fun p => (pointsAt p).cu_ne))) (fun p => (data p).2.2)
  have pole := K (continuous_const.sub (sC.mul u)) (fun p => (pointsAt p).pole_slit)
  exact (continuous_const.mul a).sub (((continuous_const.add (((b.add c).add d).div_const 2)).sub a).sub pole)

/-- The criterion for an actual alternating sign at every interior integer phase
level has one uniform lower bound on N E for the whole negative axis. -/
theorem interior_phase_sign :
    ∃ L : ℝ, 0<L ∧ ∀ p : Param, ∀ n j : ℕ, 8≤n+1 → L<((n+1:ℕ):ℝ)*edgeScale p →
      phase p (n+1)=(j:ℝ)*Real.pi → AlternatesAt (B (n+1)) j (p.val-1) := by
  obtain ⟨C,c0,err⟩ := uniform_moving_interior
  refine ⟨max 7 C,(by norm_num : (0:ℝ)<7).trans_le (le_max_left _ _),fun p n j hn hu level => ?_⟩
  let g := pointsAt p
  have E := err p n hn ((le_max_left _ _).trans hu.le)
  have NE := lt_of_lt_of_le (by norm_num : (0:ℝ)<7) ((le_max_left _ _).trans hu.le)
  have h : coefficientError p n < 1 := E.trans_lt ((div_lt_one NE).mpr ((le_max_right _ _).trans_lt hu))
  have phaseEq : Real.cos ((j:ℝ)*Real.pi)=Real.cos (g.complexWeight (n+1)).arg := level ▸ g.cos_phase (n+1)
  apply sign_at_cosine_extremum (g.normalizer_pos n) (phase:=(j:ℝ)) rfl
  simpa only [neg_sub,phaseEq] using h

end BigDescents132.Slit
