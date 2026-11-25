import BigDescents132.Strip

namespace BigDescents132.Slit
open Complex Filter Set MeasureTheory
open scoped ComplexConjugate Topology

noncomputable def direction (φ : ℝ) := Complex.exp ((φ:ℂ)*I)
noncomputable def polarPoint (x φ : ℝ) := Complex.exp ((x:ℂ)+(φ:ℂ)*I)

@[simp] theorem direction_zero : direction 0=1 := by simp [direction]
@[simp] theorem direction_period : direction (2*Real.pi)=1 := by simp [direction]
@[simp] theorem norm_direction (φ : ℝ) : ‖direction φ‖=1 := by simp [direction,Complex.norm_exp]
theorem direction_ne (φ : ℝ) : direction φ≠0 := Complex.exp_ne_zero _
theorem direction_sub (a b : ℝ) : direction (a-b)=direction a/direction b := by
  simp [direction,sub_mul,Complex.exp_sub]
theorem direction_reflect (a : ℝ) : direction (2*Real.pi-a)=conj (direction a) := by
  rw [direction_sub,direction_period,one_div]
  simp [direction,←Complex.exp_neg,←Complex.exp_conj]

theorem exp_polar (z : ℂ) : Complex.exp z=(Real.exp z.re:ℂ)*direction z.im := by
  change Complex.exp z=(Real.exp z.re:ℂ)*Complex.exp ((z.im:ℂ)*I)
  rw [Complex.ofReal_exp,←Complex.exp_add,Complex.re_add_im]

theorem polar_eq (x y : ℝ) : polarPoint x y=(Real.exp x:ℂ)*direction y := by
  simp [polarPoint,direction,Complex.exp_add,Complex.ofReal_exp]

theorem direction_unique {a b : ℝ} (ha : a∈Ico 0 (2*Real.pi)) (hb : b∈Ico 0 (2*Real.pi))
    (eq : direction a=direction b) : a=b := by
  obtain ⟨k,h⟩ := Complex.exp_eq_exp_iff_exists_int.mp eq
  have hi := congrArg Complex.im h
  simp [Complex.mul_im] at hi
  have pi := Real.pi_pos
  rcases lt_trichotomy k 0 with hneg|rfl|hpos
  · have hk : (k:ℝ)≤ -1 := by exact_mod_cast (show k≤ -1 by omega)
    linarith [mul_le_mul_of_nonneg_right hk (by linarith : 0≤2*Real.pi),ha.1,hb.2]
  · simpa using hi
  · have hk : (1:ℝ)≤k := by exact_mod_cast (show (1:ℤ)≤k by omega)
    linarith [mul_le_mul_of_nonneg_right hk (by linarith : 0≤2*Real.pi),hb.1,ha.2]

/-- Different directions give an uncut radical on the whole open ray. -/
theorem regular_angular {a φ : ℝ} {z : ℂ} (ha : 0<a)
    (hφ : φ∈Ico 0 (2*Real.pi)) (hz : z.im∈Ico 0 (2*Real.pi)) (hne : z.im≠φ) :
    argFactor ((a:ℂ)*direction φ) (Complex.exp z)∈slitPlane := by
  apply (factor_mem_iff (mul_ne_zero (ofReal_ne_zero.mpr ha.ne') (direction_ne _))).mpr
  intro c hc eq
  rw [exp_polar] at eq
  have hn := congrArg norm eq
  simp [norm_mul,norm_direction,Real.norm_of_nonneg ha.le,
    Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_of_nonneg (zero_le_one.trans hc)] at hn
  apply hne (direction_unique hz hφ ?_)
  calc
    direction z.im = (((Real.exp z.re:ℝ):ℂ)*direction z.im)/(Real.exp z.re:ℂ) := by
      field_simp [ofReal_ne_zero.mpr (Real.exp_pos _).ne']
    _ = direction φ := by
      rw [eq,hn]; push_cast; field_simp [ofReal_ne_zero.mpr ha.ne',ofReal_ne_zero.mpr (zero_lt_one.trans_le hc).ne']; ring

private theorem exp_over_direction_im (z : ℂ) (c φ : ℝ) :
    (Complex.exp z/((c:ℂ)*direction φ)).im=(Real.exp z.re/c)*Real.sin (z.im-φ) := by
  rw [exp_polar]
  have eq : ((Real.exp z.re:ℂ)*direction z.im)/((c:ℂ)*direction φ)=
      ((Real.exp z.re/c:ℝ):ℂ)*direction (z.im-φ) := by
    rw [direction_sub]; push_cast; ring
  rw [eq]
  simp [Complex.mul_im,direction,Complex.exp_im,Complex.exp_re]

theorem exp_left {l h c : ℝ} (hc : 0<c) (x : ℝ) :
    Tendsto Complex.exp (𝓝[strip l h] ((x:ℂ)+(l:ℂ)*I))
      (𝓝[leftSide ((c:ℂ)*direction l)] (polarPoint x l)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨Complex.continuous_exp.continuousAt.continuousWithinAt.tendsto,?_⟩
  have hn : ∀ᶠ w : ℂ in 𝓝 ((x:ℂ)+(l:ℂ)*I), w.im<l+Real.pi :=
    Complex.continuous_im.continuousAt.tendsto.eventually_lt_const (by simp [Real.pi_pos])
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds hn] with w hw hup
  change 0<(Complex.exp w/((c:ℂ)*direction l)).im
  rw [exp_over_direction_im]
  exact mul_pos (div_pos (Real.exp_pos _) hc) (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr hw.2.1) (by linarith))

theorem exp_right {l h c : ℝ} (hc : 0<c) (x : ℝ) :
    Tendsto Complex.exp (𝓝[strip l h] ((x:ℂ)+(h:ℂ)*I))
      (𝓝[rightSide ((c:ℂ)*direction h)] (polarPoint x h)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨Complex.continuous_exp.continuousAt.continuousWithinAt.tendsto,?_⟩
  have hn : ∀ᶠ w : ℂ in 𝓝 ((x:ℂ)+(h:ℂ)*I), h-Real.pi<w.im :=
    Complex.continuous_im.continuousAt.tendsto.eventually_const_lt (by simp [Real.pi_pos])
  filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds hn] with w hw hlo
  change (Complex.exp w/((c:ℂ)*direction h)).im<0
  rw [exp_over_direction_im]
  exact mul_neg_of_pos_of_neg (div_pos (Real.exp_pos _) hc)
    (Real.sin_neg_of_neg_of_neg_pi_lt (sub_neg.mpr hw.2.2) (by linarith))

variable {s : ℝ} (g : Points s)

theorem Points.angle : g.u.arg∈Ioo 0 Real.pi := by
  have pos := Complex.arg_nonneg_iff.mpr g.upper.le
  refine ⟨pos.lt_of_ne ?_,Complex.arg_lt_pi_iff.mpr (Or.inr g.upper.ne')⟩
  intro e
  have z := Complex.norm_mul_exp_arg_mul_I g.u
  have h := congrArg Complex.im z
  simp [←e] at h
  linarith [g.upper]

theorem Points.upper_polar : g.u=(‖g.u‖:ℂ)*direction g.u.arg := (Complex.norm_mul_exp_arg_mul_I _).symm

theorem Points.lower_polar : conj g.u=(‖g.u‖:ℂ)*direction (2*Real.pi-g.u.arg) := by
  rw [direction_reflect]
  simpa using congrArg (conj : ℂ → ℂ) g.upper_polar

/-- Holomorphy at every logarithmic point between consecutive cut directions. -/
theorem Points.exp_domain {z : ℂ} (h : z.im∈Ioo 0 (2*Real.pi))
    (hu : z.im≠g.u.arg) (hl : z.im≠2*Real.pi-g.u.arg) : Complex.exp z∈g.domain := by
  have p := Real.pi_pos
  have an := g.angle
  have e : z.im∈Ico 0 (2*Real.pi) := ⟨h.1.le,h.2⟩
  have real (a : ℝ) (ha : 0<a) : argFactor a (Complex.exp z)∈slitPlane := by
    simpa using regular_angular ha (φ:=0) ⟨le_rfl,by linarith⟩ e h.1.ne'
  refine ⟨real _ g.rpos,real _ g.Rpos,?_,?_⟩
  · nth_rw 1 [g.upper_polar]
    exact regular_angular (norm_pos_iff.mpr g.u_ne) ⟨an.1.le,by linarith [an.2]⟩ e hu
  · rw [g.lower_polar]
    exact regular_angular (norm_pos_iff.mpr g.u_ne) ⟨by linarith [an.2],by linarith [an.1]⟩ e hl

end BigDescents132.Slit
