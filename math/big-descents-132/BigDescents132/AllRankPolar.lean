import BigDescents132.AllRankCoordinate

namespace BigDescents132.AllRanks.Coordinate
open Complex Set Slit
variable (c : Coordinate)

theorem cu_parts :
    c.cu.re=c.z/c.h ∧ c.cu.im=c.z*(Real.sqrt 3*c.p)/c.h := by
  simp [cu,Complex.div_ofReal_re,Complex.div_ofReal_im,Complex.mul_re,Complex.mul_im]

theorem actual_upper_data :
    let g := pointsAt c.param
    ‖g.u‖=(c.z/c.h)^2*(1+3*c.p^2) ∧
    g.u.re=(c.z/c.h)^2*(1-3*c.p^2) ∧
    g.u.im=(c.z/c.h)^2*(2*Real.sqrt 3*c.p) := by
  obtain ⟨re,im⟩ := c.cu_parts
  have rt := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have mu : ‖c.cu^2‖=(c.z/c.h)^2*(1+3*c.p^2) := by
    rw [norm_pow,Complex.sq_norm,Complex.normSq_apply,re,im]
    linear_combination (c.z^2*c.p^2/c.h^2)*rt
  have ur : (c.cu^2).re=(c.z/c.h)^2*(1-3*c.p^2) := by
    rw [pow_two,Complex.mul_re,re,im]
    linear_combination -(c.z^2*c.p^2/c.h^2)*rt
  have ui : (c.cu^2).im=(c.z/c.h)^2*(2*Real.sqrt 3*c.p) := by
    rw [pow_two,Complex.mul_im,re,im]; ring
  dsimp only
  rw [c.small_large_upper.2.2]
  exact ⟨mu,ur,ui⟩

theorem theta_eq : (pointsAt c.param).u.arg=2*Real.arctan (Real.sqrt 3*c.p) := by
  obtain ⟨re,im⟩ := c.cu_parts
  have pos := c.hpos
  have pp := c.p_mem.1
  have zz := c.z_mem.1
  have cr : 0<c.cu.re := re ▸ div_pos zz pos
  have ar := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl cr)
  have al := Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl cr)
  have cq := Real.arctan_tan al ar
  rw [Complex.tan_arg,re,im] at cq
  have rat : (c.z*(Real.sqrt 3*c.p)/c.h)/(c.z/c.h)=Real.sqrt 3*c.p := by field_simp
  rw [rat] at cq
  have cn : c.cu≠0 := by intro eq; rw [eq] at cr; exact (lt_irrefl _ cr)
  have nn : 0≤c.cu.arg := Complex.arg_nonneg_iff.mpr (by rw [im]; positivity)
  rw [c.small_large_upper.2.2,pow_two,Complex.arg_mul cn cn ⟨by linarith [Real.pi_pos],by linarith⟩,←cq]; ring

theorem actual_slope : (pointsAt c.param).slope=(1+3*c.p^2)/(2*Real.sqrt 3*c.p) := by
  obtain ⟨a,_,b⟩ := c.actual_upper_data
  have z := c.z_mem.1
  have h := c.hpos
  have pp := c.p_mem.1
  have r : 0<Real.sqrt 3 := by positivity
  rw [Points.slope,a,b]
  field_simp
  ring

end BigDescents132.AllRanks.Coordinate
