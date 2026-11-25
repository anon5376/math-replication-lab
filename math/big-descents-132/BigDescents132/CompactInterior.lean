import BigDescents132.PointContinuity

namespace BigDescents132.Slit
open Complex Set
open scoped ComplexConjugate Topology

instance (s : ℝ) : Subsingleton (Points s) where
  allEq a b := by
    have r : (a.r:ℂ)=(b.r:ℂ) := b.unique_small ((a.root_cases _).mpr (Or.inl rfl)) rfl a.small.2
    have R : (a.R:ℂ)=(b.R:ℂ) := b.unique_large ((a.root_cases _).mpr (Or.inr (Or.inl rfl))) rfl a.large.1
    have u : a.u=b.u := b.unique_upper ((a.root_cases _).mpr (Or.inr (Or.inr (Or.inl rfl)))) a.upper
    have rr := ofReal_inj.mp r
    have RR := ofReal_inj.mp R
    cases a; cases b; congr

theorem norm_radical (a z : ℂ) : ‖radical a z‖=Real.sqrt ‖argFactor a z‖ := by
  rw [←radical_sq, norm_pow,Real.sqrt_sq (norm_nonneg _)]

theorem data_continuous :
    Continuous (fun t : Param => (pointsAt t).slope) ∧
    Continuous (fun t : Param => (pointsAt t).poleBound) ∧
    Continuous (fun t : Param => (pointsAt t).farPole) ∧
    Continuous (fun t : Param => (pointsAt t).amplitudeRatio) ∧
    Continuous (fun t : Param => (pointsAt t).logGap) := by
  obtain ⟨r,R,u⟩ := points_continuous
  have sr (t : Param) := (pointsAt t).sr_gt
  have sn (t : Param) : 0<t.val := zero_lt_one.trans t.property
  have up (t : Param) := (pointsAt t).upper
  have un (t : Param) := (pointsAt t).u_ne
  have rc : Continuous (fun t : Param => ((pointsAt t).r:ℂ)) := Complex.continuous_ofReal.comp r
  have Rc : Continuous (fun t : Param => ((pointsAt t).R:ℂ)) := Complex.continuous_ofReal.comp R
  have cu : Continuous (fun t : Param => conj (pointsAt t).u) := Complex.continuous_conj.comp u
  have rad {x z : Param → ℂ} (xc : Continuous x) (zc : Continuous z) (xn : ∀ t, x t≠0) :
      Continuous (fun t => ‖radical (x t) (z t)‖) := by
    simp only [norm_radical,argFactor]
    exact (continuous_const.sub (zc.div xc xn)).norm.sqrt
  have rn (t : Param) := ofReal_ne_zero.mpr (pointsAt t).rpos.ne'
  have Rn (t : Param) := ofReal_ne_zero.mpr (pointsAt t).Rpos.ne'
  have cun (t : Param) := (pointsAt t).cu_ne
  have den (t : Param) : (pointsAt t).rayOther (pointsAt t).u (pointsAt t).u≠0 := by
    simpa using (pointsAt t).rayOther_ne (up t).ne' (le_rfl : (0:ℝ)≤0)
  have sC : Continuous (fun t : Param => (t.val:ℂ)) := Complex.continuous_ofReal.comp continuous_subtype_val
  have pole : Continuous (fun t : Param => ‖1-(t.val:ℂ)*(pointsAt t).u‖) := (continuous_const.sub (sC.mul u)).norm
  refine ⟨u.norm.div (Complex.continuous_im.comp u) (fun t => (up t).ne'),?_,?_,?_,?_⟩
  · exact pole.div (continuous_subtype_val.mul (Complex.continuous_im.comp u)) (fun t => (mul_pos (sn t) (up t)).ne')
  · exact pole.div ((continuous_subtype_val.mul r).sub continuous_const) (fun t => (sub_pos.mpr (sr t)).ne')
  · apply Continuous.div _ _ (fun t => mul_ne_zero (by norm_num : (2:ℝ)≠0) (norm_ne_zero_iff.mpr (den t)))
    · simp only [Points.realOther,norm_mul]
      exact ((rad Rc rc Rn).mul (rad u rc un)).mul (rad cu rc cun)
    · simp only [Points.rayOther,norm_mul]
      exact continuous_const.mul (((rad rc u rn).mul (rad Rc u Rn)).mul (rad cu u cun))
  · exact (r.div u.norm (fun t => norm_ne_zero_iff.mpr (un t))).log
      (fun t => (div_pos (pointsAt t).rpos (norm_pos_iff.mpr (un t))).ne')

/-- Uniform O(1/N) oscillatory approximation for the actual coefficients on
every compact subset of the negative-parameter interval. -/
theorem compact_interior (S : Set Param) (hS : IsCompact S) :
    ∃ C : ℝ, 0≤C ∧ ∀ p∈S, ∀ n : ℕ, 8≤n+1 →
      |(B (n+1)).eval (1-p.val)/(2*‖(pointsAt p).complexWeight (n+1)‖*Cut.moment (n+1) 0)-
        Real.cos ((pointsAt p).complexWeight (n+1)).arg|≤C/((n+1:ℕ):ℝ) := by
  by_cases ne : S.Nonempty
  · obtain ⟨a,ha⟩ := ne
    obtain ⟨cs,cp,cf,cr,cg⟩ := data_continuous
    obtain ⟨K,hK⟩ := hS.bddAbove_image cs.continuousOn
    obtain ⟨P₀,h₀⟩ := hS.bddAbove_image cp.continuousOn
    obtain ⟨P₁,h₁⟩ := hS.bddAbove_image cf.continuousOn
    obtain ⟨D,hD⟩ := hS.bddAbove_image cr.continuousOn
    obtain ⟨m,hm,hmin⟩ := hS.exists_isMinOn ⟨a,ha⟩ cg.continuousOn
    let P := max P₀ P₁
    let c := (pointsAt m).logGap
    have K1 := (pointsAt a).slope_ge_one.trans (hK ⟨_,ha,rfl⟩)
    have Ppos : 0<P := (pointsAt a).poleBound_pos.trans_le ((h₀ ⟨_,ha,rfl⟩).trans (le_max_left _ _))
    have d0 : 0≤D := (show 0≤(pointsAt a).amplitudeRatio by unfold Points.amplitudeRatio; positivity).trans (hD ⟨_,ha,rfl⟩)
    have c0 : 0<c := (pointsAt m).logGap_pos
    have K0 := zero_le_one.trans K1
    have cp0 : 0≤cosineError K P := by unfold cosineError; positivity
    refine ⟨28*cosineError K P+6*D*cosineError K P/c^2,by positivity,fun p hp n hn => ?_⟩
    have N7 : 7≤((n+1:ℕ):ℝ)*1 := by rw [mul_one]; exact_mod_cast (show 7≤n+1 by omega)
    simpa only [mul_one] using (pointsAt p).geometry_cosine n hn zero_lt_one (le_rfl : (1:ℝ)≤1)
      le_rfl K1 d0 c0 N7 (by simpa using hK ⟨p,hp,rfl⟩) ((h₀ ⟨_,hp,rfl⟩).trans (le_max_left _ _))
      (Or.inr ((h₁ ⟨_,hp,rfl⟩).trans (le_max_right _ _))) (hD ⟨_,hp,rfl⟩) (by simpa [c] using hmin hp)
  · exact ⟨0,le_rfl,fun p hp => (ne ⟨p,hp⟩).elim⟩

end BigDescents132.Slit
