import BigDescents132.SmallMoving
import BigDescents132.FarMoving

namespace BigDescents132.Slit
open Set Filter
open scoped Topology

noncomputable def smallScale (p : Param) : ℝ := (p.val-1)^((3:ℝ)⁻¹)
noncomputable def farScale (p : Param) : ℝ := p.val⁻¹^((3:ℝ)⁻¹)
noncomputable def edgeScale (p : Param) : ℝ := min (smallScale p) (farScale p)

theorem scales (p : Param) :
    0<smallScale p ∧ 0<farScale p ∧ farScale p<1 ∧
    (smallScale p)^3=p.val-1 ∧ (farScale p)^3=p.val⁻¹ ∧
    nearParam (smallScale p)=p ∧ farParam (farScale p)=p := by
  have sp := zero_lt_one.trans p.property
  have d : 0<smallScale p := Real.rpow_pos_of_pos (sub_pos.mpr p.property) _
  have e : 0<farScale p := Real.rpow_pos_of_pos (inv_pos.mpr sp) _
  have D : (smallScale p)^3=p.val-1 := Real.rpow_inv_natCast_pow (sub_nonneg.mpr p.property.le) (by decide)
  have E : (farScale p)^3=p.val⁻¹ := Real.rpow_inv_natCast_pow (inv_pos.mpr sp).le (by decide)
  have eu : farScale p<1 := by
    by_contra! h
    have z : 1≤(farScale p)^3 := one_le_pow₀ h
    rw [E] at z
    exact (not_le.mpr ((inv_lt_one₀ sp).mpr p.property)) z
  refine ⟨d,e,eu,D,E,Subtype.ext ?_,Subtype.ext ?_⟩
  · rw [nearParam_val d,D]; ring
  · rw [farParam_val ⟨e,eu⟩,inv_pow,E,inv_inv]

/-- A single constant controls the cosine error for every negative real
parameter and every moving rank with N E ≥ 7. Here E is the smaller of
(s-1)^(1/3) and s^(-1/3), and N=n+1. -/
theorem uniform_moving_interior :
    ∃ C : ℝ, 0≤C ∧ ∀ p : Param, ∀ n : ℕ, 8≤n+1 → 7≤((n+1:ℕ):ℝ)*edgeScale p →
      coefficientError p n ≤ C/(((n+1:ℕ):ℝ)*edgeScale p) := by
  obtain ⟨a,a0,near⟩ := small_moving
  obtain ⟨b,b0,far⟩ := far_moving
  obtain ⟨d,dp,ds⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp near
  obtain ⟨e,ep,es⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp far
  have dpos : 0<d := dp
  have epos : 0<e := ep
  let L := 1+d^3
  let U := (e^3)⁻¹
  let S : Set Param := Subtype.val ⁻¹' Icc L U
  have cc : IsCompact S := by
    apply Topology.IsInducing.subtypeVal.isCompact_preimage' isCompact_Icc
    intro x hx
    exact ⟨⟨x,(lt_add_of_pos_right 1 (pow_pos dpos 3)).trans_le hx.1⟩,rfl⟩
  obtain ⟨m,m0,mid⟩ := compact_interior S cc
  let C := max a (max b m)
  have aC : a≤C := le_max_left _ _
  have bC : b≤C := (le_max_left _ _).trans (le_max_right _ _)
  have mC : m≤C := (le_max_right _ _).trans (le_max_right _ _)
  have C0 := a0.trans aC
  refine ⟨C,C0,fun p n N7 NE => ?_⟩
  have N0 : 0<((n+1:ℕ):ℝ) := by positivity
  obtain ⟨δp,εp,ε1,δcube,εcube,hδ,hε⟩ := scales p
  have s0 := zero_lt_one.trans p.property
  have e0 : 0<edgeScale p := lt_min δp εp
  have lo : edgeScale p≤smallScale p := min_le_left _ _
  have hi : edgeScale p≤farScale p := min_le_right _ _
  have transport {v A : ℝ} (hv : edgeScale p≤v) (hA : A≤C) (bound : coefficientError p n≤A/(((n+1:ℕ):ℝ)*v)) :
      coefficientError p n≤C/(((n+1:ℕ):ℝ)*edgeScale p) := by
    have h0 := mul_pos N0 e0
    have hden := mul_le_mul_of_nonneg_left hv N0.le
    exact bound.trans ((div_le_div_of_nonneg_right hA (h0.le.trans hden)).trans
      (div_le_div_of_nonneg_left C0 h0 hden))
  by_cases hl : smallScale p<d
  · apply transport lo aC
    have h := ds ⟨δp,hl⟩ n N7 (NE.trans (mul_le_mul_of_nonneg_left lo N0.le))
    simpa only [hδ] using h
  by_cases hr : farScale p<e
  · apply transport hi bC
    have h := es ⟨εp,hr⟩ n N7 (NE.trans (mul_le_mul_of_nonneg_left hi N0.le))
    simpa only [hε] using h
  apply transport (hi.trans ε1.le) mC
  have member : p∈S := by
    have ld := pow_le_pow_left₀ dpos.le (le_of_not_gt hl) 3
    have he3 := pow_le_pow_left₀ epos.le (le_of_not_gt hr) 3
    rw [δcube] at ld; rw [εcube] at he3
    refine ⟨by dsimp [L]; linarith,?_⟩
    simpa [U] using (inv_anti₀ (pow_pos epos 3) he3)
  simpa only [mul_one] using mid p member n N7

end BigDescents132.Slit
