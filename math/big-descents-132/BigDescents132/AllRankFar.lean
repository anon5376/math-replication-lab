import BigDescents132.PhaseEnds
import Mathlib.Analysis.Polynomial.Basic

namespace BigDescents132.AllRanks
open Complex Slit Filter Set Polynomial
open scoped Polynomial Topology

private theorem far_sign (N : ℕ) (hn : 2<expectedDegree N) :
    ∀ᶠ x : ℝ in atTop, AlternatesAt (B N) (expectedDegree N) x := by
  let p:=B N
  let d:=expectedDegree N
  let f:ℝ[X]:=Polynomial.C ((-1:ℝ)^d)*p.comp (-X)
  have deg : p.natDegree=d := degree_all N
  have sig : (-1:ℝ)^d≠0 := pow_ne_zero _ (by norm_num)
  have dq : ((-X:ℝ[X])).natDegree≠0 := by simp
  have df : f.natDegree=d := by
    change (Polynomial.C ((-1:ℝ)^d)*p.comp (-X)).natDegree=d
    rw [natDegree_C_mul sig,Polynomial.natDegree_comp,deg];simp
  have lead : f.leadingCoeff=p.leadingCoeff := by
    rw [show f=Polynomial.C ((-1:ℝ)^d)*p.comp (-X) by rfl,leadingCoeff_mul,leadingCoeff_C,leadingCoeff_comp dq,
      leadingCoeff_neg,leadingCoeff_X,deg]
    calc
      _ = p.leadingCoeff*((-1:ℝ)*(-1))^d := by rw [mul_pow];ring
      _ = _ := by norm_num
  have pos : 0<f.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (by rw [df];exact (by omega : 0<expectedDegree N))
  have lim:=f.tendsto_atTop_of_leadingCoeff_nonneg pos (lead ▸ B_coeff_nonneg N p.natDegree)
  filter_upwards [lim.eventually_gt_atTop 0] with x hx
  simpa [f,Polynomial.eval_comp,d,p,AlternatesAt] using hx

theorem far_right_phase (N : ℕ) (hn : 128≤N) (L : ℝ) :
    ∃ s : Param, L<s.val-1 ∧ ((expectedDegree N-1:ℕ):ℝ)<phase s N/Real.pi ∧
      AlternatesAt (B N) (expectedDegree N) (s.val-1) := by
  have d2 : 2<expectedDegree N := by unfold expectedDegree;omega
  have ord : (3:ℕ)*(expectedDegree N-1)<2*(N-1) := by unfold expectedDegree;omega
  have realord : (expectedDegree N-1:ℕ) < ((N:ℝ)-1)*2/3 := by
    have rr : (3:ℝ)*(expectedDegree N-1:ℕ)<2*((N-1:ℕ):ℝ) := by exact_mod_cast ord
    rw [Nat.cast_sub (by omega : 1≤N),Nat.cast_one] at rr
    linarith
  let c : ℝ := (1/4:ℝ)^((3:ℝ)⁻¹)
  have cp : 0<c := Real.rpow_pos_of_pos (by norm_num) _
  have cc : c^3=1/4 := Real.rpow_inv_natCast_pow (by norm_num) (by decide)
  have cube : 4*c^3=1 := by rw [cc];norm_num
  have θ:=(far_geometry cp cube).2.2.1
  have id0 : Tendsto (fun e : ℝ => e) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have theta : Tendsto (fun e => (pointsAt (farParam e)).u.arg) (𝓝[>] 0) (𝓝 (2*Real.pi/3)) := by
    have te:=tendsto_const_nhds (x:=(2*Real.pi/3)) (f:=𝓝[>] (0:ℝ)) |>.sub (θ.mul id0)
    rw [mul_zero,sub_zero] at te
    apply te.congr'
    filter_upwards [self_mem_nhdsWithin] with e (he : 0<e)
    rw [div_mul_cancel₀ _ he.ne'];ring
  have phi : Tendsto (fun e => phase (farParam e) N/Real.pi) (𝓝[>] 0) (𝓝 (((N:ℝ)-1)*2/3)) := by
    have h:=((theta.const_mul (N:ℝ)).sub far_phase_offset).div_const Real.pi
    convert h using 1
    congr 1;field_simp [Real.pi_ne_zero];ring
  have fs : Tendsto (fun e => (farParam e).val) (𝓝[>] (0:ℝ)) atTop := by
    have h:=(tendsto_pow_atTop (α:=ℝ) (by decide : 3≠0)).comp tendsto_inv_nhdsGT_zero
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin,id0.eventually_lt_const (by norm_num : (0:ℝ)<1)] with e ep el
    exact (farParam_val ⟨ep,el⟩).symm
  have fm : Tendsto (fun e => (farParam e).val-1) (𝓝[>] (0:ℝ)) atTop := by
    apply tendsto_atTop.mpr
    intro b;filter_upwards [fs.eventually_ge_atTop (b+1)] with e he;linarith
  obtain ⟨e,le,pg,sg⟩:=((fm.eventually_gt_atTop L).and ((phi.eventually_const_lt realord).and (fm.eventually (far_sign N d2)))).exists
  exact ⟨farParam e,le,pg,sg⟩

end BigDescents132.AllRanks
