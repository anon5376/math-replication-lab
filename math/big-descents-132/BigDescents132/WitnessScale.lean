import BigDescents132.EndpointSamples

namespace BigDescents132.Peak
open Filter Set Slit
open scoped Topology

noncomputable def croot : ℝ := 4^((3:ℝ)⁻¹)
theorem croot_pos : 0<croot := Real.rpow_pos_of_pos (by norm_num) _
theorem croot_cube : croot^3=4 := Real.rpow_inv_natCast_pow (by norm_num) (by decide)

noncomputable def nearRadius (i : ℕ) := witness i/croot
noncomputable def farRadius (j : ℕ) (e : Fin 3) := (2/croot)*Far.witness (j+1) e.val

theorem nearRadius_pos {i : ℕ} (hi : 5≤ i) : 0<nearRadius i :=
  div_pos ((by norm_num : (0:ℝ)<20).trans_le (witness_ge hi)) croot_pos

theorem farRadius_pos (j : ℕ) (e : Fin 3) : 0<farRadius j e := by
  have := croot_pos
  unfold farRadius Far.witness
  positivity

theorem radius_cubes {i : ℕ} (hi : 5≤ i) (j : ℕ) (e : Fin 3) :
    (nearRadius i)^3=nearX i ∧ (farRadius j e)^3= -sample e j := by
  constructor
  · rw [nearX_high hi,nearRadius,div_pow,croot_cube]
  · rw [farRadius,mul_pow,div_pow,croot_cube,sample]; ring

noncomputable def leftAt (N : ℕ) (a : ℝ) := nearParam (a/(N:ℝ))
noncomputable def rightAt (N : ℕ) (b : ℝ) := nearParam ((N:ℝ)/b)

private theorem invRank : Tendsto (fun N : ℕ => (N:ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

theorem left_coord {a : ℝ} (ap : 0<a) :
    Tendsto (fun N : ℕ => a/(N:ℝ)) atTop (𝓝[>] 0) ∧
    Tendsto (fun N : ℕ => (N:ℝ)*(a/(N:ℝ))) atTop (𝓝 a) := by
  constructor
  · rw [tendsto_nhdsWithin_iff]
    refine ⟨by simpa [div_eq_mul_inv] using invRank.const_mul a,?_⟩
    filter_upwards [eventually_gt_atTop (0:ℕ)] with N n
    exact div_pos ap (Nat.cast_pos.mpr n)
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0:ℕ)] with N n
    field_simp [Nat.cast_ne_zero.mpr n.ne']

theorem right_coord {b : ℝ} (bp : 0<b) :
    Tendsto (fun N : ℕ => farScale (rightAt N b)) atTop (𝓝[>] 0) ∧
    Tendsto (fun N : ℕ => (N:ℝ)*farScale (rightAt N b)) atTop (𝓝 b) := by
  have L := (left_coord bp).1.mono_right nhdsWithin_le_nhds
  have cub : Tendsto (fun N : ℕ => ((N:ℝ)*farScale (rightAt N b))^3) atTop (𝓝 (b^3)) := by
    have v := (tendsto_const_nhds (x:=b^3)).div ((tendsto_const_nhds (x:=(1:ℝ))).add (L.pow 3)) (by norm_num)
    simp only [zero_pow (by decide : 3≠0),add_zero,div_one] at v
    apply v.congr'
    filter_upwards [eventually_gt_atTop (0:ℕ)] with N n
    have np : (0:ℝ)<N := Nat.cast_pos.mpr n
    have e := (scales (rightAt N b)).2.2.2.2.1
    rw [mul_pow,e,rightAt,nearParam_val (div_pos np bp)]
    have h1 : 1+(b/(N:ℝ))^3≠0 := by positivity
    have h2 : 1+((N:ℝ)/b)^3≠0 := by positivity
    field_simp [np.ne',bp.ne',h1,h2]; ring
  have C := (Real.continuous_rpow_const (by norm_num : 0≤(3:ℝ)⁻¹)).continuousAt.tendsto.comp cub
  rw [show (b^3)^((3:ℝ)⁻¹)=b from Real.pow_rpow_inv_natCast bp.le (by decide)] at C
  have scale : Tendsto (fun N : ℕ => (N:ℝ)*farScale (rightAt N b)) atTop (𝓝 b) :=
    C.congr' (Eventually.of_forall fun N => Real.pow_rpow_inv_natCast (mul_nonneg (Nat.cast_nonneg _) (scales _).2.1.le) (by decide))
  refine ⟨tendsto_nhdsWithin_iff.mpr ⟨?_,Eventually.of_forall fun N => (scales (rightAt N b)).2.1⟩,scale⟩
  have z := scale.mul invRank
  rw [mul_zero] at z
  apply z.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N n
  field_simp [Nat.cast_ne_zero.mpr n.ne']

theorem rank_top (e : Fin 3) : Tendsto (fun p : ℕ => rank p e) atTop atTop :=
  tendsto_atTop_mono (fun p => show p≤rank p e by dsimp [rank]; omega) tendsto_id

theorem phase_left_limit {K : ℕ} (hk : 5≤K) :
    Tendsto (fun N : ℕ => phase (leftAt N (nearRadius K)) N) atTop (𝓝 ((K:ℝ)*Real.pi)) := by
  obtain ⟨a,b⟩ := left_coord (nearRadius_pos hk)
  have H := small_phase_match croot_pos croot_cube a b
  convert H using 2
  dsimp [nearRadius,witness]
  field_simp [croot_pos.ne']; ring

theorem phase_right_limit (j : ℕ) (e : Fin 3) :
    let B := farRadius j e
    Tendsto (fun p : ℕ => phase (rightAt (rank p e) B) (rank p e)-((2*p+e.val:ℕ):ℝ)*Real.pi)
      atTop (𝓝 (-((j+1:ℕ):ℝ)*Real.pi)) := by
  let b := farRadius j e
  have rp := farRadius_pos j e
  obtain ⟨t,h⟩ := right_coord rp
  have c := croot_pos
  have ci : 0<croot⁻¹ := inv_pos.mpr c
  have sc : 4*(croot⁻¹)^3=1 := by rw [inv_pow,croot_cube]; norm_num
  have H := (far_phase_match ci sc t h).comp (rank_top e)
  have K := H.add_const ((2+(e:ℝ))*Real.pi/3)
  have eq (p : ℕ) : (rank p e:ℝ)*(2*Real.pi/3)=((2*p+e.val:ℕ):ℝ)*Real.pi+(2+(e:ℝ))*Real.pi/3 := by dsimp [rank]; push_cast; ring
  convert K.congr' (Eventually.of_forall fun p => show _=phase (rightAt (rank p e) b) (rank p e)-((2*p+e.val:ℕ):ℝ)*Real.pi from by
    dsimp only [Function.comp_apply]
    rw [(scales (rightAt (rank p e) b)).2.2.2.2.2.2,eq]
    ring) using 2
  unfold farRadius Far.witness
  push_cast
  field_simp [c.ne']; ring

theorem bounds_left_right {a b L : ℝ} (ap : 0<a) (bp : 0<b) (al : L<a) (bl : L<b) :
    ∀ᶠ N : ℕ in atTop, (leftAt N a).val<(rightAt N b).val ∧
      L<(N:ℝ)*min (smallScale (leftAt N a)) (farScale (rightAt N b)) := by
  have left := (left_coord ap).1.mono_right nhdsWithin_le_nhds
  have lt := left.eventually_lt_const zero_lt_one
  have top : Tendsto (fun N : ℕ => (N:ℝ)/b) atTop atTop := by
    simpa [div_eq_mul_inv,mul_comm] using tendsto_natCast_atTop_atTop.const_mul_atTop (inv_pos.mpr bp)
  have e := (right_coord bp).2.eventually_const_lt bl
  filter_upwards [lt,top.eventually_gt_atTop 1,e,eventually_gt_atTop (0:ℕ)] with N l r big n
  have np : (0:ℝ)<N := Nat.cast_pos.mpr n
  have pp := div_pos ap np
  have ps := div_pos np bp
  have ll := nearParam_val pp
  have rr := nearParam_val ps
  have ss := (scales (leftAt N a)).2.2.2.1
  change (smallScale (leftAt N a))^3=(nearParam (a/(N:ℝ))).val-1 at ss
  rw [ll,add_sub_cancel_left] at ss
  have same := (Odd.strictMono_pow (by decide : Odd 3)).injective ss
  refine ⟨?_,?_⟩
  · change (nearParam _).val<(nearParam _).val
    rw [ll,rr]
    exact add_lt_add_left (Odd.strictMono_pow (by decide : Odd 3) (l.trans r)) 1
  · rw [mul_min_of_nonneg _ _ np.le,lt_min_iff,same]
    refine ⟨?_,big⟩
    rwa [show (N:ℝ)*(a/(N:ℝ))=a by field_simp [np.ne']]

end BigDescents132.Peak
