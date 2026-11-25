import BigDescents132.WitnessScale

namespace BigDescents132.Peak
open Filter Set Slit

private theorem choose_cutoffs (L : ℝ) :
    ∃ K : ℕ, 5≤K ∧ L<nearRadius K ∧ ∀ e : Fin 3, L<farRadius K e := by
  have c := croot_pos
  have p := Real.pi_pos
  have s : 0<Real.sqrt 3 := by positivity
  obtain ⟨k,h⟩ := exists_nat_gt (L*croot*Real.sqrt 3/(2*Real.pi))
  let K := max 5 k
  have kK : (k:ℝ)≤K := by exact_mod_cast (le_max_right 5 k)
  have H := (div_lt_iff₀ (by positivity : 0<2*Real.pi)).mp (h.trans_le kK)
  refine ⟨K,le_max_left _ _,?_,fun e => ?_⟩
  · unfold nearRadius witness
    apply (lt_div_iff₀ c).mpr
    apply (lt_div_iff₀ s).mpr
    linarith only [H,p]
  · unfold farRadius Far.witness
    rw [show 2/croot*(2*(((K+1:ℕ):ℝ)*Real.pi+(e.val:ℝ)*Real.pi/3)/Real.sqrt 3)=
      (4*(((K+1:ℕ):ℝ)*Real.pi+(e.val:ℝ)*Real.pi/3))/(croot*Real.sqrt 3) by ring]
    apply (lt_div_iff₀ (mul_pos c s)).mpr
    push_cast
    nlinarith only [H,p,mul_nonneg (Nat.cast_nonneg (α:=ℝ) K) p.le,mul_nonneg (Nat.cast_nonneg (α:=ℝ) e.val) p.le]

private theorem sample_parameters {K : ℕ} (hk : 5≤K) (j : ℕ) (e : Fin 3) {N : ℕ} (hn : 0<N) :
    (leftAt N (nearRadius K)).val-1=nearX K/(N:ℝ)^3 ∧
    (rightAt N (farRadius j e)).val-1=farX N e j := by
  have pos : 0<(N:ℝ) := Nat.cast_pos.mpr hn
  obtain ⟨a,b⟩ := radius_cubes hk j e
  constructor
  · rw [leftAt,nearParam_val (div_pos (nearRadius_pos hk) pos),add_sub_cancel_left,div_pow,a]
  · rw [rightAt,nearParam_val (div_pos pos (farRadius_pos j e)),add_sub_cancel_left,div_pow,b,farX,inv_div]; ring

/-- For each degree residue the finite endpoint sign lists and the matched
phases give a certified grid at all sufficiently large ranks in that residue. -/
theorem residue_endpoint_grids (L : ℝ) (e : Fin 3) : ∀ᶠ p : ℕ in atTop,
    Nonempty (EndpointGrid (rank p e) L) := by
  obtain ⟨K,hK,LK,LJ⟩ := choose_cutoffs L
  let a := nearRadius K
  let b := farRadius K e
  have p := Real.pi_pos
  have left := (phase_left_limit hK).eventually_lt_const
    (show (K:ℝ)*Real.pi<((K+1:ℕ):ℝ)*Real.pi by push_cast; linarith)
  have right := (phase_right_limit K e).eventually_const_lt
    (show -((K+2:ℕ):ℝ)*Real.pi< -((K+1:ℕ):ℝ)*Real.pi by push_cast; linarith)
  have top := rank_top e
  filter_upwards [top.eventually left,right,top.eventually (bounds_left_right (nearRadius_pos hK) (farRadius_pos K e) LK (LJ e)),
    top.eventually (near_grid K),top.eventually (near_sign K),far_sample_sign e K,far_grid e K,eventually_ge_atTop (2*K+2)] with m l r geom lg ls rs rg big
  let N := rank m e
  let d := 2*m+e.val
  let mid := d-(K+K+2)
  have nn : 0<N := by dsimp [N,rank]; omega
  have deg : expectedDegree N=d := by dsimp [expectedDegree,N,rank,d]; have := e.isLt; omega
  have cnt : K+(mid+1)+(K+1)=d := by dsimp [mid,d]; omega
  have cnt' : K+mid+(K+2)=d := by omega
  have sign := rs (K+mid+1) (by rw [deg]; omega)
  obtain ⟨far,g⟩ := rg
  obtain ⟨va,vb⟩ := sample_parameters hK K e nn
  have high : ((K+mid:ℕ):ℝ)*Real.pi<phase (rightAt N b) N := by
    change -((K+2:ℕ):ℝ)*Real.pi<phase (rightAt N b) N-(d:ℝ)*Real.pi at r
    have cast : ((K+mid:ℕ):ℝ)+((K+2:ℕ):ℝ)=(d:ℝ) := by exact_mod_cast cnt'
    linarith only [r,congrArg (fun x : ℝ => x*Real.pi) cast]
  exact ⟨{
    a := leftAt N a, b := rightAt N b, far := far, start := K, middle := mid, tail := K+1,
    ordered := geom.1, scale := geom.2, count_eq := cnt.trans deg.symm,
    phase_left := (div_lt_iff₀ p).mpr l, phase_right := (lt_div_iff₀ p).mpr high,
    left_grid := va.symm ▸ lg, left_sign := va.symm ▸ ls,
    right_sign := vb.symm ▸ sign, right_grid := vb.symm ▸ g }⟩

theorem all_endpoint_grids (L : ℝ) : ∀ᶠ N : ℕ in atTop, Nonempty (EndpointGrid N L) := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp (Filter.eventually_all.mpr (fun e : Fin 3 => residue_endpoint_grids L e))
  refine eventually_atTop.mpr ⟨3*M+5,fun n hn => ?_⟩
  have use (p : ℕ) (e : Fin 3) (hp : M≤p) (h : n=rank p e) := h ▸ hM p hp e
  rcases Nat.mod_lt n (by decide : 0<3) |> (fun h => show n%3=0 ∨ n%3=1 ∨ n%3=2 by omega) with h|h|h
  · exact use ((n-3)/3) 1 (by omega) (by simp [rank]; omega)
  · exact use ((n-1)/3) 0 (by omega) (by simp [rank]; omega)
  · exact use ((n-5)/3) 2 (by omega) (by simp [rank]; omega)

end BigDescents132.Peak

/-- The big-descent polynomial of literal 132-avoiding permutations at every
sufficiently large rank has exactly its expected degree in distinct,
strictly negative roots. -/
theorem BigDescents132.eventual_simple_negative : BigDescents132.EventualSimpleNegative :=
  BigDescents132.Slit.eventual_of_endpoint_grids (fun L _ => BigDescents132.Peak.all_endpoint_grids L)
