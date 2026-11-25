import BigDescents132.PhaseEnds

namespace BigDescents132.Slit
open Filter Set

/-- Only the two endpoint samples and their finite sign grids are data.
The continuity, degree, positive normalization and error on their entire
intervening interval are supplied by the proved interior theorem. -/
structure EndpointGrid (N : ℕ) (L : ℝ) where
  a : Param
  b : Param
  far : ℝ
  start : ℕ
  middle : ℕ
  tail : ℕ
  ordered : a.val<b.val
  scale : L<(N:ℝ)*min (smallScale a) (farScale b)
  count_eq : start+(middle+1)+tail=expectedDegree N
  phase_left : phase a N/Real.pi<((start+1:ℕ):ℝ)
  phase_right : ((start+middle:ℕ):ℝ)<phase b N/Real.pi
  left_grid : Grid (B N) 0 (-(a.val-1)) start
  left_sign : AlternatesAt (B N) start (a.val-1)
  right_sign : AlternatesAt (B N) (start+middle+1) (b.val-1)
  right_grid : Grid (B N) (-(b.val-1)) far tail

private noncomputable def atMagnitude (x : ℝ) : Param := parameter (1+x)
private theorem val_magnitude {x : ℝ} (hx : 0<x) : (atMagnitude x).val=1+x := by
  simp only [atMagnitude,parameter,dif_pos (lt_add_of_pos_right _ hx)]
private theorem at_parameter (p : Param) : atMagnitude (p.val-1)=p := by
  exact Subtype.ext (by rw [val_magnitude (sub_pos.mpr p.property)]; ring)

private theorem phase_on (N : ℕ) (a b : Param) :
    ContinuousOn (fun x => phase (atMagnitude x) N/Real.pi) (Icc (a.val-1) (b.val-1)) := by
  rw [continuousOn_iff_continuous_restrict]
  let f : Icc (a.val-1) (b.val-1) → Param := fun x => ⟨1+x.val,
    lt_add_of_pos_right 1 ((sub_pos.mpr a.property).trans_le x.property.1)⟩
  have fc : Continuous f := Continuous.subtype_mk (continuous_const.add continuous_subtype_val) _
  apply (((phase_continuous N).comp fc).div_const Real.pi).congr
  intro x
  have h : atMagnitude x.val=f x := Subtype.ext (val_magnitude ((sub_pos.mpr a.property).trans_le x.property.1))
  simp [Set.restrict,h,Function.comp_def]

/-- For the literal polynomial only the endpoint grids and matching bounds
remain to be supplied at a rank. There is a single threshold independent
of that rank and both endpoints. -/
theorem certificate_of_endpoint_grid :
    ∃ L : ℝ, 0<L ∧ ∀ n : ℕ, 8≤n+1 → EndpointGrid (n+1) L →
      Nonempty (PhaseCertificate (B (n+1)) (expectedDegree (n+1))) := by
  obtain ⟨C,c0,bd⟩ := uniform_moving_interior
  let L := max 7 C
  have l0 : 0<L := (by norm_num : (0:ℝ)<7).trans_le (le_max_left _ _)
  refine ⟨L,l0,fun n hn w => ?_⟩
  let N := n+1
  let normalizer := fun x => 2*‖(pointsAt (atMagnitude x)).complexWeight N‖*Cut.moment N 0
  refine ⟨{
    left := w.a.val-1, right := w.b.val-1, far := w.far, start := w.start,
    interior := w.middle, tail := w.tail, phase := fun x => phase (atMagnitude x) N/Real.pi,
    degree_le := (degree_all _).le, count_eq := w.count_eq,
    ordered := sub_lt_sub_right w.ordered 1, continuous := phase_on N w.a w.b,
    below_first := by simpa only [at_parameter] using w.phase_left,
    above_last := by simpa only [at_parameter] using w.phase_right,
    left_grid := w.left_grid, left_sign := w.left_sign, right_sign := w.right_sign,
    normalizer := normalizer, normalizer_pos := fun x _ => (pointsAt (atMagnitude x)).normalizer_pos n,
    middle_error := ?_, right_grid := w.right_grid }⟩
  intro x hx
  let p := atMagnitude x
  let g := pointsAt p
  have xp : 0<x := (sub_pos.mpr w.a.property).trans hx.1
  have pe : p.val=1+x := val_magnitude xp
  have large := interval_scale (a:=w.a) (p:=p) (b:=w.b)
    (by rw [pe]; linarith [hx.1]) (by rw [pe]; linarith [hx.2])
  have NE : L<(N:ℝ)*edgeScale p := w.scale.trans_le (mul_le_mul_of_nonneg_left large (Nat.cast_nonneg _))
  have tol := (bd p n hn ((le_max_left _ _).trans NE.le)).trans_lt
    ((div_lt_one (l0.trans NE)).mpr ((le_max_right _ _).trans_lt NE))
  change |(B N).eval (-x)/normalizer x-Real.cos (phase p N/Real.pi*Real.pi)|<1
  rw [div_mul_cancel₀ _ Real.pi_ne_zero,show Real.cos (phase p N)=_ from g.cos_phase N]
  have ev : 1-p.val= -x := by rw [pe]; ring
  simpa only [coefficientError,ev] using tol

/-- An endpoint-grid criterion for the literal permutation polynomial.
The construction of these grids is in `BigDescents132.Eventual`. -/
theorem eventual_of_endpoint_grids
    (ends : ∀ L : ℝ, 0<L → ∀ᶠ N : ℕ in atTop, Nonempty (EndpointGrid N L)) :
    EventualSimpleNegative := by
  obtain ⟨L,lpos,cert⟩ := certificate_of_endpoint_grid
  obtain ⟨K,grid⟩ := eventually_atTop.mp (ends L lpos)
  refine ⟨max K 8,fun N hn => ?_⟩
  have hK := (le_max_left _ _).trans hn
  have hN := (le_max_right _ _).trans hn
  cases N with
  | zero => omega
  | succ n => exact (grid (n+1) hK).elim fun e => (cert n hN e).elim fun c => c.sound

end BigDescents132.Slit
