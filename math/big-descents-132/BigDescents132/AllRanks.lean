import BigDescents132.EndpointSigns
import BigDescents132.AllRankUniform
import BigDescents132.AllRankInterval
import BigDescents132.AllRankFar
import BigDescents132.EndpointGrid
import BigDescents132.Through127

namespace BigDescents132
open Slit Set AllRanks

/-- The explicit endpoint grid and four uniform contour bounds give every required
phase crossing, starting at rank 128. -/
theorem all_large_simple_negative (n : ℕ) (hn : 128≤n+1) :
    (B (n+1)).natDegree=expectedDegree (n+1) ∧ SimpleNegative (B (n+1)) := by
  let N:=n+1
  let d:=expectedDegree N
  have d7 : 7≤d := by dsimp [d,N,expectedDegree];omega
  obtain ⟨a,la,pa⟩:=left_phase_bound N hn
  obtain ⟨b,ab,pb,sb⟩:=far_right_phase N hn (a.val-1)
  obtain ⟨grid,six⟩:=six_endpoint_grid N hn
  rw [←la] at grid six
  let norm:=fun x => 2*‖(pointsAt (atMagnitude x)).complexWeight N‖*Cut.moment N 0
  have right_index : 6+(d-7)+1=d := by omega
  have prev : 6+(d-7)=d-1 := by omega
  apply PhaseCertificate.sound
  refine {
    left:=a.val-1, right:=b.val-1, far:= -(b.val-1), start:=6, interior:=d-7, tail:=0,
    phase:=fun x => phase (atMagnitude x) N/Real.pi,
    degree_le:=(degree_all _).le, count_eq:=by change 6+(d-7+1)+0=d;omega,
    ordered:=ab, continuous:=phase_on N a b,
    below_first:=by simpa only [at_parameter] using pa,
    above_last:=by rw [prev,at_parameter];exact pb,
    left_grid:=grid, left_sign:=six,
    right_sign:=by rw [right_index];exact sb,
    normalizer:=norm, normalizer_pos:=fun x _ => (pointsAt (atMagnitude x)).normalizer_pos n,
    middle_error:=?_,right_grid:=Grid.nil _ }
  intro x hx
  have xp : 0<x := (sub_pos.mpr a.property).trans hx.1
  let s:=atMagnitude x
  have sx : s.val=1+x := val_magnitude xp
  obtain ⟨p,hp,hs⟩:=parameter_onto s
  have sv : (coordinate p hp).sVal=s.val := congrArg Subtype.val hs
  have bound : 3800/(N:ℝ)^3 ≤ (coordinate p hp).sVal-1 := by rw [sv,sx,←la];linarith only [hx.1]
  have move:=moving_parameter hp N hn bound
  have err:=four_ranges hp n hn move
  rw [hs] at err
  change |(B N).eval (-x)/(2*‖(pointsAt s).complexWeight N‖*Cut.moment N 0)-Real.cos (phase s N/Real.pi*Real.pi)|<1
  rw [div_mul_cancel₀ _ Real.pi_ne_zero,show Real.cos (phase s N)=Real.cos ((pointsAt s).complexWeight N).arg from (pointsAt s).cos_phase N]
  change |(B N).eval (1-s.val)/_ - _| < 1 at err
  rwa [show 1-s.val = -x by rw [sx];ring] at err

/-- Every literal 132-avoider big-descent polynomial splits over the reals and
has exactly its degree many distinct, strictly negative roots. -/
theorem all_ranks_simple_negative (n : ℕ) :
    (B n).natDegree=expectedDegree n ∧ SimpleNegative (B n) := by
  by_cases small : n≤127
  · exact finite127_simple_negative n small
  · obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (show n≠0 by omega)
    exact all_large_simple_negative k (by omega)

end BigDescents132
