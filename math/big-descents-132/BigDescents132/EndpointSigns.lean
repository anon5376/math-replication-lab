import BigDescents132.EndpointSign3800
import BigDescents132.Phase

namespace BigDescents132.AllRanks

/-- Six ordered, disjoint sign-change intervals adjacent to zero for every rank from 128. -/
theorem six_endpoint_grid (N : ℕ) (hN : 128≤N) :
    Grid (B N) 0 (-(3800/(N:ℝ)^3)) 6 ∧ AlternatesAt (B N) 6 (3800/(N:ℝ)^3) := by
  have pos : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  let atR:=fun (r : ℕ) => -(r:ℝ)/(N:ℝ)^3
  have ord (a b : ℕ) (h : a<b) : atR b<atR a := by
    exact div_lt_div_of_pos_right (neg_lt_neg (by exact_mod_cast h)) (pow_pos pos _)
  have a0 : atR 0=0 := by simp [atR]
  have h0 : 0<(B N).eval (atR 0) := by
    obtain ⟨n,eq⟩:=Nat.exists_eq_succ_of_ne_zero (show N≠0 by omega)
    rw [a0,eq,(constant_terms n).1];positivity
  have e1 : (B N).eval (atR 74)<0:=endpoint74 N hN
  have e2 : 0<(B N).eval (atR 271):=endpoint271 N hN
  have e3 : (B N).eval (atR 672)<0:=endpoint672 N hN
  have e4 : 0<(B N).eval (atR 1348):=endpoint1348 N hN
  have e5 : (B N).eval (atR 2370)<0:=endpoint2370 N hN
  have e6 : 0<(B N).eval (atR 3800):=endpoint3800 N hN
  have endpt : -(3800/(N:ℝ)^3)=atR 3800 := by dsimp [atR];ring
  constructor
  · rw [endpt,←a0]
    exact Grid.cons (ord 0 74 (by decide)) (mul_neg_of_pos_of_neg h0 e1)
      (Grid.cons (ord 74 271 (by decide)) (mul_neg_of_neg_of_pos e1 e2)
      (Grid.cons (ord 271 672 (by decide)) (mul_neg_of_pos_of_neg e2 e3)
      (Grid.cons (ord 672 1348 (by decide)) (mul_neg_of_neg_of_pos e3 e4)
      (Grid.cons (ord 1348 2370 (by decide)) (mul_neg_of_pos_of_neg e4 e5)
      (Grid.cons (ord 2370 3800 (by decide)) (mul_neg_of_neg_of_pos e5 e6) (Grid.nil _))))))
  · unfold AlternatesAt
    rw [endpt];norm_num;exact e6

end BigDescents132.AllRanks
