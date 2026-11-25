import BigDescents132.PeakSigns
import BigDescents132.EndpointGrid
import BigDescents132.ManyRoots

namespace BigDescents132.Peak
open Filter Set Polynomial
open scoped Topology

noncomputable def nearX : ℕ → ℝ
  | 0 => 0 | 1 => 74 | 2 => 271 | 3 => 672 | 4 => 1348
  | i+5 => (witness (i+5))^3/4

theorem nearX_high {i : ℕ} (hi : 5≤ i) : nearX i=(witness i)^3/4 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [add_comm]; rfl

theorem witness_mono : StrictMono witness := by
  intro i j ij
  unfold witness
  gcongr

theorem nearX_mono : StrictMono nearX := by
  apply strictMono_nat_of_lt_succ; intro i
  by_cases h : i<4
  · interval_cases i <;> norm_num [nearX]
  by_cases i4 : i=4
  · subst i
    change (1348:ℝ)<witness 5^3/4
    have v := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤20) (witness_ge (le_refl 5)) 3
    norm_num at v; linarith
  rw [nearX_high (by omega : 5≤ i),nearX_high (by omega : 5≤ i+1)]
  exact (div_lt_div_iff_of_pos_right (by norm_num)).mpr ((Odd.strictMono_pow (by decide : Odd 3)) (witness_mono (Nat.lt_succ_self i)))

theorem nearX_sign (i : ℕ) : 0<(-1:ℝ)^i*smallLimit (-(nearX i)) := by
  by_cases h : 5≤ i
  · simpa only [nearX_high h,neg_div] using witness_sign h
  obtain ⟨h1,h2,h3,h4⟩ := smallEdge_first_four
  have hh : i≤4 := by omega
  interval_cases i
  · simp [nearX,smallLimit_zero]
  · simpa [nearX,←smallLimit_neg_nat] using h1
  · simpa [nearX,←smallLimit_neg_nat] using h2
  · norm_num [nearX,←smallLimit_neg_nat] at h3 ⊢; exact h3
  · norm_num [nearX,←smallLimit_neg_nat] at h4 ⊢; exact h4

theorem near_sign (i : ℕ) : ∀ᶠ N : ℕ in atTop, AlternatesAt (B N) i (nearX i/(N:ℝ)^3) := by
  have H := ((small_endpoint_limit (-(nearX i))).const_mul ((-1:ℝ)^i)).eventually_const_lt (nearX_sign i)
  filter_upwards [H,eventually_gt_atTop (0:ℕ)] with N h n
  apply (div_pos_iff_of_pos_right (Nat.cast_pos.mpr n : (0:ℝ)<N)).mp
  simpa only [AlternatesAt,neg_div,mul_div_assoc] using h

private theorem change_sign {f : ℝ[X]} {k : ℕ} {x y : ℝ} (hx : AlternatesAt f k x) (hy : AlternatesAt f (k+1) y) :
    f.eval (-x)*f.eval (-y)<0 := by
  have h := mul_pos hx hy
  have sq : ((-1:ℝ)^k)^2=1 := by rw [←pow_mul,mul_comm k 2,pow_mul]; norm_num
  unfold AlternatesAt at hx hy
  change 0<((-1:ℝ)^k*f.eval (-x))*((-1:ℝ)^(k+1)*f.eval (-y)) at h
  rw [pow_succ,show ((-1:ℝ)^k*f.eval (-x))*((-1)^k*(-1)*f.eval (-y))= -(((-1)^k)^2*(f.eval (-x)*f.eval (-y))) by ring,sq,one_mul] at h
  exact neg_pos.mp h

theorem near_grid (K : ℕ) : ∀ᶠ N : ℕ in atTop, Grid (B N) 0 (-(nearX K/(N:ℝ)^3)) K := by
  induction K with
  | zero => exact Eventually.of_forall fun N => by simpa [nearX] using (Grid.nil (p:=B N) 0)
  | succ k ih =>
    filter_upwards [ih,near_sign k,near_sign (k+1),eventually_gt_atTop (0:ℕ)] with N grid a b N0
    have pos : (0:ℝ)<N := by exact_mod_cast N0
    exact grid.append (Grid.cons (neg_lt_neg ((div_lt_div_iff_of_pos_right (pow_pos pos 3)).mpr
      (nearX_mono (Nat.lt_succ_self k)))) (change_sign a b) (Grid.nil _))

noncomputable def farX (N : ℕ) (e : Fin 3) (j : ℕ) := -(sample e j/(N:ℝ)^3)⁻¹

theorem far_sample_sign (e : Fin 3) (j : ℕ) :
    ∀ᶠ p : ℕ in atTop, ∀ k : ℕ, k+(j+1)=expectedDegree (rank p e) →
      AlternatesAt (B (rank p e)) k (farX (rank p e) e j) := by
  filter_upwards [signs e j] with p h k count
  let N := rank p e
  let y := sample e j/(N:ℝ)^3
  have np : 0<(N:ℝ) := by dsimp [N,rank]; positivity
  have yn : y<0 := div_neg_of_neg_of_pos (sample_neg e j) (pow_pos np _)
  have hd : (B N).natDegree=k+(j+1) := (degree_all _).trans count.symm
  have q : 0< -y⁻¹ := neg_pos.mpr (inv_lt_zero.mpr yn)
  have sq : ((-1:ℝ)^k)^2=1 := by rw [←pow_mul,mul_comm k 2,pow_mul]; norm_num
  have rhs := mul_pos h (pow_pos q (k+(j+1)))
  change 0<(-1:ℝ)^k*(B N).eval (- -y⁻¹)
  rw [neg_neg,reverse_at_inverse _ yn.ne,hd,show y⁻¹=(-1)*(-y⁻¹) by ring,mul_pow,pow_add (-1:ℝ)]
  change 0<(-1:ℝ)^(j+1)*(B N).reverse.eval y*(-y⁻¹)^(k+(j+1)) at rhs
  convert rhs using 1
  linear_combination ((-1:ℝ)^(j+1)*(B N).reverse.eval y*(-y⁻¹)^(k+(j+1)))*sq

theorem far_grid (e : Fin 3) (j : ℕ) : ∀ᶠ p : ℕ in atTop,
    ∃ z : ℝ, Grid (B (rank p e)) (-(farX (rank p e) e j)) z (j+1) := by
  filter_upwards [grids e j,signs e 0] with p g first
  let N := rank p e
  let f := B N
  let y := sample e 0/(N:ℝ)^3
  have np : 0<(N:ℝ) := by dsimp [N,rank]; positivity
  have yn : y<0 := div_neg_of_neg_of_pos (sample_neg e 0) (pow_pos np _)
  have deg : f.natDegree=2*p+e.val := by rw [degree_all]; dsimp [N,rank,expectedDegree]; have := e.isLt; omega
  have coeff : 0<f.reverse.eval 0 := by rw [←coeff_zero_eq_eval_zero,coeff_zero_reverse,←coeff_natDegree,deg]; exact leading_pos p e
  have pos : ∀ᶠ x : ℝ in 𝓝[<] 0, 0<f.reverse.eval x :=
    (f.reverse.continuous.continuousAt (x:=0)).continuousWithinAt.tendsto.eventually_const_lt coeff
  have ev : ∀ᶠ x : ℝ in 𝓝[<] 0, y<x := nhdsWithin_le_nhds (Ioi_mem_nhds yn)
  have neg : ∀ᶠ x : ℝ in 𝓝[<] 0, x<0 := self_mem_nhdsWithin
  obtain ⟨x,hx,x0,yx⟩ := (pos.and (neg.and ev)).exists
  have first' : f.reverse.eval y<0 := by simpa [f,y,N] using first
  have G : Grid f.reverse x (sample e j/(N:ℝ)^3) (j+1) := by
    simpa only [Nat.add_comm 1 j] using Grid.cons yx (mul_neg_of_pos_of_neg hx first') g
  refine ⟨x⁻¹,?_⟩
  simpa [farX] using G.invert x0

end BigDescents132.Peak
