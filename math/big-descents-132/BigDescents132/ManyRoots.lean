import BigDescents132.FarScaling
import BigDescents132.RootCount

namespace BigDescents132
open Filter Polynomial Real
open scoped Topology

theorem reverse_at_inverse (f : Polynomial ℝ) {x : ℝ} (hx : x≠0) :
    f.eval (x⁻¹)=f.reverse.eval x * (x⁻¹)^f.natDegree := by
  letI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx)
  simpa only [invOf_eq_inv,inv_inv] using
    (Polynomial.eval₂_reverse_mul_pow (RingHom.id ℝ) (x⁻¹) f).symm

theorem Grid.invert {f : Polynomial ℝ} {a b : ℝ} {k : ℕ} (h : Grid f.reverse a b k)
    (ha : a<0) : Grid f b⁻¹ a⁻¹ k := by
  induction h with
  | nil a => exact Grid.nil _
  | @cons a b c k hab hs _ ih =>
    have hb := hab.trans ha
    have hpos : 0<(b⁻¹*a⁻¹)^f.natDegree := pow_pos (mul_pos_of_neg_of_neg (inv_lt_zero.mpr hb) (inv_lt_zero.mpr ha)) _
    have he : f.eval b⁻¹*f.eval a⁻¹ = (f.reverse.eval a*f.reverse.eval b)*(b⁻¹*a⁻¹)^f.natDegree := by
      rw [reverse_at_inverse _ hb.ne,reverse_at_inverse _ ha.ne,mul_pow]
      ring
    exact (ih hb).append (Grid.cons ((inv_lt_inv_of_neg ha hb).mpr hab)
      (he ▸ mul_neg_of_neg_of_pos hs hpos) (Grid.nil _))

def rank (p : ℕ) (e : Fin 3) := 3*p+2*e.val+1

noncomputable def sample (e : Fin 3) (j : ℕ) : ℝ :=
  -2*(Far.witness (j+1) e.val)^3

theorem sample_neg (e : Fin 3) (j : ℕ) : sample e j<0 := by
  have h : 0<Far.witness (j+1) e.val := by
    unfold Far.witness; positivity
  unfold sample
  exact mul_neg_of_neg_of_pos (by norm_num) (pow_pos h _)

theorem sample_lt (e : Fin 3) (j : ℕ) : sample e (j+1)<sample e j := by
  have h : Far.witness (j+1) e.val < Far.witness (j+1+1) e.val := by
    unfold Far.witness
    gcongr
    exact_mod_cast (Nat.lt_succ_self j)
  exact mul_lt_mul_of_neg_left (Odd.strictMono_pow (by decide : Odd 3) h) (by norm_num)

theorem leading_pos (p : ℕ) (e : Fin 3) : 0<(B (rank p e)).coeff (2*p+e.val) := by
  have hd : (B (rank p e)).natDegree=2*p+e.val := by
    rw [degree_all]; unfold rank expectedDegree; have := e.isLt; omega
  have hn : B (rank p e)≠0 := by
    intro hz
    have he := (constant_terms (3*p+2*e.val)).1
    change (B (rank p e)).eval 0 = _ at he
    rw [hz,eval_zero] at he
    norm_num at he
    linarith
  have h := (B_coeff_nonneg (rank p e) (2*p+e.val)).lt_of_ne
  apply h
  rw [←hd,coeff_natDegree]
  exact (leadingCoeff_ne_zero.mpr hn).symm

theorem signs (e : Fin 3) (j : ℕ) : ∀ᶠ p : ℕ in atTop, 0<(-1:ℝ)^(j+1)*
    (B (rank p e)).reverse.eval (sample e j/(rank p e:ℝ)^3) := by
  have h := ((Series.far_endpoint_limit e (sample e j)).const_mul ((-1:ℝ)^(j+1))).eventually_const_lt
    (Far.farLimit_witness e (Nat.zero_lt_succ j))
  filter_upwards [h] with p hp
  have hL := leading_pos p e
  apply (div_pos_iff_of_pos_right hL).mp
  simpa only [mul_div_assoc,rank] using hp

theorem grids (e : Fin 3) (K : ℕ) : ∀ᶠ p : ℕ in atTop,
    Grid (B (rank p e)).reverse (sample e 0/(rank p e:ℝ)^3) (sample e K/(rank p e:ℝ)^3) K := by
  induction K with
  | zero => exact Eventually.of_forall fun _ => Grid.nil _
  | succ K ih =>
    filter_upwards [ih,signs e K,signs e (K+1)] with p grid h₁ h₂
    have hr : 0<(rank p e:ℝ)^3 := by dsimp [rank]; positivity
    have hlt := (div_lt_div_iff_of_pos_right hr).mpr (sample_lt e K)
    have hmul := mul_pos h₁ h₂
    let u := (B (rank p e)).reverse.eval (sample e K/(rank p e:ℝ)^3)
    let v := (B (rank p e)).reverse.eval (sample e (K+1)/(rank p e:ℝ)^3)
    change 0<((-1:ℝ)^(K+1)*u)*((-1)^(K+1+1)*v) at hmul
    have sq : ((-1:ℝ)^(K+1))^2=1 := by rw [←pow_mul,mul_comm (K+1) 2,pow_mul]; norm_num
    rw [pow_succ (-1:ℝ) (K+1)] at hmul
    have hneg : u*v<0 := by
      have e' : ((-1:ℝ)^(K+1)*u)*((-1)^(K+1)*(-1)*v) = -(((-1:ℝ)^(K+1))^2*(u*v)) := by ring
      rw [e',sq,one_mul] at hmul
      linarith
    exact grid.append (Grid.cons hlt hneg (Grid.nil _))

private theorem residue_roots (e : Fin 3) (K : ℕ) (T : ℝ) : ∀ᶠ p : ℕ in atTop,
    ∃ s : Finset ℝ, s.card=K ∧ ∀ x∈s, x< T ∧ x<0 ∧ (B (rank p e)).IsRoot x := by
  have cneg := sample_neg e K
  obtain ⟨M,hM⟩ := exists_nat_gt (|T| * |sample e K|+1)
  filter_upwards [grids e K,eventually_ge_atTop M] with p g hp
  have hNp : (p:ℝ)≤(rank p e:ℝ) := by exact_mod_cast (show p≤rank p e by dsimp [rank]; omega)
  have hN : (1:ℝ)≤rank p e := by exact_mod_cast (show 1≤rank p e by dsimp [rank]; omega)
  have hr : 0<(rank p e:ℝ)^3 := by positivity
  have hr' : (rank p e:ℝ)≤(rank p e:ℝ)^3 := by simpa using pow_le_pow_right₀ hN (by decide : 1≤3)
  have hT : T*sample e K < (rank p e:ℝ)^3 := by
    have hh := (le_abs_self (T*sample e K)).trans_eq (abs_mul _ _)
    have hm' : (M:ℝ)≤p := by exact_mod_cast hp
    linarith
  have hu := div_neg_of_neg_of_pos (sample_neg e 0) hr
  obtain ⟨s,hs,hw⟩ := (g.invert hu).rootsBelow
  have hi : (sample e K/(rank p e:ℝ)^3)⁻¹ < T := by rw [inv_div]; exact (div_lt_iff_of_neg cneg).mpr hT
  have hj : (sample e K/(rank p e:ℝ)^3)⁻¹ < 0 := inv_lt_zero.mpr (div_neg_of_neg_of_pos cneg hr)
  exact ⟨s,hs,fun x hx => ⟨(hw x hx).1.trans hi,(hw x hx).1.trans hj,(hw x hx).2⟩⟩

/-- For any prescribed number and any real cutoff, every sufficiently large
rank has that many distinct negative roots below the cutoff. -/
theorem eventually_many_negative_roots (K : ℕ) (T : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∃ s : Finset ℝ, s.card=K ∧ ∀ x∈s, x<T ∧ x<0 ∧ (B n).IsRoot x := by
  obtain ⟨M,hM⟩ := eventually_atTop.mp (Filter.eventually_all.mpr (fun e : Fin 3 => residue_roots e K T))
  refine eventually_atTop.mpr ⟨3*M+5,fun n hn => ?_⟩
  have use (p : ℕ) (e : Fin 3) (hp : M≤p) (h : n=rank p e) := h ▸ hM p hp e
  rcases Nat.mod_lt n (by decide : 0<3) |> (fun h => show n%3=0 ∨ n%3=1 ∨ n%3=2 by omega) with h|h|h
  · exact use ((n-3)/3) 1 (by omega) (by simp [rank]; omega)
  · exact use ((n-1)/3) 0 (by omega) (by simp [rank]; omega)
  · exact use ((n-5)/3) 2 (by omega) (by simp [rank]; omega)

end BigDescents132
