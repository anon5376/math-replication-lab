import BigDescents132.Quartic
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace BigDescents132.Branch
open Complex
open scoped ComplexConjugate

/-- Product of four distinct zeros of a quartic, without division by its
leading coefficient. Successive divided differences factor out all four roots. -/
private theorem quartic_product {K : Type*} [Field K] (a b c d k r R z w : K)
    (h : ∀ x ∈ [r,R,z,w], a*x^4+b*x^3+c*x^2+d*x+k=0)
    (hR : R≠r) (hzr : z≠r) (hZR : z≠R) (hwr : w≠r) (hwR : w≠R) (hwz : w≠z) :
    k = a*r*R*z*w := by
  let F := fun x => a*x^4+b*x^3+c*x^2+d*x+k
  let G := fun x => a*x^3+(a*r+b)*x^2+(a*r^2+b*r+c)*x+(a*r^3+b*r^2+c*r+d)
  let H := fun x => a*x^2+(a*R+a*r+b)*x+(a*R^2+(a*r+b)*R+a*r^2+b*r+c)
  let I := fun x => a*x+(a*z+a*R+a*r+b)
  have e₁ (x) : F x = (x-r)*G x := by
    have hr := h r (by simp)
    dsimp [F,G]
    linear_combination hr
  have gr : G R=0 := (mul_eq_zero.mp ((e₁ R).symm.trans (h _ (by simp)))).resolve_left (sub_ne_zero.mpr hR)
  have e₂ (x) : G x = (x-R)*H x := by dsimp [G,H] at *; linear_combination gr
  have gz : G z=0 := (mul_eq_zero.mp ((e₁ z).symm.trans (h _ (by simp)))).resolve_left (sub_ne_zero.mpr hzr)
  have hz : H z=0 := (mul_eq_zero.mp ((e₂ z).symm.trans gz)).resolve_left (sub_ne_zero.mpr hZR)
  have e₃ (x) : H x = (x-z)*I x := by dsimp [H,I] at *; linear_combination hz
  have gw : G w=0 := (mul_eq_zero.mp ((e₁ w).symm.trans (h _ (by simp)))).resolve_left (sub_ne_zero.mpr hwr)
  have hw : H w=0 := (mul_eq_zero.mp ((e₂ w).symm.trans gw)).resolve_left (sub_ne_zero.mpr hwR)
  have iw : I w=0 := (mul_eq_zero.mp ((e₃ w).symm.trans hw)).resolve_left (sub_ne_zero.mpr hwz)
  have e₄ (x) : I x = (x-w)*a := by dsimp [I] at *; linear_combination iw
  have h0 : F 0 = (-r)*((-R)*((-z)*((-w)*a))) := by rw [e₁,e₂,e₃,e₄]; simp
  simpa [F,mul_comm,mul_left_comm,mul_assoc] using h0

private theorem all_roots_product {s r R : ℝ} {z : ℂ} (hR : r<R)
    (hr₀ : (radicand s).IsRoot r) (hR₀ : (radicand s).IsRoot R)
    (hz : (radicand (s:ℂ)).IsRoot z) (him : z.im≠0) :
    1 = s^2*r*R*‖z‖^2 := by
  let q := fun x : ℂ => (s:ℂ)^2*x^4+(-4*(s:ℂ)^2)*x^3+(6*(s:ℂ))*x^2+(-4)*x+1
  have toQ (u : ℝ) (hu : (radicand s).IsRoot u) : q (u:ℂ)=0 := by
    change (radicand s).eval u=0 at hu
    simp [radicand] at hu
    dsimp [q]
    exact_mod_cast (show s^2*u^4+(-4*s^2)*u^3+6*s*u^2+(-4)*u+1=0 by linear_combination hu)
  have zq : q z=0 := by change (radicand (s:ℂ)).eval z=0 at hz; simp [radicand] at hz; dsimp [q]; linear_combination hz
  have cq : q (conj z)=0 := by
    have h := congrArg (conj:ℂ → ℂ) zq
    norm_num [q, map_ofNat] at h ⊢
    exact h
  have nr (x : ℝ) : z≠(x:ℂ) := by intro e; exact him (e ▸ Complex.ofReal_im x)
  have nc (x : ℝ) : conj z≠(x:ℂ) := by
    intro e
    have j := congrArg Complex.im e
    simp [him] at j
  have nd : conj z≠z := by intro e; have j := congrArg Complex.im e; simp at j; exact him (by linarith)
  have hv := quartic_product ((s:ℂ)^2) (-4*(s:ℂ)^2) (6*(s:ℂ)) (-4) 1 (r:ℂ) (R:ℂ) z (conj z)
    (by intro u hu; rcases List.mem_cons.mp hu with hr|hu
        · exact hr ▸ toQ r hr₀
        rcases List.mem_cons.mp hu with hR|hu
        · exact hR ▸ toQ R hR₀
        rcases List.mem_cons.mp hu with h|h
        · exact h ▸ zq
        · have := List.mem_singleton.mp h; exact this ▸ cq)
    (by exact_mod_cast hR.ne') (nr r) (nr R) (nc r) (nc R) nd
  have hzz : z*conj z=(‖z‖^2:ℝ) := by
    rw [Complex.sq_norm,Complex.normSq_eq_conj_mul_self,mul_comm]
  rw [mul_assoc _ z, hzz] at hv
  exact_mod_cast hv

private def factorP {K : Type*} [CommRing K] (s w : K) := s*w^3*(2+w)-(1+2*w)

private theorem split_factor {K : Type*} [CommRing K] (s w : K) :
    (radicand s).eval (w^2) = factorP s w * factorP s (-w) := by
  simp [radicand,factorP]
  ring

private theorem select_square {s : ℝ} {z : ℂ} (hz : (radicand (s:ℂ)).IsRoot z) :
    ∃ w : ℂ, w^2=z ∧ factorP (s:ℂ) w=0 := by
  obtain ⟨w,hw⟩ := IsAlgClosed.exists_pow_nat_eq z (by decide : 0<2)
  change (radicand (s:ℂ)).eval z=0 at hz
  rw [←hw,split_factor] at hz
  rcases mul_eq_zero.mp hz with h|h
  · exact ⟨w,hw,h⟩
  · exact ⟨-w,by simpa using hw,h⟩

private theorem positive_factor {s r : ℝ} (hs : 1<s) (hr : 0<r) (hr' : r<1)
    (hz : (radicand s).IsRoot r) :
    factorP s (Real.sqrt r)=0 := by
  let u := Real.sqrt r
  have hu : 0<u := Real.sqrt_pos.mpr hr
  have hu' : u<1 := by dsimp [u]; exact (Real.sqrt_lt' (by norm_num)).mpr (by simpa)
  have he : u^2=r := Real.sq_sqrt hr.le
  have hn : factorP s (-u)<0 := by
    have hnegative : u^4-2*u^3+2*u-1 < 0 := by
      have ht : u-1<0 := by linarith
      have hpow : (u-1)^3<0 := by rw [pow_succ]; exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero ht.ne) ht
      have hprod := mul_neg_of_neg_of_pos hpow
        (show 0<u+1 by linarith)
      linarith only [show u^4-2*u^3+2*u-1=(u-1)^3*(u+1) by ring, hprod]
    have h := mul_pos (sub_pos.mpr hs) (mul_pos (pow_pos hu 3) (show 0<2-u by linarith))
    unfold factorP
    nlinarith
  change (radicand s).eval r=0 at hz
  rw [←he,split_factor] at hz
  exact (mul_eq_zero.mp hz).resolve_right hn.ne

/-- Inside the unit circle the ratio |1+2w|/|2+w| is strictly maximized at
the positive real point of the same modulus, provided w is nonreal. -/
private theorem radial_ratio {w : ℂ} (hw : w.im≠0) (hv : ‖w‖<1) :
    ‖1+2*w‖*(2+‖w‖)<‖2+w‖*(1+2*‖w‖) := by
  have hwv : w.re < ‖w‖ := by
    apply (Complex.re_le_norm w).lt_of_ne
    intro h
    have h₁ := Complex.sq_norm w
    rw [← h,Complex.normSq_apply] at h₁
    exact hw (by nlinarith [sq_pos_of_ne_zero hw])
  have one : 0<1-‖w‖^2 := by nlinarith [norm_nonneg w, mul_pos (sub_pos.mpr hv) (show 0<1+‖w‖ by positivity)]
  have h₂ : ‖1+2*w‖^2 = 1+4*w.re+4*‖w‖^2 := by
    simp [Complex.sq_norm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
    ring
  have h₃ : ‖2+w‖^2 = 4+4*w.re+‖w‖^2 := by
    simp [Complex.sq_norm,Complex.normSq_apply]
    ring
  have diff : (‖2+w‖*(1+2*‖w‖))^2 - (‖1+2*w‖*(2+‖w‖))^2 =
      12*(1-‖w‖^2)*(‖w‖-w.re) := by rw [mul_pow,mul_pow,h₂,h₃]; ring
  have hlt : (‖1+2*w‖*(2+‖w‖))^2 < (‖2+w‖*(1+2*‖w‖))^2 := by
    linarith only [diff, mul_pos (mul_pos (by norm_num : (0:ℝ)<12) one) (sub_pos.mpr hwv)]
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hlt

private theorem ordered_magnitudes {u v s : ℝ} (hu : 0<u) (hv : 0≤v)
    (h₁ : s*u^3*(2+u)=1+2*u) (h₂ : s*v^3*(2+v)<1+2*v) : v<u := by
  by_contra! h
  have d₂ : 0≤v^2-u^2 := sub_nonneg.mpr (pow_le_pow_left₀ hu.le h 2)
  have d₃ : 0≤v^3-u^3 := sub_nonneg.mpr (pow_le_pow_left₀ hu.le h 3)
  have d₄ : 0≤v^4-u^4 := sub_nonneg.mpr (pow_le_pow_left₀ hu.le h 4)
  have diff : 0≤(1+2*u)*(v^3*(2+v))-(1+2*v)*(u^3*(2+u)) := by
    calc
      0 ≤ (v^4-u^4)+2*(v^3-u^3)+2*u*v*(v^3-u^3)+4*u*v*(v^2-u^2) := by positivity
      _ = _ := by ring
  rw [←h₁] at diff
  have hmul := mul_lt_mul_of_pos_right h₂ (show 0<u^3*(2+u) by positivity)
  linarith only [show s*u^3*(2+u)*(v^3*(2+v))=s*v^3*(2+v)*(u^3*(2+u)) by ring,diff,hmul]

/-- The complex conjugate branch points are strictly closer to the origin
than the smaller positive real branch point, for every s>1. -/
theorem dominant_pair {s r : ℝ} (hs : 1<s) (hr : r∈Set.Ioo (1/s) 1)
    (hr₀ : (radicand s).IsRoot r) {z : ℂ}
    (hz : (radicand (s:ℂ)).IsRoot z) (hnr : z.im≠0) : ‖z‖<r := by
  obtain ⟨r',hr',R,hR,hall⟩ := real_branch_points hs
  have hrR : r<R := hr.2.trans hR.1
  have hprod := all_roots_product hrR hr₀ ((hall R).mpr (Or.inr rfl)) hz hnr
  have hs0 : 0<s := by linarith
  have hr0 : 0<r := (one_div_pos.mpr hs0).trans hr.1
  have hsr : 1<s*r := by simpa [mul_comm] using (div_lt_iff₀ hs0).mp hr.1
  have hsR : 1<s*R := one_lt_mul hs.le hR.1
  have hsrR : 1<s^2*r*R := by
    calc
      1 < (s*r)*(s*R) := one_lt_mul hsr.le hsR
      _ = _ := by ring
  obtain ⟨w,hw,hfac⟩ := select_square hz
  have hzn : ‖w‖^2=‖z‖ := by rw [← norm_pow,hw]
  have hzunit : ‖z‖<1 := by
    by_contra hneg
    have hp := le_of_not_gt hneg
    have hsq : 1≤‖z‖^2 := one_le_pow₀ hp
    have hbad := lt_of_lt_of_le hsrR (le_mul_of_one_le_right (by positivity : 0≤s^2*r*R) hsq)
    linarith
  have hu : ‖w‖<1 := by nlinarith [norm_nonneg w, sq_nonneg (‖w‖-1)]
  have hi : w.im≠0 := by
    intro h
    have j := congrArg Complex.im hw
    simp [pow_two,Complex.mul_im,h] at j
    exact hnr j.symm
  have hn := radial_ratio hi hu
  have he : (s:ℂ)*w^3*(2+w)=1+2*w := sub_eq_zero.mp hfac
  have hab := congrArg norm he
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hs0.le] at hab
  rw [←hab] at hn
  have hww : 0<‖2+w‖ := by
    apply norm_pos_iff.mpr
    intro hx
    have hm := congrArg Complex.im hx
    simp [hi] at hm
  have hbound : s*‖w‖^3*(2+‖w‖)<1+2*‖w‖ := by
    apply (mul_lt_mul_iff_of_pos_right hww).mp
    linarith only [hn, show s*‖w‖^3*(2+‖w‖)*‖2+w‖=s*‖w‖^3*‖2+w‖*(2+‖w‖) by ring,
      show (1+2*‖w‖)*‖2+w‖=‖2+w‖*(1+2*‖w‖) by ring]
  have hpos : s*(Real.sqrt r)^3*(2+Real.sqrt r)=1+2*Real.sqrt r :=
    sub_eq_zero.mp (positive_factor hs hr0 hr.2 hr₀)
  have h := ordered_magnitudes (Real.sqrt_pos.mpr hr0) (norm_nonneg w) hpos hbound
  have hsqr := Real.sq_sqrt hr0.le
  nlinarith [mul_pos (sub_pos.mpr h) (show 0<Real.sqrt r+‖w‖ by positivity)]

end BigDescents132.Branch
