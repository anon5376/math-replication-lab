import BigDescents132.Traces

namespace BigDescents132.Slit
open Complex Filter Set MeasureTheory
open scoped ComplexConjugate Topology

private theorem arc_join {F : ℂ → ℂ} {x l m h : ℝ}
    (a : IntervalIntegrable (fun y : ℝ => F ((x:ℂ)+(y:ℂ)*I)) volume l m)
    (b : IntervalIntegrable (fun y : ℝ => F ((x:ℂ)+(y:ℂ)*I)) volume m h) :
    arc F x l m+arc F x m h=arc F x l h := by
  rw [arc,arc,arc,←mul_add,intervalIntegral.integral_add_adjacent_intervals a b]

private theorem total_arc {F : ℂ → ℂ} {x l m h k : ℝ}
    (a : StripTraces F l m) (b : StripTraces F m h) (c : StripTraces F h k) :
    arc F x l m+arc F x m h+arc F x h k=arc F x l k := by
  rw [arc_join (a.arc_integrable x) (b.arc_integrable x),
    arc_join ((a.arc_integrable x).trans (b.arc_integrable x)) (c.arc_integrable x)]

theorem arc_eq_circle (f : ℂ → ℂ) (n : ℕ) (x : ℝ) :
    arc (lifted f n) x 0 (2*Real.pi)=
      ∮ z in C((0:ℂ),Real.exp x), z⁻¹^(n+1)*f z := by
  rw [arc,circleIntegral,←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y _
  change I*lifted f n ((x:ℂ)+(y:ℂ)*I)=_
  have e : circleMap 0 (Real.exp x) y=Complex.exp ((x:ℂ)+(y:ℂ)*I) := by
    simp [circleMap,Complex.exp_add,Complex.ofReal_exp]
  simp only [deriv_circleMap,e,smul_eq_mul,lifted,pow_succ]
  field_simp [Complex.exp_ne_zero]
  ring

noncomputable def jumpIntegrals {s : ℝ} (g : Points s) (n : ℕ) (a b : ℝ) : ℂ :=
  (∫ x : ℝ in a..b, weighted n g.r g.realJump x)+
  (∫ x : ℝ in a..b, weighted n g.u (g.complexJump g.u) x)+
  (∫ x : ℝ in a..b, weighted n (conj g.u) (g.complexJump (conj g.u)) x)

/-- Finite annular deformation for the actual algebraic function. Both circles
are counterclockwise. The counterclockwise-minus-clockwise jumps are integrated
from the inner radius to the outer radius on each radial cut. -/
private theorem annular_and_continuous {s : ℝ} (g : Points s) (n : ℕ) (a b : ℝ) :
    ((∮ z in C((0:ℂ),Real.exp a), z⁻¹^(n+1)*g.branch z)=
    (∮ z in C((0:ℂ),Real.exp b), z⁻¹^(n+1)*g.branch z)+jumpIntegrals g n a b) ∧ Continuous (weighted n g.r g.realJump) ∧
      Continuous (weighted n g.u (g.complexJump g.u)) ∧ Continuous (weighted n (conj g.u) (g.complexJump (conj g.u))) := by
  let θ := g.u.arg
  let θ' := 2*Real.pi-θ
  have an : 0<θ ∧ θ<Real.pi := g.angle
  have order : θ<θ' := by dsimp [θ']; linarith [an.2]
  have last : θ'<2*Real.pi := by dsimp [θ']; linarith [an.1]
  obtain ⟨L⟩ := axis_exists (g.all_real_jumps)
  obtain ⟨U⟩ := axis_exists (g.all_complex_jumps (Or.inl rfl))
  obtain ⟨V⟩ := axis_exists (g.all_complex_jumps (Or.inr rfl))
  have one (z : ℂ) (hz : z∈strip 0 θ) := g.exp_domain (z:=z)
    ⟨hz.2.1,hz.2.2.trans (order.trans last)⟩ hz.2.2.ne (hz.2.2.trans order).ne
  have two (z : ℂ) (hz : z∈strip θ θ') := g.exp_domain (z:=z)
    ⟨an.1.trans hz.2.1,hz.2.2.trans last⟩ hz.2.1.ne' hz.2.2.ne
  have three (z : ℂ) (hz : z∈strip θ' (2*Real.pi)) := g.exp_domain (z:=z)
    ⟨(an.1.trans order).trans hz.2.1,hz.2.2⟩ (order.trans hz.2.1).ne' hz.2.1.ne'
  have up := norm_pos_iff.mpr g.u_ne
  let d₁ := sectorTraces g an.1 g.rpos up (by simp) g.upper_polar L U n one
  let d₂ := sectorTraces g order up up g.upper_polar g.lower_polar U V n two
  let d₃ := sectorTraces g last up g.rpos g.lower_polar (by simp) V L n three
  let F := lifted g.branch n
  have s₁ := d₁.balance a b
  have s₂ := d₂.balance a b
  have s₃ := d₃.balance a b
  have C₁ := d₁.traces_continuous
  have C₂ := d₂.traces_continuous
  have C₃ := d₃.traces_continuous
  have jump {c : ℂ} {J : ℝ → ℂ} (T : Axis g.branch c J)
      (cl : Continuous (weighted n c T.left)) (cr : Continuous (weighted n c T.right)) :
      (∫ x in a..b,weighted n c T.left x)-(∫ x in a..b,weighted n c T.right x)=
        ∫ x in a..b, weighted n c J x := by
    rw [←intervalIntegral.integral_sub (cl.intervalIntegrable a b) (cr.intervalIntegrable a b)]
    apply intervalIntegral.integral_congr
    intro x _
    change (radial c x)⁻¹^n*T.left x-(radial c x)⁻¹^n*T.right x=_
    rw [←mul_sub,T.jump]; rfl
  have cont {c : ℂ} {J : ℝ → ℂ} (T : Axis g.branch c J)
      (cl : Continuous (weighted n c T.left)) (cr : Continuous (weighted n c T.right)) :
      Continuous (weighted n c J) := by
    have e : weighted n c J = fun x => weighted n c T.left x-weighted n c T.right x := by
      funext x; unfold weighted; rw [←mul_sub,T.jump]
    rw [e]; exact cl.sub cr
  refine ⟨?_,cont L C₁.1 C₃.2,cont U C₂.1 C₁.2,cont V C₃.1 C₂.2⟩
  have rL := jump L C₁.1 C₃.2
  have rU := jump U C₂.1 C₁.2
  have rV := jump V C₃.1 C₂.2
  change (∫ x in a..b,weighted n g.r L.left x)-(∫ x in a..b,weighted n g.u U.right x)+
    arc F b 0 θ-arc F a 0 θ=0 at s₁
  change (∫ x in a..b,weighted n g.u U.left x)-(∫ x in a..b,weighted n (conj g.u) V.right x)+
    arc F b θ θ'-arc F a θ θ'=0 at s₂
  change (∫ x in a..b,weighted n (conj g.u) V.left x)-(∫ x in a..b,weighted n g.r L.right x)+
    arc F b θ' (2*Real.pi)-arc F a θ' (2*Real.pi)=0 at s₃
  rw [←arc_eq_circle,←arc_eq_circle]
  change arc F a 0 (2*Real.pi)=arc F b 0 (2*Real.pi)+_
  rw [←total_arc (x:=a) d₁ d₂ d₃,←total_arc (x:=b) d₁ d₂ d₃]
  unfold jumpIntegrals
  linear_combination -s₁-s₂-s₃+rL+rU+rV

theorem Points.annular_deformation {s : ℝ} (g : Points s) (n : ℕ) (a b : ℝ) :
    (∮ z in C((0:ℂ),Real.exp a), z⁻¹^(n+1)*g.branch z)=
    (∮ z in C((0:ℂ),Real.exp b), z⁻¹^(n+1)*g.branch z)+jumpIntegrals g n a b :=
  (annular_and_continuous g n a b).1

theorem Points.jump_continuous {s : ℝ} (g : Points s) (n : ℕ) :
    Continuous (weighted n g.r g.realJump) ∧ Continuous (weighted n g.u (g.complexJump g.u)) ∧
    Continuous (weighted n (conj g.u) (g.complexJump (conj g.u))) :=
  (annular_and_continuous g n 0 1).2

end BigDescents132.Slit
