import BigDescents132.InteriorGeometry
import BigDescents132.Branch

namespace BigDescents132.Slit
open Complex Filter Set Polynomial
open scoped ComplexConjugate Topology

abbrev Param := {s : ℝ // 1<s}
noncomputable def pointsAt (s : Param) : Points s.val := Classical.choice (points_exist s.property)

theorem Points.root_cases {s : ℝ} (g : Points s) (z : ℂ) : (radicand (s:ℂ)).IsRoot z ↔
    z=(g.r:ℂ) ∨ z=(g.R:ℂ) ∨ z=g.u ∨ z=conj g.u := by
  change (radicand (s:ℂ)).eval z=0 ↔ _
  rw [g.factor]
  have f (a : ℂ) (ha : a≠0) : 1-z/a=0 ↔ z=a := by
    rw [sub_eq_zero,eq_comm,div_eq_one_iff_eq ha]
  simp only [mul_eq_zero,f _ (ofReal_ne_zero.mpr g.rpos.ne'),f _ (ofReal_ne_zero.mpr g.Rpos.ne'),f _ g.u_ne,f _ g.cu_ne,or_assoc]

theorem Points.unique_upper {s : ℝ} (g : Points s) {z : ℂ} (h : (radicand (s:ℂ)).IsRoot z)
    (hz : 0<z.im) : z=g.u := by
  rcases (g.root_cases z).mp h with rfl|rfl|eq|rfl
  · simp at hz
  · simp at hz
  · exact eq
  · simp at hz; linarith [g.upper]

theorem Points.unique_small {s : ℝ} (g : Points s) {z : ℂ} (h : (radicand (s:ℂ)).IsRoot z)
    (hz : z.im=0) (hx : z.re<1) : z=(g.r:ℂ) := by
  rcases (g.root_cases z).mp h with eq|rfl|rfl|rfl
  · exact eq
  · simp at hx; linarith [g.large.1]
  · linarith [g.upper]
  · simp at hz; linarith [g.upper]

theorem Points.unique_large {s : ℝ} (g : Points s) {z : ℂ} (h : (radicand (s:ℂ)).IsRoot z)
    (hz : z.im=0) (hx : 1<z.re) : z=(g.R:ℂ) := by
  rcases (g.root_cases z).mp h with rfl|eq|rfl|rfl
  · simp at hx; linarith [g.small.2]
  · exact eq
  · linarith [g.upper]
  · simp at hz; linarith [g.upper]

private def Q (s z : ℂ) := 1-4*z+6*s*z^2-4*s^2*z^3+s^2*z^4

private theorem root_Q {s z : ℂ} : (radicand s).IsRoot z ↔ Q s z=0 := by simp [radicand,IsRoot,Q]
private theorem Q_conj {s : ℝ} {z : ℂ} (h : Q s z=0) : Q s (conj z)=0 := by
  simpa [Q,map_ofNat] using congrArg (conj : ℂ → ℂ) h

private theorem root_germ (s : Param) (w : ℂ) (hw : (radicand (s.val:ℂ)).IsRoot w) :
    ∃ f : Param → ℂ, f s=w ∧ ContinuousAt f s ∧
      (∀ᶠ t in 𝓝 s, (radicand (t.val:ℂ)).IsRoot (f t)) ∧
      (w.im=0 → ∀ᶠ t in 𝓝 s, (f t).im=0) := by
  let S := (s.val:ℂ)
  let a := 6*w^2-8*S*w^3+2*S*w^4
  let b := -4+12*S*w-12*S^2*w^2+4*S^2*w^3
  have sc : S≠0 := ofReal_ne_zero.mpr (zero_lt_one.trans s.property).ne'
  have sc1 : S≠1 := by dsimp [S]; exact_mod_cast s.property.ne'
  have nb := radicand_simple sc sc1 hw
  have b0 : b≠0 := by
    intro e; apply nb
    change (radicand S).derivative.eval w=0
    norm_num [radicand,derivative_add,derivative_sub,derivative_mul,derivative_pow]
    dsimp [b] at e; linear_combination e
  have hd : HasStrictFDerivAt (fun p : ℂ × ℂ => Q (S+p.1) p.2)
      (a • ContinuousLinearMap.fst ℂ ℂ ℂ+b • ContinuousLinearMap.snd ℂ ℂ ℂ) (0,w) := by
    have P := hasStrictFDerivAt_fst (𝕜:=ℂ) (p:=((0:ℂ),w))
    have T := (hasStrictFDerivAt_const (𝕜:=ℂ) S ((0:ℂ),w)).add P
    have W := hasStrictFDerivAt_snd (𝕜:=ℂ) (p:=((0:ℂ),w))
    have W₂ := W.mul W
    have W₃ := W₂.mul W
    have T₂ := T.mul T
    have h := ((((hasStrictFDerivAt_const (𝕜:=ℂ) (1:ℂ) ((0:ℂ),w)).sub (W.const_mul 4)).add
      ((T.const_mul 6).mul W₂)).sub ((T₂.const_mul 4).mul W₃)).add (T₂.mul (W₃.mul W))
    convert h using 1
    · funext p; simp [Q]; ring
    · apply ContinuousLinearMap.ext; intro p
      simp [a,b,ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply]
      ring
  obtain ⟨F,hF,dF,rt,uniq⟩ := Branch.implicit_branch _ w a b b0 (by simpa [S] using root_Q.mp hw) hd
  let δ := fun t : Param => (t.val:ℂ)-S
  have ds : δ s=0 := by simp [δ,S]
  have cd : Continuous δ := by dsimp [δ]; fun_prop
  have td : Tendsto δ (𝓝 s) (𝓝 0) := ds ▸ cd.continuousAt.tendsto
  have tf := dF.continuousAt.tendsto.comp td
  rw [hF] at tf
  have rr := td.eventually rt
  have absol (t : Param) : S+δ t=(t.val:ℂ) := by dsimp [δ]; ring
  refine ⟨F ∘ δ,by simp [ds,hF],by simpa [ContinuousAt,ds,hF] using tf,?_,?_⟩
  · filter_upwards [rr] with t ht
    exact root_Q.mpr (by simpa only [absol] using ht)
  · intro realw
    have cw : conj w=w := Complex.ext rfl (by simp [realw])
    have cF := (Complex.continuous_conj.tendsto w).comp tf
    rw [cw] at cF
    have pp := td.prodMk_nhds cF
    filter_upwards [pp.eventually uniq,rr] with t unique base
    have eq : conj (F (δ t))=F (δ t) := unique (by
      dsimp; rw [absol]; apply Q_conj; simpa only [absol] using base)
    have im := congrArg Complex.im eq
    simp at im
    change (F (δ t)).im=0
    linarith

theorem points_continuous :
    Continuous (fun s : Param => (pointsAt s).r) ∧ Continuous (fun s : Param => (pointsAt s).R) ∧
      Continuous (fun s : Param => (pointsAt s).u) := by
  have real_root (s : Param) (small : Bool) :
      ContinuousAt (fun t : Param => if small then (pointsAt t).r else (pointsAt t).R) s := by
    let w : ℝ := if small then (pointsAt s).r else (pointsAt s).R
    have hw : (radicand (s.val:ℂ)).IsRoot (w:ℂ) := by
      apply ((pointsAt s).root_cases _).mpr
      cases small <;> simp [w]
    obtain ⟨f,eq,cf,rt,realF⟩ := root_germ s w hw
    have im := realF (ofReal_im _)
    have re := Complex.continuous_re.continuousAt.comp cf
    have wt : (f s).re=w := by simp [eq]
    have id : (fun t : Param => if small then (pointsAt t).r else (pointsAt t).R) =ᶠ[𝓝 s] fun t => (f t).re := by
      cases small
      · have gt : 1<(f s).re := wt ▸ (pointsAt s).large.1
        filter_upwards [rt,im,re.tendsto.eventually_const_lt gt] with t h hr hh
        simpa using congrArg Complex.re ((pointsAt t).unique_large h hr hh).symm
      · have lt : (f s).re<1 := wt ▸ (pointsAt s).small.2
        filter_upwards [rt,im,re.tendsto.eventually_lt_const lt] with t h hr hh
        simpa using congrArg Complex.re ((pointsAt t).unique_small h hr hh).symm
    exact re.congr id.symm
  refine ⟨continuous_iff_continuousAt.mpr (fun s => real_root s true),
    continuous_iff_continuousAt.mpr (fun s => real_root s false),continuous_iff_continuousAt.mpr fun s => ?_⟩
  obtain ⟨f,eq,cf,rt,-⟩ := root_germ s (pointsAt s).u (((pointsAt s).root_cases _).mpr (by simp))
  have hi := (Complex.continuous_im.continuousAt.comp cf).tendsto.eventually_const_lt
    (show 0<(f s).im by rw [eq]; exact (pointsAt s).upper)
  apply cf.congr
  filter_upwards [hi,rt] with t ht hr
  exact (pointsAt t).unique_upper hr ht

end BigDescents132.Slit
