import BigDescents132.Jump
import Mathlib.Topology.ExtendFrom

namespace BigDescents132.Slit
open Complex Filter Set MeasureTheory
open scoped Topology Interval

def strip (l h : ℝ) : Set ℂ := univ ×ℂ Ioo l h

structure StripTraces (F : ℂ → ℂ) (l h : ℝ) where
  lower : ℝ → ℂ
  upper : ℝ → ℂ
  ordered : l<h
  hol : ∀ z∈strip l h, DifferentiableAt ℂ F z
  low : ∀ x : ℝ, Tendsto F (𝓝[strip l h] ((x:ℂ)+(l:ℂ)*I)) (𝓝 (lower x))
  high : ∀ x : ℝ, Tendsto F (𝓝[strip l h] ((x:ℂ)+(h:ℂ)*I)) (𝓝 (upper x))

noncomputable def arc (F : ℂ → ℂ) (x l h : ℝ) : ℂ :=
  I*(∫ y : ℝ in l..h, F ((x:ℂ)+(y:ℂ)*I))

private theorem stripClosure {l h : ℝ} (hh : l<h) : closure (strip l h)=univ ×ℂ Icc l h := by
  simp [strip,closure_reProdIm,closure_Ioo hh.ne]

private theorem mk_complex (z : ℂ) : (z.re:ℂ)+(z.im:ℂ)*I=z := Complex.re_add_im z

private theorem inside_eq_ae {f g : ℝ → ℂ} {l h : ℝ} (lh : l≤h) (e : EqOn f g (Ioo l h)) :
    f =ᵐ[volume.restrict (uIoc l h)] g := by
  rw [uIoc_of_le lh,Filter.EventuallyEq,ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [show ∀ᵐ x : ℝ ∂volume, x≠h from by rw [ae_iff]; simp] with x hx hmem
  exact e ⟨hmem.1,lt_of_le_of_ne hmem.2 hx⟩

private theorem strip_extension {F : ℂ → ℂ} {l h : ℝ} (d : StripTraces F l h) :
    let G := extendFrom (strip l h) F
    ContinuousOn G (univ ×ℂ Icc l h) ∧
    (∀ z∈strip l h, G z=F z) ∧
    (∀ x : ℝ, G ((x:ℂ)+(l:ℂ)*I)=d.lower x) ∧
    (∀ x : ℝ, G ((x:ℂ)+(h:ℂ)*I)=d.upper x) := by
  let G := extendFrom (strip l h) F
  have cl := stripClosure d.ordered
  have within : ContinuousOn F (strip l h) := fun z hz => (d.hol z hz).continuousAt.continuousWithinAt
  have representations (z : ℂ) (hz : z∈univ ×ℂ Icc l h) :
      ∃ v, Tendsto F (𝓝[strip l h] z) (𝓝 v) := by
    rcases hz.2.1.eq_or_lt with hlow|hlow
    · have e : z=(z.re:ℂ)+(l:ℂ)*I := by rw [hlow,mk_complex]
      simpa only [←e] using (show ∃ v, Tendsto F _ (𝓝 v) from ⟨_,d.low z.re⟩)
    rcases hz.2.2.eq_or_lt with hhigh|hhigh
    · have e : z=(z.re:ℂ)+(h:ℂ)*I := by rw [←hhigh,mk_complex]
      simpa only [←e] using (show ∃ v, Tendsto F _ (𝓝 v) from ⟨_,d.high z.re⟩)
    exact ⟨_,(d.hol z ⟨trivial,hlow,hhigh⟩).continuousAt.continuousWithinAt.tendsto⟩
  refine ⟨continuousOn_extendFrom cl.ge representations,extendFrom_extends within,?_,?_⟩
  · intro x; apply extendFrom_eq _ (d.low x)
    rw [cl]; exact ⟨trivial,by simpa using (show l∈Icc l h from ⟨le_rfl,d.ordered.le⟩)⟩
  · intro x; apply extendFrom_eq _ (d.high x)
    rw [cl]; exact ⟨trivial,by simpa using (show h∈Icc l h from ⟨d.ordered.le,le_rfl⟩)⟩

/-- Cauchy–Goursat on a logarithmic rectangle with actual one-sided limits.
The horizontal integrals run outwards. Continuous extension from the open
strip includes boundary branch points, so no detour integral is needed. -/
theorem StripTraces.balance {F : ℂ → ℂ} {l h : ℝ} (d : StripTraces F l h) (a b : ℝ) :
    (∫ x in a..b, d.lower x)-(∫ x in a..b, d.upper x)+arc F b l h-arc F a l h=0 := by
  let G := extendFrom (strip l h) F
  obtain ⟨cont,eq,elo,ehi⟩ := strip_extension d
  have C : ContinuousOn G ((uIcc a b) ×ℂ (uIcc l h)) := by
    rw [uIcc_of_le d.ordered.le]
    exact cont.mono fun z hz => ⟨trivial,hz.2⟩
  have D : DifferentiableOn ℂ G (Ioo (min a b) (max a b) ×ℂ Ioo l h) := by
    have op : IsOpen (strip l h) := isOpen_univ.reProdIm isOpen_Ioo
    intro z hz
    have hz' : z∈strip l h := ⟨trivial,hz.2⟩
    have e : G =ᶠ[𝓝 z] F := eventually_of_mem (op.mem_nhds hz') eq
    exact ((d.hol z hz').congr_of_eventuallyEq e).differentiableWithinAt
  have rect := integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn G
    (⟨a,l⟩:ℂ) (⟨b,h⟩:ℂ) C (by simpa [min_eq_left d.ordered.le,max_eq_right d.ordered.le] using D)
  have v (x : ℝ) : (∫ y : ℝ in l..h, G ((x:ℂ)+(y:ℂ)*I))=
      ∫ y : ℝ in l..h, F ((x:ℂ)+(y:ℂ)*I) := by
    apply intervalIntegral.integral_congr_ae_restrict (inside_eq_ae d.ordered.le ?_)
    intro y hy
    exact eq _ ⟨trivial,by simpa using hy⟩
  change (∫ x : ℝ in a..b, G ((x:ℂ)+(l:ℂ)*I))-(∫ x : ℝ in a..b, G ((x:ℂ)+(h:ℂ)*I))+
    I • (∫ y : ℝ in l..h, G ((b:ℂ)+(y:ℂ)*I))-I • (∫ y : ℝ in l..h, G ((a:ℂ)+(y:ℂ)*I))=0 at rect
  change ∀ x : ℝ, G ((x:ℂ)+(l:ℂ)*I)=d.lower x at elo
  change ∀ x : ℝ, G ((x:ℂ)+(h:ℂ)*I)=d.upper x at ehi
  simpa only [elo,ehi,v,smul_eq_mul,arc] using rect

theorem StripTraces.arc_integrable {F : ℂ → ℂ} {l h : ℝ} (d : StripTraces F l h) (x : ℝ) :
    IntervalIntegrable (fun y : ℝ => F ((x:ℂ)+(y:ℂ)*I)) volume l h := by
  let G := extendFrom (strip l h) F
  obtain ⟨cont,eq,-,-⟩ := strip_extension d
  have h : ContinuousOn (fun y : ℝ => G ((x:ℂ)+(y:ℂ)*I)) (uIcc l h) := by
    apply cont.comp (by fun_prop)
    intro y hy; rw [uIcc_of_le d.ordered.le] at hy
    exact ⟨trivial,by simpa using hy⟩
  exact h.intervalIntegrable.congr (inside_eq_ae d.ordered.le fun y hy =>
    eq _ ⟨trivial,by simpa using hy⟩)

theorem StripTraces.traces_continuous {F : ℂ → ℂ} {l h : ℝ} (d : StripTraces F l h) :
    Continuous d.lower ∧ Continuous d.upper := by
  let G := extendFrom (strip l h) F
  obtain ⟨cont,-,elo,ehi⟩ := strip_extension d
  have c (y : ℝ) (hy : y∈Icc l h) : Continuous (fun x : ℝ => G ((x:ℂ)+(y:ℂ)*I)) :=
    continuous_iff_continuousOn_univ.mpr (cont.comp (by fun_prop) (fun _ _ => ⟨trivial,by simpa using hy⟩))
  exact ⟨(funext elo) ▸ c _ ⟨le_rfl,d.ordered.le⟩,(funext ehi) ▸ c _ ⟨d.ordered.le,le_rfl⟩⟩

end BigDescents132.Slit
