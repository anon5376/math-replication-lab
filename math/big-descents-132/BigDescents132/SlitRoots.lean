import BigDescents132.Dominance
import BigDescents132.RegularBranch
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.ComputeDegree

namespace BigDescents132.Slit
open Complex Polynomial Set
open scoped ComplexConjugate

/-- Branch points in their radial-cut order, with the upper point distinguished. -/
structure Points (s : ℝ) where
  r : ℝ
  R : ℝ
  u : ℂ
  parameter : 1<s
  small : r∈Ioo (1/s) 1
  large : R∈Ioo (1:ℝ) 4
  upper : 0<u.im
  factor : ∀ z : ℂ, (radicand (s:ℂ)).eval z =
    (1-z/r)*(1-z/R)*(1-z/u)*(1-z/(conj u))

private theorem cast_eval (s x : ℝ) :
    (radicand (s:ℂ)).eval (x:ℂ)=((radicand s).eval x:ℝ) := by simp [radicand]

private theorem root_conj {s : ℝ} {z : ℂ} (h : (radicand (s:ℂ)).IsRoot z) :
    (radicand (s:ℂ)).IsRoot (conj z) := by
  change (radicand (s:ℂ)).eval z=0 at h
  have e := congrArg (conj : ℂ → ℂ) h
  simpa [Polynomial.IsRoot,radicand,map_ofNat] using e

/-- Every negative parameter for the original polynomial has a factored quartet
of branch points. This selects actual complex roots of its radicand. -/
theorem points_exist {s : ℝ} (hs : 1<s) : Nonempty (Points s) := by
  classical
  let p := radicand (s:ℂ)
  have hs0 : 0<s := by linarith
  have sc : (s:ℂ)≠0 := ofReal_ne_zero.mpr hs0.ne'
  have sc1 : (s:ℂ)≠1 := by exact_mod_cast hs.ne'
  have hd : p.natDegree=4 := by
    dsimp [p,radicand]
    compute_degree <;> simp [sc]
  have hne : p≠0 := by intro e; rw [e,natDegree_zero] at hd; omega
  have hc : p.roots.card=4 := by simpa [hd] using (natDegree_eq_card_roots (IsAlgClosed.splits p)).symm
  have hnod : p.roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro z
    rw [p.count_roots,←not_lt,one_lt_rootMultiplicity_iff_isRoot hne]
    exact fun h => radicand_simple sc sc1 h.1 h.2
  obtain ⟨r,hr,R,hR,hall⟩ := real_branch_points hs
  have nonreal : ∃ z∈p.roots, z.im≠0 := by
    by_contra! H
    have sub : p.roots.toFinset ⊆ ({(r:ℂ),(R:ℂ)} : Finset ℂ) := by
      intro z hz
      have hm := Multiset.mem_toFinset.mp hz
      have e : z=(z.re:ℂ) := Complex.ext rfl (by simpa using H z hm)
      have eq := (Polynomial.mem_roots hne).mp hm
      have rt : (radicand s).IsRoot z.re := by
        change p.eval z=0 at eq
        rw [e] at eq
        exact ofReal_eq_zero.mp ((cast_eval s _).symm.trans eq)
      rcases (hall _).mp rt with h|h <;> rw [e,h] <;> simp
    have le := Finset.card_le_card sub
    rw [Multiset.toFinset_card_of_nodup hnod,hc] at le
    have bound := Finset.card_insert_le (r:ℂ) ({(R:ℂ)} : Finset ℂ)
    simp only [Finset.card_singleton] at bound
    omega
  obtain ⟨z,hz,him⟩ := nonreal
  obtain ⟨u,hu,hu'⟩ : ∃ u : ℂ, p.IsRoot u ∧ 0<u.im := by
    rcases lt_or_gt_of_ne him with h|h
    · exact ⟨conj z,root_conj ((mem_roots hne).mp hz),by simpa using neg_pos.mpr h⟩
    · exact ⟨z,(mem_roots hne).mp hz,h⟩
  have U (x : ℝ) : u≠(x:ℂ) := by intro e; rw [e,ofReal_im] at hu'; exact (lt_irrefl _ hu')
  have V (x : ℝ) : conj u≠(x:ℂ) := by intro e; have := congrArg im e; simp at this; linarith
  have UV : u≠conj u := by intro e; have := congrArg im e; simp at this; linarith
  have rr := (hr.2.trans hR.1).ne
  have rr' : (r:ℂ)≠(R:ℂ) := by exact_mod_cast rr
  let l : Multiset ℂ := [(r:ℂ),(R:ℂ),u,conj u]
  have ln : l.Nodup := by simp [l,rr',(U r).symm,(U R).symm,(V r).symm,(V R).symm,UV]
  have rootR (x : ℝ) (h : x=r ∨ x=R) : p.IsRoot (x:ℂ) := by
    change (radicand (s:ℂ)).eval (x:ℂ)=0
    rw [cast_eval]; exact ofReal_eq_zero.mpr ((hall x).mpr h)
  have sub : l ≤ p.roots := by
    apply (Multiset.le_iff_subset ln).mpr
    intro x hx
    apply (mem_roots hne).mpr
    simp only [l,Multiset.mem_coe,List.mem_cons,List.mem_nil_iff,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl
    · exact rootR _ (Or.inl rfl)
    · exact rootR _ (Or.inr rfl)
    · exact hu
    · exact root_conj hu
  have el : p.roots=l := (Multiset.eq_of_le_of_card_le sub (by simp [hc,l])).symm
  have ef (x : ℂ) : p.eval x=p.leadingCoeff*((x-r)*(x-R)*(x-u)*(x-conj u)) := by
    simpa [el,l,mul_assoc] using eval_eq_prod_roots_sub_of_splits_id (IsAlgClosed.splits p) x
  have e0 := ef 0
  have tr : p.eval 0=1 := by simp [p,radicand]
  rw [tr] at e0
  have r0 : (r:ℂ)≠0 := ofReal_ne_zero.mpr ((one_div_pos.mpr hs0).trans hr.1).ne'
  have R0 : (R:ℂ)≠0 := ofReal_ne_zero.mpr (zero_lt_one.trans hR.1).ne'
  have u0 : u≠0 := by simpa using U 0
  have cu0 : conj u≠0 := by simpa using V 0
  refine ⟨⟨r,R,u,hs,hr,hR,hu',fun x => ?_⟩⟩
  change p.eval x=_
  rw [ef]
  field_simp [r0,R0,u0,cu0]
  linear_combination -(x-r)*(x-R)*(x-u)*(x-conj u)*e0

end BigDescents132.Slit
