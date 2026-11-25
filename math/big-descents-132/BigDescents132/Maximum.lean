import BigDescents132.Permutations
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace BigDescents132
namespace Maximum
open Polynomial
open scoped Polynomial

theorem word_iff {w : List ℕ} {n : ℕ} :
    w ∈ words n ↔ w.Perm (List.range n) ∧ avoids132 w = true := by
  simp [words, List.mem_permutations']

theorem length_word {w : List ℕ} {n : ℕ} (h : w ∈ words n) : w.length = n := by
  simpa using (word_iff.mp h).1.length_eq

theorem lt_of_mem_word {w : List ℕ} {n a : ℕ} (h : w ∈ words n) (ha : a ∈ w) : a < n :=
  List.mem_range.mp ((word_iff.mp h).1.mem_iff.mp ha)

theorem avoids_sublist {v w : List ℕ} (h : v.Sublist w) (hw : avoids132 w = true) :
    avoids132 v = true :=
  (avoids132_iff v).mpr fun a b c hs => (avoids132_iff w).mp hw a b c (hs.trans h)

theorem avoids_shift (j : ℕ) (w : List ℕ) :
    avoids132 (w.map (j + ·)) = true ↔ avoids132 w = true := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [List.map_cons, avoids132, Bool.and_eq_true, noInversionAbove_iff,
      List.pairwise_map, Nat.add_lt_add_iff_left, ih]

theorem avoids_join {m : ℕ} {l r : List ℕ} (hl : avoids132 l = true)
    (hr : avoids132 r = true) (hlm : ∀ x ∈ l, x < m) (hrm : ∀ y ∈ r, y < m)
    (hsep : ∀ x ∈ l, ∀ y ∈ r, y < x) : avoids132 (l ++ m :: r) = true := by
  have hmax : noInversionAbove m r = true := by
    apply (noInversionAbove_iff _ _).mpr
    exact List.pairwise_of_forall_mem_list (fun _ _ _ hy h => (hrm _ hy).asymm h.1)
  induction l with
  | nil => simpa [avoids132, hmax] using hr
  | cons a l ih =>
    rw [avoids132, Bool.and_eq_true, noInversionAbove_iff] at hl
    rw [List.cons_append, avoids132, Bool.and_eq_true, noInversionAbove_iff, List.pairwise_append]
    refine ⟨⟨hl.1, ?_, ?_⟩, ih hl.2 (fun x hx => hlm x (.tail a hx))
      (fun x hx => hsep x (.tail a hx))⟩
    · rw [List.pairwise_cons]
      refine ⟨fun y hy bad => (hsep a (.head _) y hy).asymm bad.1, ?_⟩
      exact List.pairwise_of_forall_mem_list (fun _ _ _ hy bad => (hsep a (.head _) _ hy).asymm bad.1)
    · intro x hx z hz bad
      rcases List.mem_cons.mp hz with rfl | hz
      · exact (hlm x (.tail a hx)).asymm bad.2
      · exact (hsep a (.head _) z hz).asymm bad.1

/-- Insert the maximum between a shifted left block and an unshifted right block. -/
def join (i j : ℕ) (u v : List ℕ) := u.map (j + ·) ++ (i+j) :: v

theorem joined_perm {i j : ℕ} {u v : List ℕ} (hu : u.Perm (List.range i))
    (hv : v.Perm (List.range j)) : (join i j u v).Perm (List.range (i+j+1)) := by
  rw [List.range_succ, join]
  apply List.perm_middle.trans
  apply (List.Perm.cons _ ?_).trans (List.perm_append_singleton _ _).symm
  rw [show List.range (i+j) = List.range j ++ (List.range i).map (j+·) by
    rw [Nat.add_comm i j, List.range_add]]
  exact ((hu.map _).append hv).trans List.perm_append_comm

theorem join_mem {i j : ℕ} {u v : List ℕ} (hu : u ∈ words i) (hv : v ∈ words j) :
    join i j u v ∈ words (i+j+1) := by
  refine word_iff.mpr ⟨joined_perm (word_iff.mp hu).1 (word_iff.mp hv).1, ?_⟩
  apply avoids_join ((avoids_shift j u).mpr (word_iff.mp hu).2) (word_iff.mp hv).2
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    have := lt_of_mem_word hu ha
    omega
  · intro y hy
    have := lt_of_mem_word hv hy
    omega
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    have := lt_of_mem_word hv hy
    omega

/-- Standardize both blocks of a literal avoider by removing its maximum. -/
theorem decompose_raw {i j : ℕ} {l r : List ℕ}
    (hr : r.length = j) (hw : l ++ (i+j) :: r ∈ words (i+j+1)) :
    ∃ u ∈ words i, r ∈ words j ∧ l = u.map (j+·) := by
  obtain ⟨p, ha⟩ := word_iff.mp hw
  have p' : (l ++ r).Perm (List.range (i+j)) := by
    rw [List.range_succ] at p
    exact (List.perm_middle.symm.trans (p.trans (List.perm_append_singleton _ _))).cons_inv
  have nd := List.nodup_append.mp (p'.nodup_iff.mpr List.nodup_range)
  have sep (x) (hx : x ∈ l) (y) (hy : y ∈ r) : y ≤ x := by
    have ym : y < i+j := List.mem_range.mp (p'.mem_iff.mp (List.mem_append_right _ hy))
    have hs := (List.singleton_sublist.mpr hx).append ((List.singleton_sublist.mpr hy).cons₂ (i+j))
    exact le_of_not_gt (fun hxy => (avoids132_iff _).mp ha x (i+j) y hs ⟨hxy, ym⟩)
  have lower (x) (hx : x ∈ l) : j ≤ x := by
    by_contra! h
    have sub : x :: r ⊆ List.range j := by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact List.mem_range.mpr h
      · exact List.mem_range.mpr ((sep _ hx _ hy).trans_lt h)
    have hlen := (List.subperm_of_subset (List.nodup_cons.mpr ⟨nd.2.2 hx, nd.2.1⟩) sub).length_le
    simp [hr] at hlen
  have rp : r.Perm (List.range j) := by
    apply List.Perm.symm
    apply List.Subperm.perm_of_length_le _ (by simp [hr])
    apply List.subperm_of_subset List.nodup_range
    intro y hy
    have yj := List.mem_range.mp hy
    have hym : y < i+j := by omega
    rcases List.mem_append.mp (p'.mem_iff.mpr (List.mem_range.mpr hym)) with h | h
    · exact ((not_lt_of_ge (lower y h)) yj).elim
    · exact h
  have lp : l.Perm ((List.range i).map (j+·)) := by
    rw [show List.range (i+j) = List.range j ++ (List.range i).map (j+·) by
      rw [Nat.add_comm i j, List.range_add]] at p'
    apply (List.perm_append_right_iff (List.range j)).mp
    exact ((List.Perm.refl _).append rp.symm).trans (p'.trans List.perm_append_comm)
  let u := l.map (·-j)
  have recover : u.map (j+·) = l := by
    simp only [u, List.map_map]
    conv_rhs => rw [← List.map_id l]
    apply List.map_inj_left.mpr
    intro x hx
    have := lower x hx
    dsimp
    omega
  have up : u.Perm (List.range i) := by
    simpa [u, List.map_map, Function.comp_def] using lp.map (·-j)
  have la := avoids_sublist (List.sublist_append_left l ((i+j)::r)) ha
  have ra := avoids_sublist ((List.Sublist.refl r).cons (i+j) |>.trans (List.sublist_append_right l _)) ha
  exact ⟨u, word_iff.mpr ⟨up, (avoids_shift j u).mp (recover.symm ▸ la)⟩,
    word_iff.mpr ⟨rp, ra⟩, recover.symm⟩

theorem cut_join {i j : ℕ} {u v : List ℕ} (hu : u ∈ words i) :
    (join i j u v).idxOf (i+j) = i := by
  have h : i+j ∉ u.map (j+·) := by
    intro hm
    obtain ⟨a, ha, he⟩ := List.mem_map.mp hm
    have := lt_of_mem_word hu ha
    omega
  simp [join, List.idxOf_append_of_not_mem h, length_word hu]

theorem decompose {i j : ℕ} {w : List ℕ} (hw : w ∈ words (i+j+1))
    (hi : w.idxOf (i+j) = i) :
    ∃ u ∈ words i, ∃ v ∈ words j, w = join i j u v := by
  have hm : i+j ∈ w := (word_iff.mp hw).1.mem_iff.mpr (List.mem_range.mpr (by omega))
  obtain ⟨l, r, rfl⟩ := List.append_of_mem hm
  have hn := List.nodup_append.mp ((word_iff.mp hw).1.nodup_iff.mpr List.nodup_range)
  have hm' : i+j ∉ l := fun h => hn.2.2 h (.head _)
  have hl : l.length = i := by simpa [List.idxOf_append_of_not_mem hm'] using hi
  have hlen := length_word hw
  simp only [List.length_append, List.length_cons] at hlen
  have hr : r.length = j := by omega
  obtain ⟨u, hu, hv, he⟩ := decompose_raw hr hw
  exact ⟨u, hu, r, hv, by rw [join, ← he]⟩

theorem join_inj {i j : ℕ} {u v u' v' : List ℕ} (hu : u ∈ words i) (hu' : u' ∈ words i)
    (he : join i j u v = join i j u' v') : u = u' ∧ v = v' := by
  have h := congrArg (List.take i) he
  have h' := congrArg (List.drop i) he
  have lu : (u.map (j+·)).length = i := by simpa using length_word hu
  have lu' : (u'.map (j+·)).length = i := by simpa using length_word hu'
  simp only [join, ← lu, List.take_left, List.drop_left] at h h'
  rw [lu, ← lu', List.take_left] at h
  rw [lu, ← lu', List.drop_left] at h'
  exact ⟨List.map_injective_iff.mpr (fun _ _ h' => Nat.add_left_cancel h') h, (List.cons.inj h').2⟩

theorem drops_shift (j : ℕ) (w : List ℕ) : bigDescents (w.map (j+·)) = bigDescents w := by
  induction w using bigDescents.induct with
  | case1 a b t ih =>
    simp only [List.map_cons, bigDescents] at *
    simp only [show (j+b+1 < j+a) ↔ b+1 < a by omega, ih]
  | case2 w h =>
    cases w with
    | nil => rfl
    | cons a t => cases t with
      | nil => rfl
      | cons b t => exact (h a b t rfl).elim

theorem drops_append_max (m : ℕ) (l r : List ℕ) (hm : ∀ x ∈ l, x ≤ m) :
    bigDescents (l ++ m :: r) = bigDescents l + bigDescents (m :: r) := by
  induction l using bigDescents.induct with
  | case1 a b t ih =>
    simp only [List.cons_append, bigDescents]
    have h := ih (fun x hx => hm x (.tail a hx))
    simpa [List.cons_append, Nat.add_assoc] using h
  | case2 l h =>
    cases l with
    | nil => simp [bigDescents]
    | cons a t => cases t with
      | nil =>
        have h' := hm a (.head [])
        simp [bigDescents, show ¬ m+1 < a by omega]
      | cons b t => exact (h a b t rfl).elim

theorem drops_join {i j : ℕ} {u v : List ℕ} (hu : u ∈ words i) :
    bigDescents (join i j u v) = bigDescents u + bigDescents ((i+j)::v) := by
  rw [join, drops_append_max, drops_shift]
  intro x hx
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  have := lt_of_mem_word hu ha
  omega

theorem drops_interior {i j : ℕ} {u v : List ℕ} (hu : u ∈ words (i+1))
    (hv : v ∈ words (j+1)) :
    bigDescents (join (i+1) (j+1) u v) = bigDescents u + (1 + bigDescents v) := by
  rw [drops_join hu]
  cases v with
  | nil => have := length_word hv; simp at this
  | cons b t =>
    have := lt_of_mem_word hv (List.Mem.head t)
    rw [bigDescents, if_pos (by omega)]

theorem drops_front {j : ℕ} {v : List ℕ} (hv : v ∈ words (j+1)) :
    bigDescents ((j+1)::v) = (if v.head? = some j then 0 else 1) + bigDescents v := by
  cases v with
  | nil => have := length_word hv; simp at this
  | cons b t =>
    have := lt_of_mem_word hv (List.Mem.head t)
    by_cases h : b = j <;> simp [bigDescents, h, show b+1<j+1 ↔ b≠j by omega]

end Maximum
end BigDescents132
