import BigDescents132.Permutations
import Mathlib.Data.List.Chain

namespace BigDescents132

/-- Inserting a new smallest entry creates a 132 exactly when its suffix
contains an inversion. Enumerate the gaps whose suffix is increasing. -/
def insertMinimum (a : ℕ) : List ℕ → List (List ℕ)
  | [] => [[a]]
  | b :: t =>
      (if (b :: t).Chain' (· ≤ ·) then [a :: b :: t] else []) ++
        (insertMinimum a t).map (b :: ·)

private theorem pairwise_insert {R : ℕ → ℕ → Prop} (a : ℕ)
    (hl : ∀ x, R a x) (hr : ∀ x, R x a) (w : List ℕ) (i : ℕ)
    (h : w.Pairwise R) : (w.insertIdx i a).Pairwise R := by
  induction w generalizing i with
  | nil => cases i <;> simp
  | cons b t ih =>
    cases i with
    | zero => exact List.pairwise_cons.mpr ⟨fun x _ => hl x, h⟩
    | succ i =>
      obtain ⟨hpair, ht⟩ := List.pairwise_cons.mp h
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih i ht⟩
      intro x hx
      rcases List.eq_or_mem_of_mem_insertIdx hx with rfl | hx
      · exact hr b
      · exact hpair x hx

private theorem head_test (a : ℕ) (w : List ℕ) (hmin : ∀ x ∈ w, a < x) :
    noInversionAbove a w = true ↔ w.Chain' (· ≤ ·) := by
  rw [List.chain'_iff_pairwise, noInversionAbove_iff]
  constructor
  · intro h
    exact h.imp_of_mem fun _ hx hrel => le_of_not_gt fun hgt => hrel ⟨hmin _ hx, hgt⟩
  · exact fun h => h.imp fun hle ⟨_, hgt⟩ => (not_lt_of_ge hle) hgt

theorem insertMinimum_eq (a : ℕ) (w : List ℕ) (hm : ∀ x ∈ w, a < x) (hw : avoids132 w = true) :
    insertMinimum a w = (List.permutations'Aux a w).filter avoids132 := by
  induction w with
  | nil => rfl
  | cons b t ih =>
    have hab := hm b (.head t)
    have hmt : ∀ x ∈ t, a < x := fun x hx => hm x (.tail b hx)
    have hww := hw
    rw [avoids132, Bool.and_eq_true] at hww
    obtain ⟨hpair, ht⟩ := hww
    have hfilter : (List.permutations'Aux a t).filter (avoids132 ∘ (b :: ·)) =
        (List.permutations'Aux a t).filter avoids132 := by
      apply List.filter_congr
      intro u hu
      have hu' : noInversionAbove b u = true := by
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hu
        rw [List.getElem_permutations'Aux, noInversionAbove_iff]
        apply pairwise_insert a
        · intro x; dsimp; omega
        · intro x; dsimp; omega
        · exact (noInversionAbove_iff _ _).mp hpair
      simp [Function.comp_def, avoids132, hu']
    rw [insertMinimum, List.permutations'Aux, List.filter_cons, List.filter_map, hfilter, ih hmt ht]
    have ha : (avoids132 (a :: b :: t) = true) ↔ (b :: t).Chain' (· ≤ ·) := by
      rw [avoids132, Bool.and_eq_true, hw, head_test a _ hm]
      simp
    by_cases hs : (b :: t).Chain' (· ≤ ·) <;> simp [hs, ha]

end BigDescents132
