import Mathlib.Data.List.Permutation
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! The polynomial is defined by literal permutations of `0, ..., n-1`.
Translation by one preserves all comparisons used below. -/

namespace BigDescents132

open Polynomial
open scoped Polynomial

/-- Does the tail have an inversion whose smaller entry is greater than `a`? -/
def noInversionAbove (a : ℕ) : List ℕ → Bool
  | [] => true
  | b :: t => t.all (fun c => decide (¬ (a < c ∧ c < b))) && noInversionAbove a t

def avoids132 : List ℕ → Bool
  | [] => true
  | a :: t => noInversionAbove a t && avoids132 t

def bigDescents : List ℕ → ℕ
  | a :: b :: t => (if b + 1 < a then 1 else 0) + bigDescents (b :: t)
  | _ => 0

theorem noInversionAbove_iff (a : ℕ) (w : List ℕ) :
    noInversionAbove a w = true ↔ w.Pairwise (fun b c => ¬ (a < c ∧ c < b)) := by
  induction w with
  | nil => simp [noInversionAbove]
  | cons b t ih =>
    simp only [noInversionAbove, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
      List.pairwise_cons, ih]

/-- A forbidden occurrence is a three-entry subsequence, with arbitrary gaps. -/
theorem avoids132_iff (w : List ℕ) :
    avoids132 w = true ↔ ∀ a b c : ℕ, [a,b,c].Sublist w → ¬ (a < c ∧ c < b) := by
  induction w with
  | nil => simp [avoids132]
  | cons x w ih =>
    rw [avoids132, Bool.and_eq_true, noInversionAbove_iff, List.pairwise_iff_forall_sublist, ih]
    constructor
    · rintro ⟨hx, hw⟩ a b c h
      rcases List.cons_sublist_cons'.mp h with htail | ⟨hax, hpair⟩
      · exact hw a b c htail
      · subst x
        exact hx hpair
    · intro h
      exact ⟨fun hb => h x _ _ (hb.cons₂ x), fun _ _ _ hw => h _ _ _ (hw.cons x)⟩

def words (n : ℕ) : List (List ℕ) :=
  (List.range n).permutations'.filter avoids132

theorem mem_words {n : ℕ} {w : List ℕ} :
    w ∈ words n ↔ w.Perm (List.range n) ∧
      ∀ a b c : ℕ, [a,b,c].Sublist w → ¬ (a < c ∧ c < b) := by
  simp [words, List.mem_permutations', avoids132_iff]

theorem words_nodup (n : ℕ) : (words n).Nodup := by
  apply List.Nodup.filter
  exact (List.permutations_perm_permutations' _).nodup_iff.mp
    (List.nodup_permutations _ List.nodup_range)

/-- The defining sum from the paper. -/
noncomputable def B (n : ℕ) : ℝ[X] :=
  ((words n).map fun w => (X : ℝ[X]) ^ bigDescents w).sum

/-- Prune a word as soon as it contains a forbidden subsequence. -/
def enumerate : List ℕ → List (List ℕ)
  | [] => [[]]
  | a :: t => (enumerate t).flatMap (fun w => (List.permutations'Aux a w).filter avoids132)

private theorem rejected_insertions (a : ℕ) (w : List ℕ) (hw : avoids132 w ≠ true) :
    (List.permutations'Aux a w).filter avoids132 = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro u hu hgood
  apply hw
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hu
  rw [List.getElem_permutations'Aux] at hgood
  exact (avoids132_iff _).mpr fun b c d h => (avoids132_iff _).mp hgood b c d
    (h.trans (List.sublist_insertIdx w i a))

private theorem prune_step (a : ℕ) (ws : List (List ℕ)) :
    (ws.filter avoids132).flatMap (fun w => (List.permutations'Aux a w).filter avoids132) =
      ws.flatMap (fun w => (List.permutations'Aux a w).filter avoids132) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    by_cases h : avoids132 w = true
    · simp [List.filter_cons, h, ih]
    · simp [List.filter_cons, h, ih, rejected_insertions a w h]

theorem enumerate_eq (l : List ℕ) : enumerate l = l.permutations'.filter avoids132 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [enumerate, ih, List.permutations', List.filter_flatMap]
    exact prune_step a _

/-- Increment the coefficient of degree `k`, extending the list when needed. -/
def bump : ℕ → List ℕ → List ℕ
  | 0, [] => [1]
  | 0, a :: t => (a + 1) :: t
  | k+1, [] => 0 :: bump k []
  | k+1, a :: t => a :: bump k t

def histogram (ws : List (List ℕ)) : List ℕ :=
  ws.foldr (fun w acc => bump (bigDescents w) acc) []

def row (n : ℕ) := histogram (enumerate (List.range n))

noncomputable def ofRow : List ℕ → ℝ[X]
  | [] => 0
  | a :: t => C (a : ℝ) + X * ofRow t

private theorem ofRow_bump (k : ℕ) (l : List ℕ) :
    ofRow (bump k l) = X ^ k + ofRow l := by
  induction k generalizing l with
  | zero => cases l <;> simp [bump, ofRow, add_assoc, add_comm, add_left_comm]
  | succ k ih =>
    cases l <;> simp [bump, ofRow, ih, pow_succ] <;> ring

theorem ofRow_histogram (ws : List (List ℕ)) :
    ofRow (histogram ws) = (ws.map (fun w => (X : ℝ[X]) ^ bigDescents w)).sum := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simpa [histogram, ofRow_bump] using congrArg (X ^ bigDescents w + ·) ih

theorem B_eq_ofRow (n : ℕ) : B n = ofRow (row n) := by
  simp only [B, row, ofRow_histogram, enumerate_eq, words]

end BigDescents132
