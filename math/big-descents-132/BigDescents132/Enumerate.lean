import BigDescents132.Insertion

namespace BigDescents132

open Polynomial
open scoped Polynomial

private def children (a : ℕ) (w : List ℕ) : List (List ℕ) :=
  (List.permutations'Aux a w).filter avoids132

def completions : List ℕ → List ℕ → List (List ℕ)
  | [], w => [w]
  | a :: t, w => (children a w).flatMap (completions t)

private theorem completions_append (xs ys w : List ℕ) :
    completions (xs ++ ys) w = (completions xs w).flatMap (completions ys) := by
  induction xs generalizing w with
  | nil => simp [completions]
  | cons a t ih =>
    simp only [List.cons_append, completions, List.flatMap_assoc]
    rw [show completions (t ++ ys) = _ from funext ih]

private theorem completions_eq (l : List ℕ) : completions l.reverse [] = enumerate l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp [List.reverse_cons, completions_append, ih, completions, enumerate, children]

/-- Add ascending natural coefficient lists, extending the shorter one with zeros. -/
def addRows : List ℕ → List ℕ → List ℕ
  | [], t => t
  | t, [] => t
  | a :: l, b :: t => (a+b) :: addRows l t

theorem ofRow_add (l t : List ℕ) : ofRow (addRows l t) = ofRow l + ofRow t := by
  induction l generalizing t with
  | nil => simp [addRows, ofRow]
  | cons a l ih =>
    cases t with
    | nil => simp [addRows, ofRow]
    | cons b t => simp [addRows, ofRow, ih]; ring

private def nextWords (a : ℕ) (w : List ℕ) : List (List ℕ) :=
  if (w.all fun x => decide (a < x)) && avoids132 w then insertMinimum a w else children a w

private theorem nextWords_eq (a : ℕ) (w : List ℕ) : nextWords a w = children a w := by
  unfold nextWords
  split
  · rename_i h
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact insertMinimum_eq a w h.1 h.2
  · rfl

/-- Sum the coefficients at each branch before returning to its parent.
The depth of the arithmetic reduction is controlled by the permutation length. -/
def grow : List ℕ → List ℕ → List ℕ
  | [], w => bump (bigDescents w) []
  | a :: t, w => (nextWords a w).foldr (fun u r => addRows (grow t u) r) []

private theorem ofRow_fold (ws : List (List ℕ)) (f : List ℕ → List ℕ) :
    ofRow (ws.foldr (fun u r => addRows (f u) r) []) = (ws.map (fun u => ofRow (f u))).sum := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [ofRow_add, ih]

private theorem ofRow_grow (l w : List ℕ) :
    ofRow (grow l w) = ((completions l w).map (fun u => (X : ℝ[X]) ^ bigDescents u)).sum := by
  induction l generalizing w with
  | nil =>
    have h := ofRow_histogram [w]
    simpa [grow, completions, histogram] using h
  | cons a l ih =>
    simp [grow, nextWords_eq, ofRow_fold, completions, List.map_flatMap, List.flatMap_def, List.sum_flatten, ih, Function.comp_def]

def branchRow (n : ℕ) : List ℕ := grow (List.range n).reverse []

theorem B_eq_branchRow (n : ℕ) : B n = ofRow (branchRow n) := by
  simp only [B, branchRow, ofRow_grow, completions_eq, enumerate_eq, words]

/-- Partition a direct count after an initial group of insertions. Each seed
can be verified in its own kernel reduction. -/
theorem B_partition (n : ℕ) (first rest : List ℕ)
    (h : (List.range n).reverse = first ++ rest) :
    B n = ofRow ((completions first []).foldr (fun w acc => addRows (grow rest w) acc) []) := by
  rw [B_eq_branchRow, branchRow, h, ofRow_grow, completions_append, ofRow_fold]
  simp [List.map_flatMap, List.flatMap_def, List.sum_flatten, ofRow_grow, Function.comp_def]

end BigDescents132
