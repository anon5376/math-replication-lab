import BigDescents132.Recurrence
import BigDescents132.Enumerate

namespace BigDescents132
namespace Coefficients
open Polynomial
open scoped Polynomial

def shift : List ℕ → List ℕ
  | [] => []
  | a :: s => 0 :: a :: s

def scale (a : ℕ) (s : List ℕ) : List ℕ := if a = 0 then [] else s.map (a*·)

def mul : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | a :: s, t => addRows (scale a t) (shift (mul s t))

theorem ofRow_shift (s : List ℕ) : ofRow (shift s) = X * ofRow s := by
  cases s <;> simp [shift, ofRow]

theorem ofRow_scale (a : ℕ) (s : List ℕ) : ofRow (scale a s) = Polynomial.C (a : ℝ) * ofRow s := by
  by_cases h : a = 0
  · simp [scale, h, ofRow]
  simp only [scale, if_neg h]
  induction s with
  | nil => simp [ofRow]
  | cons b s ih => simp [ofRow, ih]; ring

theorem ofRow_mul (s t : List ℕ) : ofRow (mul s t) = ofRow s * ofRow t := by
  induction s with
  | nil => simp [mul, ofRow]
  | cons a s ih => rw [mul, ofRow_add, ofRow_scale, ofRow_shift, ih, ofRow]; ring

/-- The first m summands in the convolution for rank k+2. -/
def convolution (b : ℕ → List ℕ) (k : ℕ) : ℕ → List ℕ
  | 0 => []
  | m+1 => addRows (convolution b k m) (mul (b (m+1)) (b (k-m)))

theorem ofRow_convolution (b : ℕ → List ℕ) (k m : ℕ) :
    ofRow (convolution b k m) =
      ∑ i ∈ Finset.range m, ofRow (b (i+1)) * ofRow (b (k-i)) := by
  induction m with
  | zero => simp [convolution, ofRow]
  | succ m ih => rw [convolution, ofRow_add, ofRow_mul, ih, Finset.sum_range_succ]

structure Counts where
  total : List ℕ
  first : List ℕ
  other : List ℕ
  deriving DecidableEq, Inhabited

def empty : Counts := ⟨[1], [], []⟩
def singleton : Counts := ⟨[1], [1], []⟩

/-- One step of the polynomial recurrence, computed entirely over naturals. -/
def next (table : ℕ → Counts) (k : ℕ) : Counts :=
  let prior := table (k+1)
  let a := addRows prior.first (shift prior.other)
  let c := addRows prior.total (shift (convolution (fun i => (table i).total) k k))
  ⟨addRows a c, a, c⟩

def Represents (r : Counts) (n : ℕ) : Prop :=
  B n = ofRow r.total ∧ A n = ofRow r.first ∧ BigDescents132.C n = ofRow r.other

theorem next_represents (t : ℕ → Counts) (k : ℕ)
    (previous : ∀ i ≤ k+1, Represents (t i) i) : Represents (next t k) (k+2) := by
  obtain ⟨hb,ha,hc⟩ := previous (k+1) le_rfl
  have fa : A (k+2) = ofRow (next t k).first := by
    rw [A_recurrence, ha, hc]
    simp [next, ofRow_add, ofRow_shift]
  have fc : BigDescents132.C (k+2) = ofRow (next t k).other := by
    rw [C_recurrence, hb]
    simp only [next, ofRow_add, ofRow_shift, ofRow_convolution]
    congr 2
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [(previous (i+1) (by omega)).1, (previous (k-i) (by omega)).1]
  refine ⟨?_, fa, fc⟩
  rw [B_eq_A_add_C, fa, fc]
  exact (ofRow_add _ _).symm

/-- A checked finite table is a certificate for the literal permutation polynomials. -/
theorem table_correct (t : ℕ → Counts) (limit : ℕ) (h0 : t 0 = empty) (h1 : t 1 = singleton)
    (steps : ∀ k, k+2 ≤ limit → t (k+2) = next t k) (n : ℕ) (hn : n ≤ limit) :
    Represents (t n) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [h0, Represents, empty, ofRow, A, BigDescents132.C]
    | 1 => simp [h1, Represents, singleton, ofRow]
    | k+2 =>
      rw [steps k hn]
      exact next_represents t k fun i hi => ih i (by omega) (by omega)

end Coefficients
end BigDescents132
