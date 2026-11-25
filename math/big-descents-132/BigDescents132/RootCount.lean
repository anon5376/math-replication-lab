import BigDescents132.Permutations
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

namespace BigDescents132

open Polynomial Set
open scoped Polynomial

/-- A nonzero polynomial that splits over the reals, with distinct negative roots. -/
def SimpleNegative (p : ℝ[X]) : Prop :=
  p ≠ 0 ∧ p.Splits (RingHom.id ℝ) ∧ p.roots.Nodup ∧ ∀ x ∈ p.roots, x < 0

/-- At rank zero natural subtraction gives the correct degree zero. -/
def expectedDegree (n : ℕ) : ℕ := 2 * (n - 1) / 3

/-- The unrestricted asymptotic target. -/
def EventualSimpleNegative : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, (B n).natDegree = expectedDegree n ∧ SimpleNegative (B n)

/-- Descending sample arguments from `a` to `c`, with a sign change in every gap. -/
inductive Grid (p : ℝ[X]) : ℝ → ℝ → ℕ → Prop
  | nil (a) : Grid p a a 0
  | cons {a b c k} (ordered : b < a) (change : p.eval a * p.eval b < 0)
      (rest : Grid p b c k) : Grid p a c (k+1)

theorem Grid.append {p : ℝ[X]} {a b c : ℝ} {k j : ℕ}
    (h : Grid p a b k) (h' : Grid p b c j) : Grid p a c (k+j) := by
  induction h with
  | nil => simpa using h'
  | cons hab hs _ ih => simpa [Nat.succ_add] using Grid.cons hab hs (ih h')

private theorem root_between {p : ℝ[X]} {a b : ℝ}
    (h : a < b) (hs : p.eval b * p.eval a < 0) :
    ∃ x ∈ Ioo a b, p.eval x = 0 := by
  rcases mul_neg_iff.mp hs with ⟨hb, ha⟩ | ⟨hb, ha⟩
  · exact intermediate_value_Ioo h.le p.continuousOn ⟨ha, hb⟩
  · exact intermediate_value_Ioo' h.le p.continuousOn ⟨hb, ha⟩

theorem Grid.rootsBelow {p : ℝ[X]} {a b : ℝ} {k : ℕ} (h : Grid p a b k) :
    ∃ s : Finset ℝ, s.card = k ∧ ∀ x ∈ s, x < a ∧ p.IsRoot x := by
  classical
  induction h with
  | nil => exact ⟨∅, by simp, by simp⟩
  | @cons a b c k hab hs _ ih =>
    obtain ⟨s, hcard, hroots⟩ := ih
    obtain ⟨x, hx, hz⟩ := root_between hab hs
    have hnew : x ∉ s := fun hm => (not_lt_of_ge hx.1.le) (hroots x hm).1
    refine ⟨insert x s, by simp [hnew, hcard], ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ⟨hx.2, hz⟩
    · exact ⟨(hroots y hy).1.trans hab, (hroots y hy).2⟩

/-- One more sign sample than the degree forces a full set of simple negative roots. -/
theorem simpleNegative_of_grid {p : ℝ[X]} {b : ℝ} {d : ℕ} (hp : p ≠ 0)
    (grid : Grid p 0 b d) (bound : p.natDegree ≤ d) :
    p.natDegree = d ∧ SimpleNegative p := by
  classical
  obtain ⟨s, hcard, hs⟩ := grid.rootsBelow
  have hsub : s ⊆ p.roots.toFinset := fun x hx =>
    Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr (hs x hx).2)
  have h₁ := Finset.card_le_card hsub
  have h₂ := Multiset.toFinset_card_le p.roots
  have h₃ := Polynomial.card_roots' p
  have heq : s = p.roots.toFinset := Finset.eq_of_subset_of_card_le hsub (by omega)
  refine ⟨by omega, hp, Polynomial.splits_iff_card_roots.mpr (by omega),
    Multiset.toFinset_card_eq_card_iff_nodup.mp (by omega), ?_⟩
  intro x hx
  exact (hs x (heq ▸ Multiset.mem_toFinset.mpr hx)).1

end BigDescents132
