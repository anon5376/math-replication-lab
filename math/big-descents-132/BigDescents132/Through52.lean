import BigDescents132.Data52
import BigDescents132.Certificate

namespace BigDescents132
namespace Certificate52
open Coefficients

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private def goodStep (k : ℕ) : Bool := decide (table (k+2) = next table k)

private theorem all_steps : (List.range 51).all goodStep = true := by decide +kernel

theorem represents_table (n : ℕ) (hn : n ≤ 52) : Represents (table n) n := by
  apply table_correct table 52 (by rfl) (by rfl) _ n hn
  intro k hk
  have h := List.all_eq_true.mp all_steps k (List.mem_range.mpr (by omega))
  exact of_decide_eq_true h

private def goodGrid (n : ℕ) : Bool :=
  let r := (table n).total
  let g := grid n
  decide (evalQ r 0 ≠ 0 ∧ r.length-1 ≤ g.length ∧ g.length = expectedDegree n) && checks r 0 g

private theorem all_grids : (List.range 53).all goodGrid = true := by decide +kernel

theorem root_certificate (n : ℕ) (hn : n ≤ 52) :
    (ofRow (table n).total).natDegree = expectedDegree n ∧ SimpleNegative (ofRow (table n).total) := by
  have h := List.all_eq_true.mp all_grids n (List.mem_range.mpr (by omega))
  simp only [goodGrid, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hz, hb, hd⟩, hs⟩ := h
  rw [← hd]
  exact checked_row _ _ hz hb hs

end Certificate52

theorem B_eq_row_through52 (n : ℕ) (hn : n ≤ 52) : B n = ofRow (Certificate52.table n).total :=
  (Certificate52.represents_table n hn).1

/-- Every certificate in the finite table concerns the defining permutation polynomial. -/
theorem finite52_simple_negative (n : ℕ) (hn : n ≤ 52) :
    (B n).natDegree = expectedDegree n ∧ SimpleNegative (B n) := by
  rw [B_eq_row_through52 n hn]
  exact Certificate52.root_certificate n hn

end BigDescents132
