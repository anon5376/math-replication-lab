import BigDescents132.Data127
import BigDescents132.PackedData
import BigDescents132.Horner

namespace BigDescents132.Certificate127
open Coefficients Packing

set_option exponentiation.threshold 1024

def radix : ℕ := 2^260
def bigTable (n : ℕ) := if n<128 then stored n else counts radix (table n)
def oneTable (n : ℕ) := if n<128 then masses n else counts 1 (table n)

def rowCheck (n : ℕ) := decide (
  counts radix (table n)=bigTable n ∧ counts 1 (table n)=oneTable n ∧
  (oneTable n).b<radix ∧ (oneTable n).a<radix ∧ (oneTable n).c<radix)

def recurrenceCheck (k : ℕ) := decide (
  bigTable (k+2)=calcStep radix bigTable k ∧ oneTable (k+2)=calcStep 1 oneTable k)

def gridCheck (n : ℕ) :=
  let row := (table n).total
  let l := grid n
  decide (evalQ row 0≠0 ∧ row.length-1≤l.length ∧ l.length=expectedDegree n) &&
    fastChecks row 0 (homogeneous 0 row).1 l

theorem row_steps_sound (row : ∀ n,n<128 → rowCheck n=true)
    (step : ∀ k,k<126 → recurrenceCheck k=true) (n : ℕ) (hn : n≤127) :
    Represents (table n) n := by
  have big (j : ℕ) : counts radix (table j)=bigTable j := by
    by_cases hj : j<128
    · exact (of_decide_eq_true (row j hj)).1
    · simp [bigTable,hj]
  have one (j : ℕ) : counts 1 (table j)=oneTable j := by
    by_cases hj : j<128
    · exact (of_decide_eq_true (row j hj)).2.1
    · simp [oneTable,hj]
  apply Packing.table_sound (q:=radix) (by decide) table 127 (by rfl) (by rfl) _ n hn
  intro k hk
  have hh := of_decide_eq_true (row (k+2) (by omega))
  obtain ⟨bp,op⟩ := of_decide_eq_true (step k (by omega))
  simp only [good,big,one,decide_eq_true_eq]
  exact ⟨op,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2,bp⟩

theorem grid_sound {n : ℕ} (rep : Represents (table n) n) (h : gridCheck n=true) :
    (B n).natDegree=expectedDegree n ∧ SimpleNegative (B n) := by
  simp only [gridCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨hz,hb,hd⟩,hs⟩ := h
  rw [rep.1,←hd]
  exact checked_row _ _ hz hb (checks_of_fast _ _ _ hs)

end BigDescents132.Certificate127
