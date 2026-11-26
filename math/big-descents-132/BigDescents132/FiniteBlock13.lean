import BigDescents132.FiniteBlock12

namespace BigDescents132.Certificate127

set_option maxRecDepth 250000
set_option maxHeartbeats 8000000

set_option Elab.async false
private theorem rows13At0 : rowCheck 104=true := by decide +kernel
private theorem rows13At1 : rowCheck 105=true := by decide +kernel
private theorem rows13At2 : rowCheck 106=true := by decide +kernel
private theorem rows13At3 : rowCheck 107=true := by decide +kernel
private theorem rows13At4 : rowCheck 108=true := by decide +kernel
private theorem rows13At5 : rowCheck 109=true := by decide +kernel
private theorem rows13At6 : rowCheck 110=true := by decide +kernel
private theorem rows13At7 : rowCheck 111=true := by decide +kernel
theorem rows13 : (List.range 8).all (fun j => rowCheck (104+j))=true := by
  rw [show List.range 8=[0, 1, 2, 3, 4, 5, 6, 7] by decide]
  simp only [List.all_cons,List.all_nil,Nat.reduceAdd,rows13At0,rows13At1,rows13At2,rows13At3,rows13At4,rows13At5,rows13At6,rows13At7,Bool.and_self]

set_option Elab.async false
private theorem steps13At0 : recurrenceCheck 104=true := by decide +kernel
private theorem steps13At1 : recurrenceCheck 105=true := by decide +kernel
private theorem steps13At2 : recurrenceCheck 106=true := by decide +kernel
private theorem steps13At3 : recurrenceCheck 107=true := by decide +kernel
private theorem steps13At4 : recurrenceCheck 108=true := by decide +kernel
private theorem steps13At5 : recurrenceCheck 109=true := by decide +kernel
private theorem steps13At6 : recurrenceCheck 110=true := by decide +kernel
private theorem steps13At7 : recurrenceCheck 111=true := by decide +kernel
theorem steps13 : (List.range 8).all (fun j => recurrenceCheck (104+j))=true := by
  rw [show List.range 8=[0, 1, 2, 3, 4, 5, 6, 7] by decide]
  simp only [List.all_cons,List.all_nil,Nat.reduceAdd,steps13At0,steps13At1,steps13At2,steps13At3,steps13At4,steps13At5,steps13At6,steps13At7,Bool.and_self]

set_option Elab.async false
private theorem grids13At0 : gridCheck 104=true := by decide +kernel
private theorem grids13At1 : gridCheck 105=true := by decide +kernel
private theorem grids13At2 : gridCheck 106=true := by decide +kernel
private theorem grids13At3 : gridCheck 107=true := by decide +kernel
private theorem grids13At4 : gridCheck 108=true := by decide +kernel
private theorem grids13At5 : gridCheck 109=true := by decide +kernel
private theorem grids13At6 : gridCheck 110=true := by decide +kernel
private theorem grids13At7 : gridCheck 111=true := by decide +kernel
theorem grids13 : (List.range 8).all (fun j => gridCheck (104+j))=true := by
  rw [show List.range 8=[0, 1, 2, 3, 4, 5, 6, 7] by decide]
  simp only [List.all_cons,List.all_nil,Nat.reduceAdd,grids13At0,grids13At1,grids13At2,grids13At3,grids13At4,grids13At5,grids13At6,grids13At7,Bool.and_self]

end BigDescents132.Certificate127
