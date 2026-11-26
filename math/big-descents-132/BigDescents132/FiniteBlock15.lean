import BigDescents132.FiniteBlock14

namespace BigDescents132.Certificate127

set_option maxRecDepth 250000
set_option maxHeartbeats 8000000

set_option Elab.async false
private theorem rows15At0 : rowCheck 120=true := by decide +kernel
private theorem rows15At1 : rowCheck 121=true := by decide +kernel
private theorem rows15At2 : rowCheck 122=true := by decide +kernel
private theorem rows15At3 : rowCheck 123=true := by decide +kernel
private theorem rows15At4 : rowCheck 124=true := by decide +kernel
private theorem rows15At5 : rowCheck 125=true := by decide +kernel
private theorem rows15At6 : rowCheck 126=true := by decide +kernel
private theorem rows15At7 : rowCheck 127=true := by decide +kernel
theorem rows15 : (List.range 8).all (fun j => rowCheck (120+j))=true := by
  rw [show List.range 8=[0, 1, 2, 3, 4, 5, 6, 7] by decide]
  simp only [List.all_cons,List.all_nil,Nat.reduceAdd,rows15At0,rows15At1,rows15At2,rows15At3,rows15At4,rows15At5,rows15At6,rows15At7,Bool.and_self]

set_option Elab.async false
private theorem steps15At0 : recurrenceCheck 120=true := by decide +kernel
private theorem steps15At1 : recurrenceCheck 121=true := by decide +kernel
private theorem steps15At2 : recurrenceCheck 122=true := by decide +kernel
private theorem steps15At3 : recurrenceCheck 123=true := by decide +kernel
private theorem steps15At4 : recurrenceCheck 124=true := by decide +kernel
private theorem steps15At5 : recurrenceCheck 125=true := by decide +kernel
theorem steps15 : (List.range 6).all (fun j => recurrenceCheck (120+j))=true := by
  rw [show List.range 6=[0, 1, 2, 3, 4, 5] by decide]
  simp only [List.all_cons,List.all_nil,Nat.reduceAdd,steps15At0,steps15At1,steps15At2,steps15At3,steps15At4,steps15At5,Bool.and_self]

set_option Elab.async false
private theorem grids15At0 : gridCheck 120=true := by decide +kernel
private theorem grids15At1 : gridCheck 121=true := by decide +kernel
private theorem grids15At2 : gridCheck 122=true := by decide +kernel
private theorem grids15At3 : gridCheck 123=true := by decide +kernel
private theorem grids15At4 : gridCheck 124=true := by decide +kernel
private theorem grids15At5 : gridCheck 125=true := by decide +kernel
private theorem grids15At6 : gridCheck 126=true := by decide +kernel
private theorem grids15At7 : gridCheck 127=true := by decide +kernel
theorem grids15 : (List.range 8).all (fun j => gridCheck (120+j))=true := by
  rw [show List.range 8=[0, 1, 2, 3, 4, 5, 6, 7] by decide]
  simp only [List.all_cons,List.all_nil,Nat.reduceAdd,grids15At0,grids15At1,grids15At2,grids15At3,grids15At4,grids15At5,grids15At6,grids15At7,Bool.and_self]

end BigDescents132.Certificate127
