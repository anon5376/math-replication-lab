import BigDescents132.FiniteBlock11

namespace BigDescents132.Certificate127

set_option maxRecDepth 250000
set_option maxHeartbeats 8000000

set_option Elab.async false
private theorem rows12At0 : rowCheck 96=true := by decide +kernel
private theorem rows12At1 : rowCheck 97=true := by decide +kernel
private theorem rows12At2 : rowCheck 98=true := by decide +kernel
private theorem rows12At3 : rowCheck 99=true := by decide +kernel
private theorem rows12At4 : rowCheck 100=true := by decide +kernel
private theorem rows12At5 : rowCheck 101=true := by decide +kernel
private theorem rows12At6 : rowCheck 102=true := by decide +kernel
private theorem rows12At7 : rowCheck 103=true := by decide +kernel
theorem rows12 : (List.range 8).all (fun j => rowCheck (96+j))=true := by
  rw [show List.range 8=[0, 1, 2, 3, 4, 5, 6, 7] by decide]
  simp only [List.all_cons,List.all_nil,Nat.reduceAdd,rows12At0,rows12At1,rows12At2,rows12At3,rows12At4,rows12At5,rows12At6,rows12At7,Bool.and_self]

set_option Elab.async false
private theorem steps12At0 : recurrenceCheck 96=true := by decide +kernel
private theorem steps12At1 : recurrenceCheck 97=true := by decide +kernel
private theorem steps12At2 : recurrenceCheck 98=true := by decide +kernel
private theorem steps12At3 : recurrenceCheck 99=true := by decide +kernel
private theorem steps12At4 : recurrenceCheck 100=true := by decide +kernel
private theorem steps12At5 : recurrenceCheck 101=true := by decide +kernel
private theorem steps12At6 : recurrenceCheck 102=true := by decide +kernel
private theorem steps12At7 : recurrenceCheck 103=true := by decide +kernel
theorem steps12 : (List.range 8).all (fun j => recurrenceCheck (96+j))=true := by
  rw [show List.range 8=[0, 1, 2, 3, 4, 5, 6, 7] by decide]
  simp only [List.all_cons,List.all_nil,Nat.reduceAdd,steps12At0,steps12At1,steps12At2,steps12At3,steps12At4,steps12At5,steps12At6,steps12At7,Bool.and_self]

set_option Elab.async false
private theorem grids12At0 : gridCheck 96=true := by decide +kernel
private theorem grids12At1 : gridCheck 97=true := by decide +kernel
private theorem grids12At2 : gridCheck 98=true := by decide +kernel
private theorem grids12At3 : gridCheck 99=true := by decide +kernel
private theorem grids12At4 : gridCheck 100=true := by decide +kernel
private theorem grids12At5 : gridCheck 101=true := by decide +kernel
private theorem grids12At6 : gridCheck 102=true := by decide +kernel
private theorem grids12At7 : gridCheck 103=true := by decide +kernel
theorem grids12 : (List.range 8).all (fun j => gridCheck (96+j))=true := by
  rw [show List.range 8=[0, 1, 2, 3, 4, 5, 6, 7] by decide]
  simp only [List.all_cons,List.all_nil,Nat.reduceAdd,grids12At0,grids12At1,grids12At2,grids12At3,grids12At4,grids12At5,grids12At6,grids12At7,Bool.and_self]

end BigDescents132.Certificate127
