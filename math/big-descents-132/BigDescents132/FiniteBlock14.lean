import BigDescents132.FiniteBlock13

namespace BigDescents132.Certificate127

set_option maxRecDepth 250000
set_option maxHeartbeats 8000000

set_option Elab.async false
private theorem rows14At0 : rowCheck 112=true := by decide +kernel
private theorem rows14At1 : rowCheck 113=true := by decide +kernel
private theorem rows14At2 : rowCheck 114=true := by decide +kernel
private theorem rows14At3 : rowCheck 115=true := by decide +kernel
private theorem rows14At4 : rowCheck 116=true := by decide +kernel
private theorem rows14At5 : rowCheck 117=true := by decide +kernel
private theorem rows14At6 : rowCheck 118=true := by decide +kernel
private theorem rows14At7 : rowCheck 119=true := by decide +kernel
theorem rows14 : (List.range 8).all (fun j => rowCheck (112+j))=true := by
  rw [show List.range 8=[0, 1, 2, 3, 4, 5, 6, 7] by decide]
  simp only [List.all_cons,List.all_nil,Nat.reduceAdd,rows14At0,rows14At1,rows14At2,rows14At3,rows14At4,rows14At5,rows14At6,rows14At7,Bool.and_self]

set_option Elab.async false
private theorem steps14At0 : recurrenceCheck 112=true := by decide +kernel
private theorem steps14At1 : recurrenceCheck 113=true := by decide +kernel
private theorem steps14At2 : recurrenceCheck 114=true := by decide +kernel
private theorem steps14At3 : recurrenceCheck 115=true := by decide +kernel
private theorem steps14At4 : recurrenceCheck 116=true := by decide +kernel
private theorem steps14At5 : recurrenceCheck 117=true := by decide +kernel
private theorem steps14At6 : recurrenceCheck 118=true := by decide +kernel
private theorem steps14At7 : recurrenceCheck 119=true := by decide +kernel
theorem steps14 : (List.range 8).all (fun j => recurrenceCheck (112+j))=true := by
  rw [show List.range 8=[0, 1, 2, 3, 4, 5, 6, 7] by decide]
  simp only [List.all_cons,List.all_nil,Nat.reduceAdd,steps14At0,steps14At1,steps14At2,steps14At3,steps14At4,steps14At5,steps14At6,steps14At7,Bool.and_self]

set_option Elab.async false
private theorem grids14At0 : gridCheck 112=true := by decide +kernel
private theorem grids14At1 : gridCheck 113=true := by decide +kernel
private theorem grids14At2 : gridCheck 114=true := by decide +kernel
private theorem grids14At3 : gridCheck 115=true := by decide +kernel
private theorem grids14At4 : gridCheck 116=true := by decide +kernel
private theorem grids14At5 : gridCheck 117=true := by decide +kernel
private theorem grids14At6 : gridCheck 118=true := by decide +kernel
private theorem grids14At7 : gridCheck 119=true := by decide +kernel
theorem grids14 : (List.range 8).all (fun j => gridCheck (112+j))=true := by
  rw [show List.range 8=[0, 1, 2, 3, 4, 5, 6, 7] by decide]
  simp only [List.all_cons,List.all_nil,Nat.reduceAdd,grids14At0,grids14At1,grids14At2,grids14At3,grids14At4,grids14At5,grids14At6,grids14At7,Bool.and_self]

end BigDescents132.Certificate127
