import BigDescents132.FiniteBlock04

namespace BigDescents132.Certificate127

set_option maxRecDepth 250000
set_option maxHeartbeats 8000000

theorem rows5 : (List.range 8).all (fun j => rowCheck (40+j))=true := by decide +kernel

theorem steps5 : (List.range 8).all (fun j => recurrenceCheck (40+j))=true := by decide +kernel

theorem grids5 : (List.range 8).all (fun j => gridCheck (40+j))=true := by decide +kernel

end BigDescents132.Certificate127
