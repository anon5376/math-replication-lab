import BigDescents132.FiniteBlock05

namespace BigDescents132.Certificate127

set_option maxRecDepth 250000
set_option maxHeartbeats 8000000

theorem rows6 : (List.range 8).all (fun j => rowCheck (48+j))=true := by decide +kernel

theorem steps6 : (List.range 8).all (fun j => recurrenceCheck (48+j))=true := by decide +kernel

theorem grids6 : (List.range 8).all (fun j => gridCheck (48+j))=true := by decide +kernel

end BigDescents132.Certificate127
