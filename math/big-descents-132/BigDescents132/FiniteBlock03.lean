import BigDescents132.FiniteBlock02

namespace BigDescents132.Certificate127

set_option maxRecDepth 250000
set_option maxHeartbeats 8000000

theorem rows3 : (List.range 8).all (fun j => rowCheck (24+j))=true := by decide +kernel

theorem steps3 : (List.range 8).all (fun j => recurrenceCheck (24+j))=true := by decide +kernel

theorem grids3 : (List.range 8).all (fun j => gridCheck (24+j))=true := by decide +kernel

end BigDescents132.Certificate127
