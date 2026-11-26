import BigDescents132.FiniteBlock09

namespace BigDescents132.Certificate127

set_option maxRecDepth 250000
set_option maxHeartbeats 8000000

theorem rows10 : (List.range 8).all (fun j => rowCheck (80+j))=true := by decide +kernel

theorem steps10 : (List.range 8).all (fun j => recurrenceCheck (80+j))=true := by decide +kernel

theorem grids10 : (List.range 8).all (fun j => gridCheck (80+j))=true := by decide +kernel

end BigDescents132.Certificate127
