import BigDescents132.FiniteBlock01

namespace BigDescents132.Certificate127

set_option maxRecDepth 250000
set_option maxHeartbeats 8000000

theorem rows2 : (List.range 8).all (fun j => rowCheck (16+j))=true := by decide +kernel

theorem steps2 : (List.range 8).all (fun j => recurrenceCheck (16+j))=true := by decide +kernel

theorem grids2 : (List.range 8).all (fun j => gridCheck (16+j))=true := by decide +kernel

end BigDescents132.Certificate127
