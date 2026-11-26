import BigDescents132.FiniteBlock00

namespace BigDescents132.Certificate127

set_option maxRecDepth 250000
set_option maxHeartbeats 8000000

theorem rows1 : (List.range 8).all (fun j => rowCheck (8+j))=true := by decide +kernel

theorem steps1 : (List.range 8).all (fun j => recurrenceCheck (8+j))=true := by decide +kernel

theorem grids1 : (List.range 8).all (fun j => gridCheck (8+j))=true := by decide +kernel

end BigDescents132.Certificate127
