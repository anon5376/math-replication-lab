import BigDescents132.FiniteBlock10

namespace BigDescents132.Certificate127

set_option maxRecDepth 250000
set_option maxHeartbeats 8000000

theorem rows11 : (List.range 8).all (fun j => rowCheck (88+j))=true := by decide +kernel

theorem steps11 : (List.range 8).all (fun j => recurrenceCheck (88+j))=true := by decide +kernel

theorem grids11 : (List.range 8).all (fun j => gridCheck (88+j))=true := by decide +kernel

end BigDescents132.Certificate127
