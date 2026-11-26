import BigDescents132.RankChecks

namespace BigDescents132.Certificate127

set_option maxRecDepth 250000
set_option maxHeartbeats 8000000

theorem rows0 : (List.range 8).all (fun j => rowCheck (0+j))=true := by decide +kernel

theorem steps0 : (List.range 8).all (fun j => recurrenceCheck (0+j))=true := by decide +kernel

theorem grids0 : (List.range 8).all (fun j => gridCheck (0+j))=true := by decide +kernel

end BigDescents132.Certificate127
