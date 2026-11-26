import BigDescents132.FiniteBlock03

namespace BigDescents132.Certificate127

set_option maxRecDepth 250000
set_option maxHeartbeats 8000000

theorem rows4 : (List.range 8).all (fun j => rowCheck (32+j))=true := by decide +kernel

theorem steps4 : (List.range 8).all (fun j => recurrenceCheck (32+j))=true := by decide +kernel

theorem grids4 : (List.range 8).all (fun j => gridCheck (32+j))=true := by decide +kernel

end BigDescents132.Certificate127
