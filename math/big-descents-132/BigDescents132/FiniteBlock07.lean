import BigDescents132.FiniteBlock06

namespace BigDescents132.Certificate127

set_option maxRecDepth 250000
set_option maxHeartbeats 8000000

theorem rows7 : (List.range 8).all (fun j => rowCheck (56+j))=true := by decide +kernel

theorem steps7 : (List.range 8).all (fun j => recurrenceCheck (56+j))=true := by decide +kernel

theorem grids7 : (List.range 8).all (fun j => gridCheck (56+j))=true := by decide +kernel

end BigDescents132.Certificate127
