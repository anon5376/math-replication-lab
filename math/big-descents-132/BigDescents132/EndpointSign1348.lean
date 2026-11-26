import BigDescents132.EndpointSign672

namespace BigDescents132.AllRanks

set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem check1348 :
    headCheck (countFast 129) (countFast (fixedRadix+128)) 1348 true=true := by decide +kernel

theorem endpoint1348 (N : ℕ) (hN : 128≤N) : 0<(B N).eval (-(1348:ℝ)/(N:ℝ)^3) := by
  simpa using headCheck_sound _ _ (fun _ _ => rfl) (fun _ _ => rfl) 1348 true check1348 N hN (by decide)

end BigDescents132.AllRanks
