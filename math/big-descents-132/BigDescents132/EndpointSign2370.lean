import BigDescents132.EndpointSign1348

namespace BigDescents132.AllRanks

set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem check2370 :
    headCheck (countFast 129) (countFast (fixedRadix+128)) 2370 false=true := by decide +kernel

theorem endpoint2370 (N : ℕ) (hN : 128≤N) : (B N).eval (-(2370:ℝ)/(N:ℝ)^3)<0 := by
  simpa using headCheck_sound _ _ (fun _ _ => rfl) (fun _ _ => rfl) 2370 false check2370 N hN (by decide)

end BigDescents132.AllRanks
