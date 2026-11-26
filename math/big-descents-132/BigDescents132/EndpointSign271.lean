import BigDescents132.EndpointSign74

namespace BigDescents132.AllRanks

set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem check271 :
    headCheck (countFast 129) (countFast (fixedRadix+128)) 271 true=true := by decide +kernel

theorem endpoint271 (N : ℕ) (hN : 128≤N) : 0<(B N).eval (-(271:ℝ)/(N:ℝ)^3) := by
  simpa using headCheck_sound _ _ (fun _ _ => rfl) (fun _ _ => rfl) 271 true check271 N hN (by decide)

end BigDescents132.AllRanks
