import BigDescents132.EndpointHeadCheck

namespace BigDescents132.AllRanks

set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem check74 :
    headCheck (countFast 129) (countFast (fixedRadix+128)) 74 false=true := by decide +kernel

theorem endpoint74 (N : ℕ) (hN : 128≤N) : (B N).eval (-(74:ℝ)/(N:ℝ)^3)<0 := by
  simpa using headCheck_sound _ _ (fun _ _ => rfl) (fun _ _ => rfl) 74 false check74 N hN (by decide)

end BigDescents132.AllRanks
