import BigDescents132.EndpointSign2370

namespace BigDescents132.AllRanks

set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem check3800 :
    headCheck (countFast 129) (countFast (fixedRadix+128)) 3800 true=true := by decide +kernel

theorem endpoint3800 (N : ℕ) (hN : 128≤N) : 0<(B N).eval (-(3800:ℝ)/(N:ℝ)^3) := by
  simpa using headCheck_sound _ _ (fun _ _ => rfl) (fun _ _ => rfl) 3800 true check3800 N hN (by decide)

end BigDescents132.AllRanks
