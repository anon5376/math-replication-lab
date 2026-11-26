import BigDescents132.EndpointSign271

namespace BigDescents132.AllRanks

set_option maxHeartbeats 0
set_option maxRecDepth 200000

private theorem check672 :
    headCheck (countFast 129) (countFast (fixedRadix+128)) 672 false=true := by decide +kernel

theorem endpoint672 (N : ℕ) (hN : 128≤N) : (B N).eval (-(672:ℝ)/(N:ℝ)^3)<0 := by
  simpa using headCheck_sound _ _ (fun _ _ => rfl) (fun _ _ => rfl) 672 false check672 N hN (by decide)

end BigDescents132.AllRanks
