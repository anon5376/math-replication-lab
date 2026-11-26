import BigDescents132.FiniteBlock15

namespace BigDescents132.Certificate127

private theorem all_rows (n : ℕ) (hn : n<128) : rowCheck n=true := by
  by_cases h8 : n<8
  · simpa only [show 0+(n-0)=n by omega] using List.all_eq_true.mp rows0 (n-0) (List.mem_range.mpr (by omega))
  by_cases h16 : n<16
  · simpa only [show 8+(n-8)=n by omega] using List.all_eq_true.mp rows1 (n-8) (List.mem_range.mpr (by omega))
  by_cases h24 : n<24
  · simpa only [show 16+(n-16)=n by omega] using List.all_eq_true.mp rows2 (n-16) (List.mem_range.mpr (by omega))
  by_cases h32 : n<32
  · simpa only [show 24+(n-24)=n by omega] using List.all_eq_true.mp rows3 (n-24) (List.mem_range.mpr (by omega))
  by_cases h40 : n<40
  · simpa only [show 32+(n-32)=n by omega] using List.all_eq_true.mp rows4 (n-32) (List.mem_range.mpr (by omega))
  by_cases h48 : n<48
  · simpa only [show 40+(n-40)=n by omega] using List.all_eq_true.mp rows5 (n-40) (List.mem_range.mpr (by omega))
  by_cases h56 : n<56
  · simpa only [show 48+(n-48)=n by omega] using List.all_eq_true.mp rows6 (n-48) (List.mem_range.mpr (by omega))
  by_cases h64 : n<64
  · simpa only [show 56+(n-56)=n by omega] using List.all_eq_true.mp rows7 (n-56) (List.mem_range.mpr (by omega))
  by_cases h72 : n<72
  · simpa only [show 64+(n-64)=n by omega] using List.all_eq_true.mp rows8 (n-64) (List.mem_range.mpr (by omega))
  by_cases h80 : n<80
  · simpa only [show 72+(n-72)=n by omega] using List.all_eq_true.mp rows9 (n-72) (List.mem_range.mpr (by omega))
  by_cases h88 : n<88
  · simpa only [show 80+(n-80)=n by omega] using List.all_eq_true.mp rows10 (n-80) (List.mem_range.mpr (by omega))
  by_cases h96 : n<96
  · simpa only [show 88+(n-88)=n by omega] using List.all_eq_true.mp rows11 (n-88) (List.mem_range.mpr (by omega))
  by_cases h104 : n<104
  · simpa only [show 96+(n-96)=n by omega] using List.all_eq_true.mp rows12 (n-96) (List.mem_range.mpr (by omega))
  by_cases h112 : n<112
  · simpa only [show 104+(n-104)=n by omega] using List.all_eq_true.mp rows13 (n-104) (List.mem_range.mpr (by omega))
  by_cases h120 : n<120
  · simpa only [show 112+(n-112)=n by omega] using List.all_eq_true.mp rows14 (n-112) (List.mem_range.mpr (by omega))
  simpa only [show 120+(n-120)=n by omega] using List.all_eq_true.mp rows15 (n-120) (List.mem_range.mpr (by omega))

private theorem all_steps (n : ℕ) (hn : n<126) : recurrenceCheck n=true := by
  by_cases h8 : n<8
  · simpa only [show 0+(n-0)=n by omega] using List.all_eq_true.mp steps0 (n-0) (List.mem_range.mpr (by omega))
  by_cases h16 : n<16
  · simpa only [show 8+(n-8)=n by omega] using List.all_eq_true.mp steps1 (n-8) (List.mem_range.mpr (by omega))
  by_cases h24 : n<24
  · simpa only [show 16+(n-16)=n by omega] using List.all_eq_true.mp steps2 (n-16) (List.mem_range.mpr (by omega))
  by_cases h32 : n<32
  · simpa only [show 24+(n-24)=n by omega] using List.all_eq_true.mp steps3 (n-24) (List.mem_range.mpr (by omega))
  by_cases h40 : n<40
  · simpa only [show 32+(n-32)=n by omega] using List.all_eq_true.mp steps4 (n-32) (List.mem_range.mpr (by omega))
  by_cases h48 : n<48
  · simpa only [show 40+(n-40)=n by omega] using List.all_eq_true.mp steps5 (n-40) (List.mem_range.mpr (by omega))
  by_cases h56 : n<56
  · simpa only [show 48+(n-48)=n by omega] using List.all_eq_true.mp steps6 (n-48) (List.mem_range.mpr (by omega))
  by_cases h64 : n<64
  · simpa only [show 56+(n-56)=n by omega] using List.all_eq_true.mp steps7 (n-56) (List.mem_range.mpr (by omega))
  by_cases h72 : n<72
  · simpa only [show 64+(n-64)=n by omega] using List.all_eq_true.mp steps8 (n-64) (List.mem_range.mpr (by omega))
  by_cases h80 : n<80
  · simpa only [show 72+(n-72)=n by omega] using List.all_eq_true.mp steps9 (n-72) (List.mem_range.mpr (by omega))
  by_cases h88 : n<88
  · simpa only [show 80+(n-80)=n by omega] using List.all_eq_true.mp steps10 (n-80) (List.mem_range.mpr (by omega))
  by_cases h96 : n<96
  · simpa only [show 88+(n-88)=n by omega] using List.all_eq_true.mp steps11 (n-88) (List.mem_range.mpr (by omega))
  by_cases h104 : n<104
  · simpa only [show 96+(n-96)=n by omega] using List.all_eq_true.mp steps12 (n-96) (List.mem_range.mpr (by omega))
  by_cases h112 : n<112
  · simpa only [show 104+(n-104)=n by omega] using List.all_eq_true.mp steps13 (n-104) (List.mem_range.mpr (by omega))
  by_cases h120 : n<120
  · simpa only [show 112+(n-112)=n by omega] using List.all_eq_true.mp steps14 (n-112) (List.mem_range.mpr (by omega))
  simpa only [show 120+(n-120)=n by omega] using List.all_eq_true.mp steps15 (n-120) (List.mem_range.mpr (by omega))

private theorem all_grids (n : ℕ) (hn : n<128) : gridCheck n=true := by
  by_cases h8 : n<8
  · simpa only [show 0+(n-0)=n by omega] using List.all_eq_true.mp grids0 (n-0) (List.mem_range.mpr (by omega))
  by_cases h16 : n<16
  · simpa only [show 8+(n-8)=n by omega] using List.all_eq_true.mp grids1 (n-8) (List.mem_range.mpr (by omega))
  by_cases h24 : n<24
  · simpa only [show 16+(n-16)=n by omega] using List.all_eq_true.mp grids2 (n-16) (List.mem_range.mpr (by omega))
  by_cases h32 : n<32
  · simpa only [show 24+(n-24)=n by omega] using List.all_eq_true.mp grids3 (n-24) (List.mem_range.mpr (by omega))
  by_cases h40 : n<40
  · simpa only [show 32+(n-32)=n by omega] using List.all_eq_true.mp grids4 (n-32) (List.mem_range.mpr (by omega))
  by_cases h48 : n<48
  · simpa only [show 40+(n-40)=n by omega] using List.all_eq_true.mp grids5 (n-40) (List.mem_range.mpr (by omega))
  by_cases h56 : n<56
  · simpa only [show 48+(n-48)=n by omega] using List.all_eq_true.mp grids6 (n-48) (List.mem_range.mpr (by omega))
  by_cases h64 : n<64
  · simpa only [show 56+(n-56)=n by omega] using List.all_eq_true.mp grids7 (n-56) (List.mem_range.mpr (by omega))
  by_cases h72 : n<72
  · simpa only [show 64+(n-64)=n by omega] using List.all_eq_true.mp grids8 (n-64) (List.mem_range.mpr (by omega))
  by_cases h80 : n<80
  · simpa only [show 72+(n-72)=n by omega] using List.all_eq_true.mp grids9 (n-72) (List.mem_range.mpr (by omega))
  by_cases h88 : n<88
  · simpa only [show 80+(n-80)=n by omega] using List.all_eq_true.mp grids10 (n-80) (List.mem_range.mpr (by omega))
  by_cases h96 : n<96
  · simpa only [show 88+(n-88)=n by omega] using List.all_eq_true.mp grids11 (n-88) (List.mem_range.mpr (by omega))
  by_cases h104 : n<104
  · simpa only [show 96+(n-96)=n by omega] using List.all_eq_true.mp grids12 (n-96) (List.mem_range.mpr (by omega))
  by_cases h112 : n<112
  · simpa only [show 104+(n-104)=n by omega] using List.all_eq_true.mp grids13 (n-104) (List.mem_range.mpr (by omega))
  by_cases h120 : n<120
  · simpa only [show 112+(n-112)=n by omega] using List.all_eq_true.mp grids14 (n-112) (List.mem_range.mpr (by omega))
  simpa only [show 120+(n-120)=n by omega] using List.all_eq_true.mp grids15 (n-120) (List.mem_range.mpr (by omega))

end BigDescents132.Certificate127

namespace BigDescents132
open Certificate127

/-- Exact coefficient and sign checks for every rank through 127. -/
theorem finite127_simple_negative (n : ℕ) (hn : n≤127) :
    (B n).natDegree=expectedDegree n ∧ SimpleNegative (B n) :=
  grid_sound (row_steps_sound all_rows all_steps n hn) (all_grids n (by omega))

end BigDescents132
