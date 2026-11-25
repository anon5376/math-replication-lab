import BigDescents132.Enumerate

namespace BigDescents132

set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! Direct rank 10 verification. The fourteen seeds are the avoiding orderings
of the four largest entries. Each equality uses kernel reduction. -/

private theorem family0 : grow [5, 4, 3, 2, 1, 0] [6, 7, 8, 9] = [7, 273, 1451, 1585, 320, 4] := by decide +kernel
private theorem family1 : grow [5, 4, 3, 2, 1, 0] [7, 6, 8, 9] = [1, 63, 553, 995, 373, 17] := by decide +kernel
private theorem family2 : grow [5, 4, 3, 2, 1, 0] [7, 8, 6, 9] = [0, 7, 161, 513, 300, 20] := by decide +kernel
private theorem family3 : grow [5, 4, 3, 2, 1, 0] [7, 8, 9, 6] = [0, 7, 105, 233, 82, 2] := by decide +kernel
private theorem family4 : grow [5, 4, 3, 2, 1, 0] [8, 6, 7, 9] = [0, 7, 217, 919, 761, 98] := by decide +kernel
private theorem family5 : grow [5, 4, 3, 2, 1, 0] [8, 7, 6, 9] = [1, 42, 322, 494, 139, 3] := by decide +kernel
private theorem family6 : grow [5, 4, 3, 2, 1, 0] [8, 7, 9, 6] = [0, 7, 105, 233, 82, 2] := by decide +kernel
private theorem family7 : grow [5, 4, 3, 2, 1, 0] [8, 9, 6, 7] = [0, 7, 161, 513, 300, 20] := by decide +kernel
private theorem family8 : grow [5, 4, 3, 2, 1, 0] [8, 9, 7, 6] = [0, 1, 21, 161, 205, 41] := by decide +kernel
private theorem family9 : grow [5, 4, 3, 2, 1, 0] [9, 6, 7, 8] = [0, 7, 217, 919, 761, 98] := by decide +kernel
private theorem family10 : grow [5, 4, 3, 2, 1, 0] [9, 7, 6, 8] = [0, 1, 42, 322, 494, 139, 3] := by decide +kernel
private theorem family11 : grow [5, 4, 3, 2, 1, 0] [9, 7, 8, 6] = [0, 0, 7, 105, 233, 82, 2] := by decide +kernel
private theorem family12 : grow [5, 4, 3, 2, 1, 0] [9, 8, 6, 7] = [0, 7, 161, 513, 300, 20] := by decide +kernel
private theorem family13 : grow [5, 4, 3, 2, 1, 0] [9, 8, 7, 6] = [1, 21, 161, 205, 41] := by decide +kernel
theorem B_ten : B 10 = ofRow [10, 450, 3684, 7710, 4391, 546, 5] := by
  rw [B_partition 10 [9, 8, 7, 6] [5, 4, 3, 2, 1, 0] (by decide)]
  have hs : completions [9, 8, 7, 6] [] =
    [[6, 7, 8, 9],
     [7, 6, 8, 9],
     [7, 8, 6, 9],
     [7, 8, 9, 6],
     [8, 6, 7, 9],
     [8, 7, 6, 9],
     [8, 7, 9, 6],
     [8, 9, 6, 7],
     [8, 9, 7, 6],
     [9, 6, 7, 8],
     [9, 7, 6, 8],
     [9, 7, 8, 6],
     [9, 8, 6, 7],
     [9, 8, 7, 6]] := by decide +kernel
  rw [hs]
  simp only [List.foldr_cons, List.foldr_nil, family0, family1, family2, family3, family4, family5, family6, family7, family8, family9, family10, family11, family12, family13]
  rfl

end BigDescents132
