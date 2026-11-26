import BigDescents132

open BigDescents132

#check mem_words
#check words_nodup
#print bigDescents
#print B
#print expectedDegree
#print SimpleNegative
#check all_ranks_simple_negative
#print axioms BigDescents132.all_ranks_simple_negative

example (n : ℕ) : (B n).Splits (RingHom.id ℝ) ∧ (B n).roots.Nodup ∧
    ∀ x ∈ (B n).roots, x < 0 :=
  (all_ranks_simple_negative n).2.2
