import BigDescents132.Certificate

namespace BigDescents132.Packing

/-- Homogeneous Horner evaluation uses no rational GCD inside the coefficient loop. -/
def homogeneous (x : ℚ) : List ℕ → ℤ × ℕ
  | [] => (0,1)
  | c::l =>
    let (u,b) := homogeneous x l
    (x.num*u+(c:ℤ)*(x.den*b:ℕ),x.den*b)

theorem homogeneous_spec (r : List ℕ) (x : ℚ) :
    0<(homogeneous x r).2 ∧ evalQ r x=
    ((homogeneous x r).1:ℚ)/((homogeneous x r).2:ℚ) := by
  induction r with
  | nil => norm_num [homogeneous,evalQ]
  | cons c t ih =>
    obtain ⟨positive,e⟩ := ih
    have dp : 0<(x.den:ℚ) := by exact_mod_cast x.pos
    have tp : 0<((homogeneous x t).2:ℚ) := by exact_mod_cast positive
    simp only [homogeneous]
    refine ⟨mul_pos x.pos positive,?_⟩
    change (c:ℚ)+x*evalQ t x=_
    rw [e]
    push_cast
    have hx : (x.num:ℚ)=x*(x.den:ℚ) := (div_eq_iff dp.ne').mp x.num_div_den
    field_simp [dp.ne',tp.ne']
    rw [hx]
    ring

def fastChecks (r : List ℕ) (a : ℚ) (u : ℤ) : List ℚ → Bool
  | [] => true
  | b::l =>
    let v := (homogeneous b r).1
    decide (b<a ∧ u*v<0) && fastChecks r b v l

theorem checks_of_fast (r : List ℕ) (a : ℚ) (l : List ℚ)
    (h : fastChecks r a (homogeneous a r).1 l=true) : checks r a l=true := by
  induction l generalizing a with
  | nil => rfl
  | cons b t ih =>
    simp only [fastChecks,Bool.and_eq_true,decide_eq_true_eq] at h
    simp only [checks,Bool.and_eq_true,decide_eq_true_eq]
    refine ⟨⟨h.1.1,?_⟩,ih b h.2⟩
    obtain ⟨da,ea⟩ := homogeneous_spec r a
    obtain ⟨db,eb⟩ := homogeneous_spec r b
    rw [ea,eb,div_mul_div_comm,div_neg_iff]
    refine Or.inr ⟨?_,?_⟩
    · exact_mod_cast h.1.2
    · exact_mod_cast mul_pos da db

end BigDescents132.Packing
