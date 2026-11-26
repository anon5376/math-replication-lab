import BigDescents132.Coefficients

namespace BigDescents132.Packing
open Coefficients Polynomial

def pack (q : ℕ) : List ℕ → ℕ
  | [] => 0
  | a::t => a+q*pack q t

theorem eval_eq (q : ℕ) (t : List ℕ) : (ofRow t).eval (q:ℝ)=(pack q t:ℝ) := by
  induction t with
  | nil => simp [ofRow,pack]
  | cons a l ih => simp [ofRow,pack,ih]

private theorem zero_row {q : ℕ} (hq : 0<q) (l : List ℕ) (h : pack q l=0) : ofRow l=0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [pack,Nat.add_eq_zero,Nat.mul_eq_zero] at h
    rw [h.1,ofRow,ih (h.2.resolve_left hq.ne')]; simp

/-- A single evaluation at a radix exceeding both digit sums identifies
the represented polynomials; trailing zeros do not affect the equality. -/
theorem inject {q : ℕ} (hq : 0<q) (a b : List ℕ)
    (da : pack 1 a<q) (db : pack 1 b<q) (eq : pack q a=pack q b) :
    ofRow a=ofRow b := by
  induction a generalizing b with
  | nil => exact (zero_row hq b eq.symm).symm
  | cons x a ih =>
    cases b with
    | nil => exact zero_row hq _ eq
    | cons y b =>
      simp only [pack,one_mul] at da db
      have xx : x<q := by omega
      have yy : y<q := by omega
      have hxy := congrArg (·%q) eq
      simp only [pack,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt xx,Nat.mod_eq_of_lt yy] at hxy
      subst y
      have tail : pack q a=pack q b := by
        simp only [pack,Nat.add_left_cancel_iff,Nat.mul_right_inj hq.ne'] at eq
        exact eq
      rw [ofRow,ofRow,ih b (by omega) (by omega) tail]

structure Triple where
  b : ℕ
  a : ℕ
  c : ℕ
deriving DecidableEq, Inhabited

def counts (q : ℕ) (u : Counts) : Triple := ⟨pack q u.total, pack q u.first, pack q u.other⟩

def conv (f : ℕ → ℕ) (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | m+1 => conv f k m + f (m+1)*f (k-m)

def calcStep (q : ℕ) (t : ℕ → Triple) (k : ℕ) : Triple :=
  let a := (t (k+1)).a+q*(t (k+1)).c
  let c := (t (k+1)).b+q*conv (fun j => (t j).b) k k
  ⟨a+c,a,c⟩

private theorem pack_add (q) (a b : List ℕ) : pack q (addRows a b)=pack q a+pack q b := by
  have e := congrArg (Polynomial.eval (q:ℝ)) (ofRow_add a b)
  simp only [Polynomial.eval_add,eval_eq] at e
  exact_mod_cast e
private theorem pack_shift (q) (a : List ℕ) : pack q (shift a)=q*pack q a := by
  cases a <;> simp [shift,pack]
private theorem pack_mul (q) (a b : List ℕ) : pack q (mul a b)=pack q a*pack q b := by
  have e := congrArg (Polynomial.eval (q:ℝ)) (ofRow_mul a b)
  simp only [Polynomial.eval_mul,eval_eq] at e
  exact_mod_cast e
private theorem pack_conv (q) (f : ℕ → List ℕ) (k m : ℕ) :
    pack q (convolution f k m)=conv (fun j => pack q (f j)) k m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [convolution,conv,pack_add,pack_mul,ih]

theorem calc_spec (q) (t : ℕ → Counts) (k) :
    counts q (next t k)=calcStep q (fun i => counts q (t i)) k := by
  simp only [counts,next,calcStep,pack_add,pack_shift,pack_conv]

def good (q : ℕ) (t : ℕ → Counts) (k : ℕ) : Bool :=
  let one := counts 1 (t (k+2))
  decide (one=calcStep 1 (fun j => counts 1 (t j)) k ∧ one.b<q ∧ one.a<q ∧ one.c<q ∧
    counts q (t (k+2))=calcStep q (fun j => counts q (t j)) k)

theorem table_sound {q : ℕ} (hq : 0<q) (t : ℕ → Counts) (N : ℕ)
    (h0 : t 0=empty) (h1 : t 1=singleton) (step : ∀ k,k+2≤N → good q t k=true)
    (n : ℕ) (hn : n≤N) : Represents (t n) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [h0,Represents,empty,ofRow,BigDescents132.C,A]
    | 1 => simp [h1,Represents,Coefficients.singleton,ofRow]
    | k+2 =>
      have hh := step k hn
      simp only [good,decide_eq_true_eq,←calc_spec] at hh
      obtain ⟨a,b,c,d,e⟩ := hh
      have r := next_represents t k (fun i hi => ih i (by omega) (by omega))
      have b' : (counts 1 (next t k)).b<q := a ▸ b
      have c' : (counts 1 (next t k)).a<q := a ▸ c
      have d' : (counts 1 (next t k)).c<q := a ▸ d
      refine ⟨r.1.trans (inject hq _ _ b' b (congrArg Triple.b e).symm),
        r.2.1.trans (inject hq _ _ c' c (congrArg Triple.a e).symm),
        r.2.2.trans (inject hq _ _ d' d (congrArg Triple.c e).symm)⟩

end BigDescents132.Packing
