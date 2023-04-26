import basic
import exp
import coeff
import explicit
open polynomial


-- lemma hermite_eval_even (n : ℕ) (x : ℝ) :
-- eval (-x) (hermite n) = if (even n) then eval x (hermite n) else -(eval x (hermite n)) :=
-- begin
--   induction n with n ih,
--   { sorry },
--   { sorry }
-- end

-- example (p : polynomial ℝ) (x : ℝ) : eval x p = eval x p :=
-- begin
--   refl,
-- end

-- example (n : ℕ) (x : ℝ) : eval x (hermite n) = eval x (hermite n) :=
-- begin
--   refl,
-- end

example (p : polynomial ℝ) (h : ∀ n, odd n → coeff p n = 0) (x : ℝ) : eval (-x) p = eval x p :=
begin
  sorry
end


variables {R : Type} [comm_ring R] (p : polynomial R)

lemma polynomial_even (hp : ∀ n, odd n → p.coeff n = 0) (x) : p.eval (-x) = p.eval x :=
begin
  repeat {rw polynomial.eval_eq_sum_range},
  congr,
  ext i,
  cases i.even_or_odd with hi hi,
  { rw [neg_pow, hi.neg_one_pow, one_mul] },
  { rw [hp _ hi, zero_mul, zero_mul] },
end

lemma polynomial_odd (hp : ∀ n, even n → p.coeff n = 0) (x) : p.eval (-x) = -(p.eval x) :=
begin
  repeat {rw polynomial.eval_eq_sum_range},
  nth_rewrite 0 (neg_eq_neg_one_mul _),
  rw [finset.mul_sum],
  congr,
  ext i,
  cases i.even_or_odd with hi hi,
  { rw hp _ hi, ring },
  { rw [neg_pow, hi.neg_one_pow], ring },
end

#check nat.odd_add

lemma hermite_eval_even (n : ℕ) (x : ℤ) (h : even n) :
eval (-x) (hermite n) = eval x (hermite n) :=
begin
  have h1 : ∀ k, odd k → odd (n + k),
  { intros k hk,
    rw add_comm,
    apply nat.odd_add.mpr,
    exact iff_of_true hk h },
  have h2 : ∀ k, odd k → coeff (hermite n) k = 0,
  { intros k hk,
    exact hermite_coeff_odd_zero n k (h1 k hk) },
  exact polynomial_even (hermite n) h2 x
end

lemma hermite_eval_odd (n : ℕ) (x : ℤ) (h : odd n):
eval (-x) (hermite n) = -(eval x (hermite n)) :=
begin
    have h1 : ∀ k, even k → odd (n + k),
    { intros k hk,
      apply nat.odd_add.mpr,
      exact iff_of_true h hk },
    have h2 : ∀ k, even k → coeff (hermite n) k = 0,
    { intros k hk,
      exact hermite_coeff_odd_zero n k (h1 k hk) },
    exact polynomial_odd (hermite n) h2 x
end

lemma hermite_eval_even' (n : ℕ) (x : ℤ) (h : even n) :
eval (-x) (hermite n) = eval x (hermite n) :=
begin
  have h1 : ∀ k, odd k → odd (n + k),
  { intros k hk,
    rw add_comm,
    apply nat.odd_add.mpr,
    exact iff_of_true hk h },
  have h2 : ∀ k, odd k → coeff (hermite n) k = 0,
  { intros k hk,
    exact hermite_coeff_odd_zero n k (h1 k hk) },
  repeat {rw polynomial.eval_eq_sum_range},
  congr,
  ext i,
  cases i.even_or_odd with hi hi,
  { rw [neg_pow, hi.neg_one_pow, one_mul] },
  { rw [h2 i hi, zero_mul, zero_mul] }
end

lemma hermite_eval_odd' (n : ℕ) (x : ℤ) (h : odd n):
eval (-x) (hermite n) = -(eval x (hermite n)) :=
begin
    have h1 : ∀ k, even k → odd (n + k),
    { intros k hk,
      apply nat.odd_add.mpr,
      exact iff_of_true h hk },
    have h2 : ∀ k, even k → coeff (hermite n) k = 0,
    { intros k hk,
      exact hermite_coeff_odd_zero n k (h1 k hk) },
    repeat {rw polynomial.eval_eq_sum_range},
  nth_rewrite 0 (neg_eq_neg_one_mul _),
  rw [finset.mul_sum],
  congr,
  ext i,
  cases i.even_or_odd with hi hi,
  { rw h2 i hi, ring },
  { rw [neg_pow, hi.neg_one_pow], ring }
end

lemma polynomial_odd_or_even (n : ℕ) (x : ℤ) (p : polynomial ℤ)
(hp : ∀ k, odd (n + k) → p.coeff k = 0) : p.eval (-x) = (-1)^n * p.eval x :=
begin
  repeat {rw polynomial.eval_eq_sum_range},
  rw finset.mul_sum,
  congr',
  ext i,
  rw [neg_pow],
  nth_rewrite 1 mul_comm,
  rw [← mul_assoc, mul_comm],
  cases nat.even_or_odd (n+i) with hni hni,
  { 
    rw (_ : (-1:ℤ)^i = (-1:ℤ)^n),
    
    sorry,
    -- cases nat.even_or_odd i with hi hi,
    -- { have hn : even n, by { rwa nat.even_add.mp hni },
    --   repeat {rw (neg_one_pow_eq_one_iff_even _).mpr},
    --   exact hn,
    --   sorry,
    --   exact hi,
    --   sorry, },
    -- {  } 
    },
  { rw hp i hni,
    simp, }
end

lemma hermite_eval_even_odd (n : ℕ) (x : ℤ) :
(hermite n).eval (-x) = (-1)^n * (hermite n).eval x :=
begin
  repeat {rw polynomial.eval_eq_sum_range},
  rw finset.mul_sum,
  congr',
  ext i,
  rw [neg_pow],
  nth_rewrite 1 mul_comm,
  rw [← mul_assoc, mul_comm],
  sorry
end


lemma polynomial.coeff_comp_neg_X {R : Type} [comm_ring R] {p : polynomial R} (k : ℕ) :
(p.comp (-X).coeff k = )