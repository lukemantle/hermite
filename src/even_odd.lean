import basic
import exp
import coeff
import explicit
open polynomial

#check hermite_coeff_odd_zero

lemma hermite_eval_even (n : ℕ) (x : ℝ) (h : even n) :
eval (-x) (hermite n) = eval x (hermite n) :=
begin
  have h1 : ∀ k, odd k → odd (n + k), sorry,
  have h2 : ∀ k, odd k → coeff (hermite n) k = 0, sorry,
  sorry
end

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

-- example (p : polynomial ℝ) : true :=
-- begin
--   have a := p.support,
--   have h : p = (∑ n in p.support, coeff p n),
-- end