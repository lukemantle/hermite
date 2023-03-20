import analysis.calculus.mean_value
import analysis.special_functions.exp
import analysis.special_functions.exp_deriv
import data.nat.factorial.basic
import data.nat.choose.basic
import basic
import exp
import coeff
open polynomial

open set filter

noncomputable theory

@[simp]
def double_factorial : ℕ → ℕ
| 0 := 1
| 1 := 1
| (k+2) := (k+2) * double_factorial k

notation n `‼`:10000 := double_factorial n -- this is \!! not two !'s
localized "notation (name := nat.factorial) n `!`:10000 := nat.factorial n" in nat

@[simp] 
def hermite_explicit (n k : ℕ) : ℤ :=
if (even (n-k)) then (-1)^((n-k)/2) * (n-k-1)‼ * nat.choose n k
else 0

-- -- a _ 2n, 2k
-- @[simp]
-- def hermite_explicit_even (n k : ℕ) : ℝ := (-1)^(n - k) * double_factorial (2*n - 2*k - 1) * nat.choose (2*n) (2*k)

-- lemma hermite_coeff_explicit_even_zero_zero : hermite_coeff_explicit_even 0 0 = 1 := by simp

-- lemma hermite_coeff_explicit_even_one_one : hermite_coeff_explicit_even 1 1 = 1 := by simp

-- #check nat.choose

-- lemma hermite_coeff_explicit_even_upper_zero (n k : ℕ) : hermite_coeff_explicit_even n (n+k+1) = 0 :=
-- begin
--   induction n with n ih,
--   { norm_num,
--     refl },
--   { norm_num,
--     right,
--     apply nat.choose_eq_zero_of_lt,
--     ring,
--     apply lt_add_of_pos_right,
--     simp }
-- end

-- -- a _ 2n+1, 2k+1
-- @[simp]
-- def hermite_coeff_explicit_odd (n k : ℕ) : ℝ := (-1)^(n - k) * double_factorial (2*n - 2*k - 1) * nat.choose (2*n + 1) (2*k + 1)


-- lemma hermite_coeff_explicit_odd_zero_zero : hermite_coeff_explicit_odd 0 0 = 1 := by simp

-- lemma hermite_coeff_explicit_odd_upper_zero (n k : ℕ) : hermite_coeff_explicit_odd n (n+k+1) = 0 :=
-- begin
--   induction n with n ih,
--   { norm_num,
--     refl },
--   { norm_num,
--     right,
--     apply nat.choose_eq_zero_of_lt,
--     ring,
--     apply lt_add_of_pos_right,
--     simp }
-- end

lemma hermite_explicit_upper (n k : ℕ) : hermite_explicit n (n + k + 1) = 0 :=
begin
  induction n with n ih,
  { simp },
  { simp only [hermite_explicit],
    split_ifs,
    { norm_num,
      right,
      apply nat.choose_eq_zero_of_lt,
      linarith },
    { refl }}
end

lemma hermite_explicit_recur_zero (n : ℕ) : hermite_explicit (n + 1) 0 = - hermite_explicit n 1 :=
begin
  sorry
end

lemma hermite_explicit_recur (n k : ℕ) : hermite_explicit (n + 1) (k + 1) =
hermite_explicit n k - (k + 2) * hermite_explicit n (k + 2) :=
begin
  sorry
end

lemma hermite_explicit_eq_coeff (n k : ℕ) : (hermite_explicit n k) = coeff (hermite n) k :=
begin
  sorry
end
-- lemma add_two_of_succ_add_succ (n k : ℕ) : (n.succ + k.succ) = (n + k + 2) :=
-- begin
--   repeat {rw ← nat.add_one},
--   ring
-- end
ℤ  ℝ


-- lemma hermite_coeff_explicit_even (n k : ℕ) :
-- coeff (hermite (n + 2)) (k + 2) = coeff (hermite n) k - (2*k + 5) * (coeff (hermite n) (k + 2))
-- + (k + 3) * (k + 4) * (coeff (hermite n) (k + 4)) :=

lemma hermite_coeff_explicit_recur_even (n k : ℕ) :
hermite_coeff_explicit_even (n + 1) (k + 1) = hermite_coeff_explicit_even n k -
(4*k + 5) * hermite_coeff_explicit_even n (k+1)
+ (2*k + 3) * (2*k + 4) * (hermite_coeff_explicit_even n (k+2)) :=
begin
  induction n with n ih generalizing k,
  { cases k,
    { repeat {rw zero_add},
      rw [hermite_coeff_explicit_even_one_one, hermite_coeff_explicit_even_zero_zero,
          hermite_coeff_explicit_even_upper_zero 0 0,
          hermite_coeff_explicit_even_upper_zero 0 1],
      ring },
    { rw [zero_add, ← nat.add_one, (by linarith : k + 1 + 1 = 1 + k + 1)],
      rw [hermite_coeff_explicit_even_upper_zero 1 k,
          (by linarith : 1 + k + 1 = 0 + (k + 1) + 1),
          hermite_coeff_explicit_even_upper_zero 0 (k + 1),
          (by linarith : k + 1 + 2 = 0 + (k + 2) + 1),
          hermite_coeff_explicit_even_upper_zero 0 (k + 2)],
      norm_num,
      rw [two_mul, nat.add_one k, nat.add_succ,
          nat.choose_zero_succ (k.succ + k), nat.cast_zero] }},
  {  } -- unfold, use properties of bin coefficient and !!, rw cast
end

lemma hermite_coeff_explicit_recur_even_zero (n : ℕ) :
hermite_coeff_explicit_even (n + 1) 0 =
2 * hermite_coeff_explicit_even n 1 - hermite_coeff_explicit_even n 0 :=
begin
  sorry,
end

lemma hermite_coeff_explicit_recur_odd (n k : ℕ) :
hermite_coeff_explicit_odd (n + 1) (k + 1) = hermite_coeff_explicit_odd n k -
(4*k + 5) * hermite_coeff_explicit_odd n (k+1)
+ (2*k + 3) * (2*k + 4) * (hermite_coeff_explicit_odd n (k+2)) :=
begin
  induction n with n ih,
  { sorry },
  { sorry } -- unfold, use properties of bin coefficient and !!, rw cast
end

lemma hermite_coeff_eq_explicit_even (n k : ℕ) : hermite_coeff_explicit_even n k = coeff (hermite (2*n)) (2*k) :=
begin
  induction n with n ihn generalizing k,
  { cases k,
    { repeat { rw mul_zero },
      rw [hermite_coeff_explicit_even_zero_zero, hermite_zero_zero] },
    { rw [mul_zero, ← nat.add_one, ← zero_add (k + 1), ← add_assoc,
          hermite_coeff_explicit_even_upper_zero 0 k, hermite_upper_coeff_zero'],
      simp } },
  { cases k,
    { rw [nat.mul_succ, mul_zero],
      rw [hermite_coeff_explicit_recur_even_zero, hermite_recur_coeff_zero_two],
      repeat {rw ihn _},
      rw [mul_one, mul_zero], },
    { repeat {rw nat.mul_succ},
      rw hermite_recur_coeff_two (2*n) (2*k),
      rw hermite_coeff_explicit_recur_even,
      repeat {rw ihn _},
      norm_num,
      ring } }
end

lemma hermite_coeff_eq_explicit_odd (n k : ℕ) : hermite_coeff_explicit_odd n k = coeff (hermite (2*n + 1)) (2*k + 1) :=
begin
  induction n with n ihn generalizing k,
  { cases k,
    { 
      repeat { rw mul_zero },
      rw [hermite_coeff_explicit_odd_zero_zero, hermite_one_one] },
    { 
      rw hermite_upper_coeff_zero',
      rw hermite_coeff_explicit_odd_upper_zero,
      -- rw [mul_zero, ← nat.add_one, ← zero_add (k + 1), ← add_assoc,
      --     hermite_coeff_explicit_even_upper_zero 0 k, hermite_upper_coeff_zero'],
      simp } },
  -- { cases k,
  --   { rw [nat.mul_succ, mul_zero],
  --     rw [hermite_coeff_explicit_recur_even_zero, hermite_recur_coeff_zero_two],
  --     repeat {rw ihn _},
  --     rw [mul_one, mul_zero], },
  --   { repeat {rw nat.mul_succ},
  --     rw hermite_recur_coeff_two (2*n) (2*k),
  --     rw hermite_coeff_explicit_recur_even,
  --     repeat {rw ihn _},
  --     norm_num,
  --     ring_nf } }
  
end

lemma hermite_coeff_eq_explicit_odd (n k : ℕ) : hermite_coeff_explicit_odd n k = coeff (hermite (2*n + 1)) (2*k + 1) := sorry

-- (2m)! = 2^m * m! * (2m - 1)!!

example : ∀ (a b : ℕ), (b+1) * (nat.choose a (b+1)) = (nat.choose a b) * (a - b)
| 0 b := by simp
| (a+1) b := by rw [← nat.choose_mul_succ_eq, mul_comm, ← nat.succ_mul_choose_eq, mul_comm]