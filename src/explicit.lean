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

lemma double_factorial_add_two (n : ℕ) : double_factorial (n + 2) = (n + 2) * double_factorial n := rfl

notation n `‼`:10000 := double_factorial n -- this is \!! not two !'s
localized "notation (name := nat.factorial) n `!`:10000 := nat.factorial n" in nat

@[simp] 
def hermite_explicit (n k : ℕ) : ℝ :=
if (even (n-k)) then (-1)^((n-k)/2) * (n-k-1)‼ * nat.choose n k
else 0

lemma hermite_explicit_upper (n k : ℕ) : hermite_explicit n (n + k + 1) = 0 :=
begin
  simp only [hermite_explicit],
  rw nat.choose_eq_zero_of_lt (by linarith : n < n + k + 1),
  simp
end

lemma hermite_explicit_recur_zero (n : ℕ) : hermite_explicit (n + 1) 0 = - hermite_explicit n 1 :=
begin
  simp only [hermite_explicit],
  rw nat.sub_zero,
  rw (by simp : n + 1 - 1 = n - 2 + 2),
  rw double_factorial_add_two,
  sorry
end


lemma succ_mul_choose_succ_eq (n k : ℕ) : (k+1) * (nat.choose n (k+1)) = (nat.choose n k) * (n - k) :=
begin
  cases n,
    { simp },
    { have := nat.choose_mul_succ_eq n k,
      have := nat.succ_mul_choose_eq n k,
      repeat {rw nat.succ_eq_add_one at *},
      linarith },
end

lemma hermite_explicit_recur (n k : ℕ) : hermite_explicit (n + 1) (k + 1) =
hermite_explicit n k - (k + 2) * hermite_explicit n (k + 2) :=
begin
  simp only [hermite_explicit],
  rw (by simp : (n + 1 - (k + 1) = n - k)),
  have hnk : even (n - k) ∨ odd (n - k), from nat.even_or_odd (n - k),
  cases hnk,
  {
  have hnk₁ : even (n - (k + 2)),
  { rw ← nat.sub_sub,
    rw nat.even_sub,
    { split, 
      exact λ x, even_two,
      exact λ x, hnk },
    sorry },
  repeat { rw if_pos hnk },
  rw if_pos hnk₁,
  -- rw (by {rw ← nat.sub_sub, ring} : ((n - (k + 2))/2 = (n - k)/2 - 1)),
  sorry
  },
  {
  have hnk₂ : odd (n - (k + 2)),
  { rw ← nat.sub_sub,
    rw nat.odd_sub,
    { split,
      exact λ x, even_two,
      exact λ x, hnk },
    sorry },
  rw nat.odd_iff_not_even at *,
  repeat { rw if_neg hnk },
  rw if_neg hnk₂,
  simp
  }
end

lemma hermite_explicit_eq_coeff (n k : ℕ) : hermite_explicit n k = coeff (hermite n) k :=
begin
  induction n with n ih;
  sorry
end