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

lemma double_factorial_def (n : ℕ) : double_factorial (n + 2) = (n + 2) * double_factorial n := rfl

lemma double_factorial_def' (n : ℕ) : (n+1) ‼ = (n+1) * (n-1)‼ := by { cases n; refl }

lemma succ_mul_choose_succ_eq (n k : ℕ) : (k+1) * (nat.choose n (k+1)) = (nat.choose n k) * (n - k) :=
begin
  cases n,
    { simp },
    { have := nat.choose_mul_succ_eq n k,
      have := nat.succ_mul_choose_eq n k,
      repeat {rw nat.succ_eq_add_one at *},
      linarith },
end

lemma neg_one_half_pow (n : ℕ) : (-1 : ℝ) ^ ((n + 2) / 2) = (-1) * (-1) ^ (n / 2) :=
begin
  rw [(by linarith : n+2 = n + 2 * 1), nat.add_mul_div_left, pow_add];
  simp
end

@[simp] -- a_{n, k}
def hermite_explicit (n k : ℕ) : ℝ :=
if (even (n-k)) then (-1)^((n-k)/2) * (n-k-1)‼ * nat.choose n k
else 0

lemma hermite_explicit_def (n k : ℕ) : hermite_explicit n k =
if (even (n-k)) then (-1)^((n-k)/2) * (n-k-1)‼ * nat.choose n k else 0 := rfl

@[simp] -- alt definition of a_{n+k, k}
def hermite_explicit' (n k : ℕ) : ℝ :=
if (even n) then (-1)^(n/2) * (n-1)‼ * nat.choose (n+k) k
else 0

lemma hermite_explicit_def' (n k : ℕ) : hermite_explicit' n k =
if (even n) then (-1)^(n/2) * (n-1)‼ * nat.choose (n+k) k else 0 := rfl

lemma hermite_explicit_eq_explicit' (n k : ℕ) :
  (if (even n) then (-1 : ℝ)^(n/2) * (n-1)‼ * nat.choose (n+k) k
  else 0) = (if (even n) then (-1 : ℝ)^(n/2) * (n-1)‼ * nat.choose (n+k) k
  else 0) := rfl

lemma hermite_explicit_upper (n k : ℕ) : hermite_explicit n (n + k + 1) = 0 :=
begin
  simp only [hermite_explicit],
  rw nat.choose_eq_zero_of_lt (by linarith : n < n + k + 1),
  simp
end

lemma hermite_explicit_upper' (n k : ℕ) (h : n < k) : hermite_explicit n k = 0 :=
begin
  obtain ⟨k', rfl⟩ := nat.exists_eq_add_of_lt h,
  apply hermite_explicit_upper,
end

lemma hermite_explicit'_recur (n k : ℕ) : hermite_explicit' (n + 2) (k + 1) =
hermite_explicit' (n + 2) k - (k + 2) * hermite_explicit' n (k + 2) :=
begin
  -- Simplify `even (n+2)` to `even n`
  simp only [hermite_explicit', nat.even_add, even_two, iff_true],
  split_ifs,
  { -- Some algebra rearrangement.
    rw [nat.add_succ_sub_one, mul_comm (↑k + _),
        (by linarith : n + 2 + (k + 1) = (n + 1) + (k + 1) + 1),
        (by linarith : n + 2 + k = (n + 1) + (k + 1)),
        (by linarith : n + (k + 2) = (n + 1) + (k + 1))],
    -- Factor out the (-1)'s.
    rw [neg_one_half_pow, sub_eq_add_neg],
    nth_rewrite 4 neg_eq_neg_one_mul,
    simp only [mul_assoc, ← mul_add],
    congr' 2,
    -- Factor out the factorials.
    norm_cast,
    rw [double_factorial_def', mul_comm (n + 1)],
    simp only [mul_assoc, ← mul_add],
    congr' 1,
    -- Factor out the binomial coefficients.
    rw [nat.choose, mul_add],
    have key : (k + 2) * _ = _ := succ_mul_choose_succ_eq (n+1 + (k+1)) (k+1),
    rw nat.add_sub_cancel at key,
    linarith },
  { -- The odd case (0 = 0 - 0)
    simp },
end

lemma hermite_explicit_recur_zero (n : ℕ) : hermite_explicit (n + 1) 0 = - hermite_explicit n 1 :=
begin
  cases n,
  { simp },
  { simp only [hermite_explicit, tsub_zero, nat.succ_sub_succ_eq_sub, eq_self_iff_true],
    rw (by ring : n.succ + 1 = n + 2),
    simp only [nat.even_add, even_two, iff_true],
    split_ifs,
  { rw [neg_one_half_pow, double_factorial_def', nat.choose_zero_right, nat.choose_one_right],
    simp [mul_one, mul_assoc, mul_comm, neg_mul],
    ring },
  { simp }}
end

lemma hermite_explicit_recur (n k : ℕ) : hermite_explicit (n + 1) (k + 1) =
hermite_explicit n k - (k + 2) * hermite_explicit n (k + 2):=
begin
  cases le_or_gt k n with h,
  { obtain ⟨n', rfl⟩ := nat.exists_eq_add_of_le h,
    rw [add_comm k n', add_assoc],
    repeat {rw hermite_explicit_eq_explicit'},
    cases n',
      { rw hermite_explicit_upper' (0 + k) (k + 2) (by linarith),
        simp [hermite_explicit'] },
      { cases n',
        { rw hermite_explicit_upper' (1 + k) (k + 2) (by linarith),
          simp [hermite_explicit'] },
        repeat {rw hermite_explicit_def},
        repeat {rw nat.add_sub_cancel},
        have h₁ : n'.succ.succ + k - (k + 2) = n',
        {simp [← nat.add_one, ← nat.sub_sub]},
        repeat {rw h₁},
        have h₂ : n'.succ.succ + k = n' + (k + 2),
        { repeat {rw ← nat.add_one},
          ring },
        nth_rewrite 1 h₂,
        repeat {rw ← hermite_explicit_def'}, 
        {apply hermite_explicit'_recur }}},
  { repeat {rw hermite_explicit_upper'};
    linarith }
end

lemma hermite_explicit'_recur_zero (n : ℕ) : hermite_explicit' (n + 2) 0 = -hermite_explicit' n 1 :=
begin
    -- Simplify `even (n+2)` to `even n`
  simp only [hermite_explicit', nat.even_add, even_two, iff_true],
  split_ifs,
  { rw neg_one_half_pow,
    nth_rewrite 2 neg_eq_neg_one_mul,
    rw [(by ring : n + 2 - 1 = n + 1), double_factorial_def'],
    simp only [mul_assoc],
    congr' 2,
    rw [nat.choose, nat.choose_zero_right,
        nat.choose_zero_right, nat.choose_one_right],
    norm_cast,
    simp [mul_one, add_comm, mul_comm] },
  { simp }
end

lemma hermite_explicit'_zero (k : ℕ) : hermite_explicit' 0 k = 1 := by simp

lemma hermite_explicit'_one (k : ℕ) : hermite_explicit' 1 k = 0 := by simp

lemma hermite_explicit_eq_coeff (n k : ℕ) : 
(if (even (n-k)) then (-1 : ℝ)^((n-k)/2) * (n-k-1)‼ * nat.choose n k else 0) = coeff (hermite n) k :=
begin
  induction n with n ih generalizing k,
  { cases k,
    { simp },
    { rw (by ring : k.succ = 0 + k + 1),
      rw [← hermite_explicit_def, hermite_explicit_upper, hermite_coeff_upper] }},
  { cases k,
    { rw [← hermite_explicit_def, hermite_explicit_recur_zero, hermite_coeff_recur_zero,
          hermite_explicit_def, ih 1] },
    { rw [← hermite_explicit_def, hermite_explicit_recur, hermite_coeff_recur],
      repeat { rw hermite_explicit_def },
      rw [ih k, ih (k+2)] }}
end

lemma hermite_explicit'_eq_coeff (n k : ℕ) : hermite_explicit' n k = coeff (hermite (n+k)) k :=
by rw [hermite_explicit_def', ← hermite_explicit_eq_coeff, nat.add_sub_cancel]