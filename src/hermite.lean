import analysis.calculus.mean_value
import analysis.special_functions.exp
import analysis.special_functions.exp_deriv
import data.nat.factorial.basic
import data.nat.choose.basic
open polynomial

open set filter

noncomputable theory

@[simp]
def x_sub_dx (p : polynomial ℝ) :=
X * p - p.derivative

lemma x_sub_dx_def (p : polynomial ℝ) : x_sub_dx p = X*p - p.derivative := rfl

lemma x_sub_dx_apply (p : polynomial ℝ) (x : ℝ) :
eval x (x_sub_dx p) = x*(eval x p) - (eval x (derivative p)) := by simp



@[simp]
def x_sub_dx_fn (f : ℝ → ℝ) :=
id * f - deriv f

lemma x_sub_dx_fn_def (f : ℝ → ℝ) : x_sub_dx_fn f = id * f - deriv f := rfl

lemma x_sub_dx_fn_apply (f : ℝ → ℝ) (x : ℝ) :
x_sub_dx_fn f x = x * f x - deriv f x := rfl



@[simp]
def hermite (n : ℕ) : polynomial ℝ :=
nat.iterate x_sub_dx n 1

lemma hermite_succ (n : ℕ) : hermite n.succ = x_sub_dx (hermite n) :=
begin
  simp only [hermite],
  rw function.iterate_succ' x_sub_dx n,
end



def gaussian : ℝ → ℝ := λ x, real.exp (-(x^2 / 2))

def inv_gaussian : ℝ → ℝ := λ x, real.exp (x^2 / 2)


lemma inv_gaussian_mul_gaussian (x : ℝ) : inv_gaussian x * gaussian x = 1 :=
by rw [gaussian, inv_gaussian, ← real.exp_add, add_neg_self, real.exp_zero]


lemma deriv_gaussian (x : ℝ) : deriv gaussian x = -x * gaussian x :=
by simp [gaussian, mul_comm]

lemma deriv_inv_gaussian (x : ℝ) : deriv inv_gaussian x = x * inv_gaussian x :=
by simp [inv_gaussian, mul_comm]

lemma cont_diff_gaussian : cont_diff ℝ ⊤ gaussian :=
((cont_diff_id.pow 2).div_const 2).neg.exp

lemma cont_diff.iterated_deriv :
∀ (n : ℕ) (f : ℝ → ℝ) (hf : cont_diff ℝ ⊤ f), cont_diff ℝ ⊤ (deriv^[n] f)
| 0     f hf := hf
| (n+1) f hf := cont_diff.iterated_deriv n (deriv f) (cont_diff_top_iff_deriv.mp hf).2


@[simp]
def hermite_exp (n : ℕ) : ℝ → ℝ :=
λ x, (-1)^n * (inv_gaussian x) * (deriv^[n] gaussian x)

lemma hermite_exp_def (n : ℕ) : 
hermite_exp n = λ x, (-1)^n * (inv_gaussian x) * (deriv^[n] gaussian x) := rfl

lemma hermite_exp_succ (n : ℕ) : hermite_exp (n + 1) = x_sub_dx_fn (hermite_exp n) :=
begin
  ext,
  simp only [hermite_exp, x_sub_dx_fn, function.iterate_succ', function.comp_app,
             id.def, pi.mul_apply, pi.sub_apply, pow_succ],
  rw [deriv_mul, deriv_const_mul, deriv_inv_gaussian],
  ring,
  { simp [inv_gaussian] },
  { simp [inv_gaussian] },
  { apply (cont_diff_top_iff_deriv.mp (cont_diff.iterated_deriv _ _ cont_diff_gaussian)).1 },
end

lemma exp_mul_exp_neg_eq_one (x : ℝ) : real.exp(x) * real.exp(-x) = 1 :=
begin
  rw real.exp_neg,
  apply (mul_inv_eq_one₀ (real.exp_ne_zero (x))).mpr,
  refl,
end

@[simp]
lemma hermite_zero : hermite 0 = C 1 :=
begin
  refl,
end

@[simp]
lemma hermite_one : hermite 1 = X :=
begin
  rw [hermite_succ, x_sub_dx_def],
  simp only [hermite_zero, map_one, mul_one, derivative_one, sub_zero],
end

@[simp]
lemma hermite_exp_zero : hermite_exp 0 = (λ x, 1) :=
begin
  ext,
  simp [hermite_exp, inv_gaussian, gaussian, exp_mul_exp_neg_eq_one]
end


lemma eval_x_sub_dx_eq (p : polynomial ℝ) :
(λ (x : ℝ), eval x (x_sub_dx p)) = x_sub_dx_fn (λ (x : ℝ), eval x p) :=
begin
  ext, simp,
end

lemma hermite_eq_hermite_exp (n : ℕ) :
(λ x, eval x (hermite n)) = hermite_exp n :=
begin
  induction n with n ih,
  { simp, },
  { rw [hermite_exp_succ, hermite_succ, ← ih],
    apply eval_x_sub_dx_eq, },
end

lemma hermite_zero_zero : coeff (hermite 0) 0 = 1 := coeff_one_zero

lemma hermite_one_zero : coeff (hermite 1) 0 = 0 :=
begin
  rw hermite_one,
  exact coeff_X_zero,
end

lemma hermite_one_one : coeff (hermite 1) 1 = 1 :=
begin
  rw hermite_one,
  exact coeff_X_one,
end

lemma x_sub_dx_coeff (p : polynomial ℝ) (k : ℕ) :
coeff (x_sub_dx p) k = coeff (X*p) k - coeff (p.derivative) k :=
begin
  simp,
end

#check x_sub_dx_coeff

lemma hermite_recur_coeff (n k : ℕ) :
coeff (hermite (n + 1)) (k + 1) = coeff (hermite n) k - (k+2)*(coeff (hermite n) (k+2)) :=
begin
  rw [hermite_succ, x_sub_dx_coeff, coeff_X_mul, coeff_derivative, mul_comm],
  suffices : ((k+1 : ℕ) : ℝ) + 1 = k + 2,
  { rw this, },
  { simp only [nat.cast_add, nat.cast_one],
    ring, },
end

lemma hermite_recur_coeff_two (n k : ℕ) :
coeff (hermite (n + 2)) (k + 2) = coeff (hermite n) k - (2*k + 5) * (coeff (hermite n) (k + 2))
+ (k + 3) * (k + 4) * (coeff (hermite n) (k + 4)) :=
begin
  repeat {rw hermite_recur_coeff},
  -- generalize : coeff (hermite n) k = A,
  -- generalize : coeff (hermite n) (k + 2) = B,
  -- generalize : coeff (hermite n) (k + 4) = C,
  simp only [algebra_map.coe_one, nat.cast_add],
  ring,
end

lemma hermite_upper_coeff_zero (n k : ℕ) : coeff (hermite n) (n+k+1) = 0 :=
begin
  induction n with n ih generalizing k,
  { apply coeff_C },
  {  rw [hermite_recur_coeff,
      (by linarith : n + 1 + k = n + k + 1),
      (by linarith : n + k + 1 + 2 = n + (k + 2) + 1),
      ih k, ih (k+2), mul_zero, sub_zero] }
end

lemma hermite_upper_coeff_zero' (n k : ℕ) (hnk : n < k) : coeff (hermite n) k = 0 :=
begin
  obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_lt hnk,
  apply hermite_upper_coeff_zero
end

lemma hermite_top_coeff (n : ℕ) : coeff (hermite n) n = 1 :=
begin
  induction n with n ih,
  { apply coeff_C },
  { rw [hermite_recur_coeff, ih, hermite_upper_coeff_zero, mul_zero, sub_zero] }
end

lemma hermite_recur_coeff_zero (n : ℕ) :
coeff (hermite (n + 1)) 0 = -(coeff (hermite n) 1) :=
begin
rw [hermite_succ, x_sub_dx_def, coeff_sub, coeff_X_mul_zero, coeff_derivative, zero_sub, zero_add],
  suffices : ((0 : ℕ) + 1 : ℝ) = 1,
  { rw [this, mul_one] },
  { rw [nat.cast_zero, zero_add] }
end

lemma hermite_recur_coeff_zero_two (n : ℕ) :
coeff (hermite (n + 2)) 0 = 2 * (coeff (hermite n) 2) - (coeff (hermite n) 0) :=
begin
  rw [hermite_recur_coeff_zero, hermite_recur_coeff],
  simp
end



lemma eval_x_sub_dx_eq_fn (p : polynomial ℝ) (f : ℝ → ℝ) (h : (λ x, eval x p) = f) (x : ℝ) :
(λ x, (eval x (x_sub_dx p))) = x_sub_dx_fn f :=
by rw [eval_x_sub_dx_eq, h]

lemma hermite_eq_exp : ∀ (n : ℕ) (x : ℝ), eval x (hermite n) = (hermite_exp n) x :=
begin
  intro n,
  induction n with n ih,
  { simp [hermite_zero, hermite_exp_zero] },
  { rw [hermite_succ, hermite_exp_succ],
    intro x,
    have h : (λ (x : ℝ), eval x (hermite n)) = hermite_exp n,
    { ext z,
      exact ih z, },
    rw ← eval_x_sub_dx_eq_fn (hermite n) (hermite_exp n) h x }
end

@[simp]
def double_factorial : ℕ → ℕ
| 0 := 1
| 1 := 1
| (k+2) := (k+2) * double_factorial k

notation n `‼` := double_factorial n -- this is \!! not two !'s
localized "notation (name := nat.factorial) n `!`:10000 := nat.factorial n" in nat

-- a _ 2n, 2k
@[simp]
def hermite_coeff_explicit_even (n k : ℕ) : ℝ := (-1)^(n - k) * double_factorial (2*n - 2*k - 1) * nat.choose (2*n) (2*k)

lemma hermite_coeff_explicit_even_zero_zero : hermite_coeff_explicit_even 0 0 = 1 := by simp

lemma hermite_coeff_explicit_even_one_one : hermite_coeff_explicit_even 1 1 = 1 := by simp

#check nat.choose

lemma hermite_coeff_explicit_even_upper_zero (n k : ℕ) : hermite_coeff_explicit_even n (n+k+1) = 0 :=
begin
  induction n with n ih,
  { unfold hermite_coeff_explicit_even,
    rw mul_zero,
    norm_num,
    refl },
  { sorry }
end

-- a _ 2n+1, 2k+1
@[simp]
def hermite_coeff_explicit_odd (n k : ℕ) : ℝ := (-1)^(n - k) * double_factorial (2*n - 2*k - 1) * nat.choose (2*n + 1) (2*k + 1)

#eval hermite_coeff_explicit_odd 3 2
#check hermite_recur_coeff

lemma odd_of_odd_add_even (n k : ℕ) : odd (n + k) → even k → odd n :=
begin
  intros hnk hk,
  exact (nat.odd_add.mp hnk).mpr hk
end

lemma add_two_of_succ_add_succ (n k : ℕ) : (n.succ + k.succ) = (n + k + 2) :=
begin
  repeat {rw ← nat.add_one},
  ring
end

lemma hermite_coeff_odd_zero (n k : ℕ) : odd (n + k) → coeff (hermite n) k = 0 :=
begin
  induction n with n ih generalizing k,
  { intro h,
    rw zero_add at h,
    apply hermite_upper_coeff_zero',
    cases k,
    { exfalso,
      exact nat.even_iff_not_odd.mp (even_zero) h },
    { exact ne_zero.pos (nat.succ k) } },
  { intro h,
    induction k with k ihk,
    { rw hermite_recur_coeff_zero,
      rw [ih 1 h, neg_zero] },
    { rw hermite_recur_coeff,
      rw ih k (odd_of_odd_add_even (n+k) 2 (by rwa add_two_of_succ_add_succ at h) (even_two)),
      rw ih (k+2) (by rwa [add_two_of_succ_add_succ, add_assoc] at h),
      ring }
  }
end

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
    { sorry
      -- norm_num,
      -- rw [zero_add, ← nat.add_one, add_comm, ← add_assoc],
      -- rw hermite_coeff_explicit_even_upper_zero _ _, 
      } },
  { sorry } -- unfold, use properties of bin coefficient and !!, rw cast
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
    { 
      repeat {rw nat.mul_succ},
      rw hermite_recur_coeff_two (2*n) (2*k),
      rw hermite_coeff_explicit_recur_even,
      repeat {rw ihn _},
      -- simp only [nat.cast_id, nat.cast_mul], 
      -- simp only [mul_add, mul_one],
      generalize : hermite (2 * n) = f,
      generalize : coeff = g,

      sorry } }
end

lemma hermite_coeff_eq_explicit_odd (n k : ℕ) : hermite_coeff_explicit_odd n k = coeff (hermite (2*n + 1)) (2*k + 1) := sorry

-- (2m)! = 2^m * m! * (2m - 1)!!

lemma hermite_appell : ∀ n : ℕ, derivative (hermite (n+1)) = (n+1) * (hermite n) :=
begin
  intro n,
  induction n with n ih,
  { rw [hermite_zero, hermite_one],
    simp },
  { rw hermite_succ,
    sorry }
end

#eval (0-1) !!