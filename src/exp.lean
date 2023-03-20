import analysis.special_functions.exp
import analysis.special_functions.exp_deriv
import basic
open polynomial

open set filter

noncomputable theory

@[simp]
def x_sub_dx_fn (f : ℝ → ℝ) :=
id * f - deriv f

lemma x_sub_dx_fn_def (f : ℝ → ℝ) : x_sub_dx_fn f = id * f - deriv f := rfl

lemma x_sub_dx_fn_apply (f : ℝ → ℝ) (x : ℝ) :
x_sub_dx_fn f x = x * f x - deriv f x := rfl

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
lemma hermite_zero : hermite 0 = C 1 := rfl

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

lemma hermite_eq_exp (n : ℕ) :
(λ x, eval x (hermite n)) = hermite_exp n :=
begin
  induction n with n ih,
  { simp, },
  { rw [hermite_exp_succ, hermite_succ, ← ih],
    apply eval_x_sub_dx_eq, },
end

lemma hermite_eq_exp_apply : ∀ (n : ℕ) (x : ℝ), eval x (hermite n) = (hermite_exp n) x :=
λ n x, congr_fun (hermite_eq_exp n) x