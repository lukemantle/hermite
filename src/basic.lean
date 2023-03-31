import analysis.calculus.mean_value
open polynomial

open set filter

noncomputable theory

@[simp]
def x_sub_dx (p : polynomial ℝ) :=
X * p - p.derivative

lemma x_sub_dx_def (p : polynomial ℝ) : x_sub_dx p = X*p - p.derivative := rfl

lemma x_sub_dx_apply (p : polynomial ℝ) (x : ℝ) :
eval x (x_sub_dx p) = x*(eval x p) - (eval x (derivative p)) := by simp

def hermite (n : ℕ) : polynomial ℝ :=
nat.iterate x_sub_dx n 1

@[simp]
lemma hermite_eq_iter (n : ℕ) : hermite n = nat.iterate x_sub_dx n 1 := rfl

@[simp]
lemma hermite_succ (n : ℕ) : hermite n.succ = x_sub_dx (hermite n) :=
begin
  simp only [hermite],
  rw function.iterate_succ' x_sub_dx n,
end

@[simp]
lemma hermite_zero : hermite 0 = C 1 := rfl

@[simp]
lemma hermite_one : hermite 1 = X :=
begin
  rw [hermite_succ, x_sub_dx_def],
  simp only [hermite_zero, map_one, mul_one, derivative_one, sub_zero],
end