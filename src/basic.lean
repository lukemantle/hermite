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

@[simp]
def hermite (n : ℕ) : polynomial ℝ :=
nat.iterate x_sub_dx n 1

lemma hermite_succ (n : ℕ) : hermite n.succ = x_sub_dx (hermite n) :=
begin
  simp only [hermite],
  rw function.iterate_succ' x_sub_dx n,
end