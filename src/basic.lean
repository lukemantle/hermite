/-
Copyright (c) 2023 Luke Mantle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Luke Mantle.
-/

import analysis.calculus.deriv
open polynomial
open set filter

/-!
# Hermite polynomials

This file defines `hermite n`, the nth probabilist's Hermite polynomial.

## Main definitions

* `x_sub_dx`  : the operation `(x - d/dx)` used to recursively define the Hermite polynomials
* `hermite n` : the nth probabilist's Hermite polynomial, defined as a `polynomial ℝ`, using
                `x_sub_dx` recursively

## Notation

## References

-/

noncomputable theory

/-- the operation `(x - d/dx)` defined for `polynomial ℝ` -/
@[simp]
def x_sub_dx (p : polynomial ℝ) :=
X * p - p.derivative

lemma x_sub_dx_def (p : polynomial ℝ) : x_sub_dx p = X*p - p.derivative := rfl

lemma x_sub_dx_apply (p : polynomial ℝ) (x : ℝ) :
eval x (x_sub_dx p) = x*(eval x p) - (eval x (derivative p)) := by simp

/-- the nth probabilist's Hermite polynomial -/
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