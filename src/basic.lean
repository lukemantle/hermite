/-
Copyright (c) 2023 Luke Mantle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Mantle
-/

import data.polynomial.derivative
import data.nat.parity

/-!
# Hermite polynomials

This file defines `polynomial.hermite n`, the nth probabilist's Hermite polynomial.

## Main definitions

* `polynomial.hermite n`: the `n`th probabilist's Hermite polynomial,
  defined recursively as a `polynomial ℤ`

## References

* [Hermite Polynomials](https://en.wikipedia.org/wiki/Hermite_polynomials)

-/

noncomputable theory
open polynomial

namespace polynomial

/-- the nth probabilist's Hermite polynomial -/
noncomputable def hermite : ℕ → polynomial ℤ
| 0     := 1
| (n+1) := X * (hermite n) - (hermite n).derivative

@[simp] lemma hermite_succ (n : ℕ) : hermite (n+1) = X * (hermite n) - (hermite n).derivative :=
by rw hermite

lemma hermite_eq_iterate (n : ℕ) : hermite n = ((λ p, X*p - p.derivative)^[n] 1) :=
begin
  induction n with n ih,
  { refl },
  { rw [function.iterate_succ_apply', ← ih, hermite_succ] }
end

@[simp] lemma hermite_zero : hermite 0 = C 1 := rfl

@[simp] lemma hermite_one : hermite 1 = X :=
begin
  rw [hermite_succ, hermite_zero],
  simp only [map_one, mul_one, derivative_one, sub_zero]
end

/-!
### Lemmas about `polynomial.coeff`

## Main definitions

* `polynomial.coeff_hermite_of_odd_add`: for `n`,`k` where `n+k` is odd, `(hermite n).coeff k` is
  zero.
* `monic_hermite`: for all `n`, `hermite n` is monic.

-/

section coeff

lemma coeff_hermite_succ_zero (n : ℕ) :
  coeff (hermite (n + 1)) 0 = -(coeff (hermite n) 1) := by simp [coeff_derivative]

lemma coeff_hermite_succ_succ (n k : ℕ) :
  coeff (hermite (n + 1)) (k + 1) = coeff (hermite n) k - (k + 2) * (coeff (hermite n) (k + 2)) :=
begin
  rw [hermite_succ, coeff_sub, coeff_X_mul, coeff_derivative, mul_comm],
  norm_cast
end

lemma coeff_hermite_of_lt {n k : ℕ} (hnk : n < k) : coeff (hermite n) k = 0 :=
begin
  obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_lt hnk,
  clear hnk,
  induction n with n ih generalizing k,
  { apply coeff_C },
  { have : n + k + 1 + 2 = n + (k + 2) + 1 := by ring,
    rw [nat.succ_eq_add_one, coeff_hermite_succ_succ, add_right_comm, this, ih k, ih (k + 2),
      mul_zero, sub_zero] }
end

@[simp] lemma coeff_hermite_self (n : ℕ) : coeff (hermite n) n = 1 :=
begin
  induction n with n ih,
  { apply coeff_C },
  { rw [coeff_hermite_succ_succ, ih, coeff_hermite_of_lt, mul_zero, sub_zero],
    simp }
end

@[simp] lemma degree_hermite (n : ℕ) : (hermite n).degree = n :=
begin
  rw degree_eq_of_le_of_coeff_ne_zero,
  simp_rw [degree_le_iff_coeff_zero, with_bot.coe_lt_coe],
  { intro m,
    exact coeff_hermite_of_lt },
  { simp [coeff_hermite_self n] }
end

@[simp] lemma nat_degree_hermite {n : ℕ} : (hermite n).nat_degree = n :=
nat_degree_eq_of_degree_eq_some (degree_hermite n)

@[simp] lemma leading_coeff_hermite (n : ℕ) : (hermite n).leading_coeff = 1 :=
begin
  rw [← coeff_nat_degree, nat_degree_hermite, coeff_hermite_self],
end

lemma hermite_monic (n : ℕ) : (hermite n).monic := leading_coeff_hermite n

lemma coeff_hermite_of_odd_add {n k : ℕ} (hnk : odd (n + k)) : coeff (hermite n) k = 0 :=
begin
  induction n with n ih generalizing k,
  { rw zero_add at hnk,
    exact coeff_hermite_of_lt hnk.pos },
  { cases k,
    { rw nat.succ_add_eq_succ_add at hnk,
      rw [coeff_hermite_succ_zero, ih hnk, neg_zero] },
    { rw [coeff_hermite_succ_succ, ih, ih, mul_zero, sub_zero],
      { rwa [nat.succ_add_eq_succ_add] at hnk },
      { rw (by rw [nat.succ_add, nat.add_succ] : n.succ + k.succ = n + k + 2) at hnk,
        exact (nat.odd_add.mp hnk).mpr even_two }}}
end

lemma hermite_comp_neg_X (n : ℕ) : (hermite n).comp (-X) = (-1)^n * hermite n :=
begin
  induction n  with n ih,
  { simp only [hermite_zero, eq_int_cast, algebra_map.coe_one, one_comp, pow_zero, mul_one] },
  have := (hermite n).derivative_comp (-X),
  -- equivalvent to `simp [ih, pow_succ, polynomial.derivative_pow] at this ⊢,`
  simp only [ih, pow_succ, polynomial.derivative_pow, hermite_succ, sub_comp, mul_comp, X_comp,
    neg_mul, one_mul, derivative_mul, derivative_neg, derivative_one, neg_zero, mul_zero,
    zero_mul, zero_add, derivative_X] at this ⊢,
  rw [sub_eq_add_neg, ← this],
  ring,
end

lemma coeff_comp_neg_X {R : Type} [comm_ring R] {p : polynomial R} (k : ℕ) :
  (p.comp (-X)).coeff k = (-1)^k * (p.coeff k) :=
begin
  rw [mul_comm, comp, eval₂, coeff_sum, (by simp : -(X : polynomial R) = C (-1) * X)],
  simp_rw [coeff_C_mul, mul_pow, ← C_pow, coeff_C_mul_X_pow],
  convert finset.sum_eq_single k _ _,
  { rw if_pos rfl },
  { assume b hbp hbk,
    rw [if_neg hbk.symm, mul_zero] },
  { assume hkp,
    rw [not_mem_support_iff.mp hkp, zero_mul] }
end

lemma neg_one_pow_eq_neg_of_odd_add (n k : ℕ) (h : odd (n+k)) : ((-1) : ℤ)^n = -((-1) : ℤ)^k :=
begin
  cases nat.even_or_odd n with hn hn,
  { rw [add_comm, nat.odd_add] at h,
    rw [even.neg_one_pow hn, odd.neg_one_pow],
    { simp },
    { exact h.mpr hn } },
  { rw nat.odd_add at h,
    rw [odd.neg_one_pow hn, even.neg_one_pow],
    exact h.mp hn }
end

lemma coeff_hermite_comp_neg_X (n k : ℕ) :
((hermite n).comp (-X)).coeff k = (-1)^n * (hermite n).coeff k :=
begin
  rw hermite_comp_neg_X,
  convert coeff_C_mul _,
  simp,
end

lemma coeff_hermite_of_odd_add' {n k : ℕ} (hnk : odd (n + k)) : coeff (hermite n) k = 0 :=
begin
  apply neg_eq_self_iff.mp _,
  repeat { apply_instance },
  { have H : (-1:ℤ)^k ≠ 0,
    { apply pow_ne_zero,
      rw neg_ne_zero,
      exact one_ne_zero },
    have h : (-1 : ℤ) ^ k = 0 ∨ (hermite n).coeff k = 0,
    { rw [← mul_eq_zero, ← neg_eq_self_iff, neg_mul_eq_neg_mul,
          ← neg_one_pow_eq_neg_of_odd_add n k hnk, ← coeff_hermite_comp_neg_X n k,
          (by rw polynomial.coeff_comp_neg_X :
          ((hermite n).comp (-X)).coeff k = (-1)^k * (hermite n).coeff k)] },
    cases h,
    { exfalso,
      exact H h },
    { rw h,
      simp } },
end

-- lemma coeff_hermite_comp_neg_X' (k n : ℕ) :
-- ((hermite n).comp (-X)).coeff k = (-1)^k * (hermite n).coeff k :=
-- begin
--   rw polynomial.coeff_comp_neg_X,
-- end

-- lemma coeff_hermite_of_odd_add' {n k : ℕ} (hnk : odd (n + k)) : coeff (hermite n) k = 0 :=
-- begin
--   apply neg_eq_self_iff.mp,
--   { have h₁ := coeff_hermite_comp_neg_X n k,
--     have h₂ := coeff_hermite_comp_neg_X' k n,
--     have h₃ := eq_neg_of_odd_add n k hnk,
--     have h₄ : (-1:ℤ)^k ≠ 0,
--     { apply pow_ne_zero,
--       rw neg_ne_zero,
--       exact one_ne_zero },
--     rw h₁ at h₂,
--     rw h₃ at h₂,
--     rw [← neg_mul_eq_neg_mul, neg_eq_self_iff, mul_eq_zero] at h₂,
--     cases h₂,
--     { exfalso,
--       exact h₄ h₂ },
--     { rw h₂,
--       simp } },
--   repeat { apply_instance },
-- end

-- lemma coeff_hermite_comp_neg_X (n k : ℕ) :
-- ((hermite n).comp (-X)).coeff k = (-1)^n * (hermite n).coeff k :=
-- begin
--   rw hermite_comp_neg_X,
--   convert coeff_C_mul _,
--   simp,
-- end

end coeff
end polynomial
