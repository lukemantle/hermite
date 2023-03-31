import analysis.calculus.mean_value
import data.nat.factorial.basic
import data.nat.choose.basic
import basic
import exp
open polynomial

open set filter

noncomputable theory

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
coeff (x_sub_dx p) k = coeff (X*p) k - coeff (p.derivative) k := by simp

lemma hermite_coeff_recur (n k : ℕ) :
coeff (hermite (n + 1)) (k + 1) = coeff (hermite n) k - (k+2)*(coeff (hermite n) (k+2)) :=
begin
  rw [hermite_succ, x_sub_dx_coeff, coeff_X_mul, coeff_derivative, mul_comm],
  suffices : ((k+1 : ℕ) : ℝ) + 1 = k + 2,
  { rw this, },
  { simp only [nat.cast_add, nat.cast_one],
    ring, },
end

lemma hermite_coeff_upper (n k : ℕ) : coeff (hermite n) (n+k+1) = 0 :=
begin
  induction n with n ih generalizing k,
  { apply coeff_C },
  {  rw [hermite_coeff_recur,
      (by linarith : n + 1 + k = n + k + 1),
      (by linarith : n + k + 1 + 2 = n + (k + 2) + 1),
      ih k, ih (k+2), mul_zero, sub_zero] }
end

lemma hermite_coeff_upper' (n k : ℕ) (hnk : n < k) : coeff (hermite n) k = 0 :=
begin
  obtain ⟨k, rfl⟩ := nat.exists_eq_add_of_lt hnk,
  apply hermite_coeff_upper
end

lemma hermite_coeff_top (n : ℕ) : coeff (hermite n) n = 1 :=
begin
  induction n with n ih,
  { apply coeff_C },
  { rw [hermite_coeff_recur, ih, hermite_coeff_upper, mul_zero, sub_zero] }
end

lemma hermite_coeff_recur_zero (n : ℕ) :
coeff (hermite (n + 1)) 0 = -(coeff (hermite n) 1) :=
begin
  rw [hermite_succ, x_sub_dx_def, coeff_sub, coeff_X_mul_zero, coeff_derivative, zero_sub, zero_add],
  norm_num
end

lemma hermite_coeff_odd_zero (n k : ℕ) : odd (n + k) → coeff (hermite n) k = 0 :=
begin
  induction n with n ih generalizing k,
  { intro h,
    rw zero_add at h,
    apply hermite_coeff_upper',
    cases k,
    { exfalso,
      exact nat.even_iff_not_odd.mp (even_zero) h },
    { exact ne_zero.pos (nat.succ k) } },
  { intro h,
    induction k with k ihk,
    { rw hermite_coeff_recur_zero,
      rw [ih 1 h, neg_zero] },
    { rw [hermite_coeff_recur, ih k, ih (k+2)],
      { ring },
      { rwa (by simp [nat.succ_add, nat.add_succ] : n.succ + k.succ = n + (k + 2)) at h },
      { rw (by simp [nat.succ_add, nat.add_succ] : n.succ + k.succ = n + k + 2) at h,
        exact (nat.odd_add.mp h).mpr even_two }}}
end