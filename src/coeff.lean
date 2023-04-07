import data.nat.parity
import basic

open polynomial

noncomputable theory

@[simp] lemma hermite_zero_zero : coeff (hermite 0) 0 = 1 := coeff_one_zero
@[simp] lemma hermite_one_zero : coeff (hermite 1) 0 = 0 := by rw [hermite_one, coeff_X_zero]
@[simp] lemma hermite_one_one : coeff (hermite 1) 1 = 1 := by rw [hermite_one, coeff_X_one]

lemma hermite_coeff_recur_zero (n : ℕ) :
  coeff (hermite (n + 1)) 0 = -(coeff (hermite n) 1) := by simp [coeff_derivative]

lemma hermite_coeff_recur (n k : ℕ) :
  coeff (hermite (n + 1)) (k + 1) = coeff (hermite n) k - (k + 2) * (coeff (hermite n) (k + 2)) :=
begin
  rw [hermite_succ, coeff_sub, coeff_X_mul, coeff_derivative, mul_comm],
  norm_cast
end

lemma hermite_coeff_upper (n k : ℕ) : coeff (hermite n) (n + k + 1) = 0 :=
begin
  induction n with n ih generalizing k,
  { apply coeff_C },
  {  rw [hermite_coeff_recur,
      (by linarith : n + 1 + k = n + k + 1),
      (by linarith : n + k + 1 + 2 = n + (k + 2) + 1),
      ih k, ih (k + 2), mul_zero, sub_zero] }
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

lemma hermite_coeff_odd_zero (n k : ℕ) (hnk : odd (n + k)) : coeff (hermite n) k = 0 :=
begin
  induction n with n ih generalizing k,
  { rw zero_add at hnk,
    exact hermite_coeff_upper' _ _ hnk.pos },
  { cases k,
    { rw [hermite_coeff_recur_zero, ih 1 hnk, neg_zero] },
    { rw [hermite_coeff_recur, ih k _, ih (k + 2) _, mul_zero, sub_zero],
      { rwa (by simp [nat.succ_add, nat.add_succ] : n.succ + k.succ = n + (k + 2)) at hnk },
      { rw (by rw [nat.succ_add, nat.add_succ] : n.succ + k.succ = n + k + 2) at hnk,
        exact (nat.odd_add.mp hnk).mpr even_two }}}
end