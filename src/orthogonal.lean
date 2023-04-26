import analysis.special_functions.gamma
import analysis.special_functions.polar_coord
import analysis.convex.complex
import analysis.normed.group.basic
import analysis.complex.cauchy_integral
import measure_theory.group.integration

open real set measure_theory filter asymptotics
open_locale real topology

-- lemma integral_polynomial_mul_deriv_gaussian_of_deg_lt
--   (p : polynomial ℝ) (n m : ℕ) (hp : n = p.nat_degree) (hnm : n < m) :
-- ∫ (x : ℝ), (λ x, p.eval (x:ℝ) * deriv^[m] real.exp (-(x:ℝ)^2 / 2)) = 0 := sorry

-- lemma integral_polynomial_mul_deriv_gaussian_of_deg_lt
--   (p : polynomial ℝ) (n m : ℕ) (hp : n = p.nat_degree) (hnm : n < m) :
-- ∫ (x : ℝ), p.eval x * (deriv^[m] (λ y, real.exp (-y^2 / 2)) x) = 0 := sorry

-- ∫ (x : ℝ), (λ x, p.eval (x:ℝ)) = 0 := sorry

#check tendsto

example (f : ℕ → ℝ) (x₀ : ℝ) (hf : ∀ n, f n = x₀): tendsto f at_top (𝓝 x₀) :=
begin
  apply tendsto_iff_eventually.mpr,
  intros p hpy,
  -- simp only [filter.eventually_at_top],
  -- squeeze_simp,
  sorry,
end

example (x₀ : ℝ) : tendsto (λ (x : ℝ), x) (𝓝 x₀) (𝓝 x₀) :=
begin
  -- simp only [tendsto_const_nhds_iff],
  apply tendsto_id,
end

example (c : ℝ) : tendsto (λ (x : ℝ), exp (-c * x)) at_top (𝓝 0) :=
begin
  apply tendsto_map'_iff.mp,
end

#check tendsto_map'_iff
#check tendsto_exp_neg_at_top_nhds_0
#check map_const


variables (c : ℝ)

#check has_mul.mul c