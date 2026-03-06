import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import ContourIntegral.ResidueTheorem

open Complex Topology MeasureTheory Filter Set Polynomial ContourIntegral

namespace Test3

/--
The specific complex integrand `1 / ((z^2 + 1)^2)`.
-/
noncomputable def integrand (z : ℂ) : ℂ := 1 / ((z ^ 2 + 1) ^ 2)

/--
The bottom-left corner `-R` of the rectangular contour used to integrate `integrand`.
-/
noncomputable def bottomLeft (R : ℝ) : ℂ := -R

/--
The top-right corner `R + R*I` of the rectangular contour used to integrate `integrand`.
-/
noncomputable def topRight (R : ℝ) : ℂ := R + R * I

lemma contour_integral (R : ℝ) (hR : 1 < R) :
    rectIntegral integrand (bottomLeft R) (topRight R) = ↑Real.pi / 2 := by
  let U : Set ℂ := {-I}ᶜ
  have hU_open : IsOpen U := isOpen_compl_singleton
  have hz_re : (bottomLeft R).re < I.re := by simp [bottomLeft]; linarith
  have hz_im : (bottomLeft R).im < I.im := by simp [bottomLeft]
  have hw_re : I.re < (topRight R).re := by simp [topRight]; linarith
  have hw_im : I.im < (topRight R).im := by simp [topRight]; linarith
  have h_filled : filledRect (bottomLeft R) (topRight R) ⊆ U := by
    rintro z hz contra
    have him : z.im = (-I).im := congrArg Complex.im contra
    simp only [neg_im, I_im] at him
    have hz_im_bounds := hz.2
    unfold bottomLeft topRight at hz_im_bounds
    simp only [neg_im, ofReal_im, neg_zero, add_im, mul_im, ofReal_re, I_im, mul_one, I_re,
      mul_zero, add_zero, zero_add, mem_uIcc] at hz_im_bounds
    rcases hz_im_bounds with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  let g : ℂ → ℂ := fun z ↦ 1 / ((z + I) ^ 2)
  have h_holo : DifferentiableOn ℂ g U := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.div (by fun_prop) (by fun_prop)
    intro contra
    rw [sq_eq_zero_iff] at contra
    have : z = -I := by linear_combination contra
    exact hz this
  have h_thm := residue_theorem_rect_pole g 2 I (bottomLeft R) (topRight R)
    hz_re hw_re hz_im hw_im U hU_open h_filled h_holo
  have h_f_eq : (fun x ↦ g x / (x - I) ^ 2) = integrand := by
    ext x
    rw [integrand]
    unfold g
    rw [div_div, ← mul_pow, ← sq_sub_sq, I_sq, sub_neg_eq_add]
  rw [h_f_eq] at h_thm
  have h_res : residue_pole g I 2 = -I / 4 := by
    simp [residue_pole, dslope_iter, g]
    field_simp
    norm_num
  rw [h_thm, h_res]
  have h_pi : 2 * ↑Real.pi * I * (-I / 4 : ℂ) = ↑Real.pi / 2 := by
    field_simp
    norm_num
  push_cast at h_pi ⊢
  exact h_pi


lemma norm_integrand_le {z : ℂ} {R : ℝ} (hR : 1 < R) (hz_norm : R ≤ ‖z‖) :
    ‖integrand z‖ ≤ 1 / ((R^2 - 1) ^ 2) := by
  unfold integrand
  have h_R_pos : 0 < R := by linarith
  rw [norm_div]
  have h1 : R^2 - 1 ≤ ‖z^2 + 1‖ := by
    calc R^2 - 1 ≤ ‖z‖^2 - 1 := by gcongr
    _ = ‖z^2‖ - 1 := by rw [norm_pow]
    _ ≤ ‖z^2 + 1‖ := by simpa [← norm_pow] using norm_sub_norm_le (z^2) (-1)
  have h3 : 0 < R^2 - 1 := by nlinarith
  norm_num
  gcongr

lemma tendsto_bound :
    Tendsto (fun R : ℝ ↦ R / ((R^2 - 1)^2)) atTop (𝓝 0) := by
  rw [← Asymptotics.isLittleO_iff_tendsto']
  · convert_to (X : ℝ[X]).eval =o[atTop] (X^4 - 2 * X^2 + 1 : ℝ[X]).eval
    · ext
      simp
    · ext
      simp
      ring
    apply Polynomial.isLittleO_atTop_of_degree_lt
    convert_to (1 : WithBot ℕ) < 4 <;> (try compute_degree) <;> (norm_num; try decide)
  · filter_upwards [eventually_gt_atTop 1] with R hR
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
    intro h
    nlinarith

lemma tendsto_integral_of_bound_isO
    (a b : ℝ → ℝ) (f : ℝ → ℝ → ℂ) (c : ℝ)
    (h_bound : ∀ᶠ R in atTop, ∀ t ∈ uIoc (a R) (b R), ‖f R t‖ ≤ 1 / ((R ^ 2 - 1) ^ 2))
    (h_len : ∀ᶠ R in atTop, |b R - a R| ≤ c * R) :
    Tendsto (fun R ↦ ∫ y in a R..b R, f R y) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
  · filter_upwards with R using norm_nonneg _
  · filter_upwards [h_bound, h_len, eventually_gt_atTop 2] with R hB hL hR2
    have h_norm_le := intervalIntegral.norm_integral_le_of_norm_le_const hB
    have h_denom_pos : 0 < R^2 - 1 := by nlinarith
    calc ‖∫ (y : ℝ) in a R..b R, f R y‖
      _ ≤ 1 / ((R^2 - 1)^2) * |b R - a R| := h_norm_le
      _ ≤ 1 / ((R^2 - 1)^2) * (c * R) := by gcongr
      _ = c * (R / ((R^2 - 1)^2)) := by ring
  · have : 𝓝 (0 : ℝ) = 𝓝 (c * 0) := by rw [mul_zero]
    rw [this]
    exact tendsto_bound.const_mul c

lemma limit_right_edge :
    Tendsto (fun R : ℝ ↦ ∫ y in 0..R, integrand (↑R + ↑y * I)) atTop (𝓝 0) := by
  apply tendsto_integral_of_bound_isO (fun _ ↦ 0) (fun R ↦ R) (fun R y ↦ integrand (↑R + ↑y * I)) 1
  · filter_upwards [eventually_gt_atTop 1] with R hR y hy
    apply norm_integrand_le hR
    calc R
    _ = |(R + y * I).re| := by rw [add_re, ofReal_re, re_ofReal_mul, I_re, mul_zero,
      add_zero, abs_of_pos (by linarith)]
    _ ≤ ‖R + y * I‖ := abs_re_le_norm _
  · filter_upwards [eventually_gt_atTop 0] with R hR
    rw [sub_zero, abs_of_pos hR, one_mul]

lemma limit_left_edge :
    Tendsto (fun R : ℝ ↦ ∫ y in 0..R, integrand (-↑R + ↑y * I)) atTop (𝓝 0) := by
  apply tendsto_integral_of_bound_isO (fun _ ↦ 0) (fun R ↦ R) (fun R y ↦ integrand (-↑R + ↑y * I)) 1
  · filter_upwards [eventually_gt_atTop 1] with R hR y hy
    apply norm_integrand_le hR
    calc R
    _ = |(-R + y * I).re| := by rw [add_re, neg_re, ofReal_re, re_ofReal_mul, I_re, mul_zero,
      add_zero, abs_of_neg (by linarith), neg_neg]
    _ ≤ ‖-R + y * I‖ := abs_re_le_norm _
  · filter_upwards [eventually_gt_atTop 0] with R hR
    rw [sub_zero, abs_of_pos hR, one_mul]

lemma limit_top_edge :
    Tendsto (fun R : ℝ ↦ ∫ x in -R..R, integrand (↑x + ↑R * I)) atTop (𝓝 0) := by
  apply tendsto_integral_of_bound_isO (fun R ↦ -R) (fun R ↦ R) (fun R x ↦ integrand (↑x + ↑R * I)) 2
  · filter_upwards [eventually_gt_atTop 1] with R hR x _
    apply norm_integrand_le hR
    calc R
    _ = |(x + R * I).im| := by rw [add_im, ofReal_im, im_ofReal_mul, I_im, mul_one, zero_add,
      abs_of_pos (by linarith)]
    _ ≤ ‖x + R * I‖ := abs_im_le_norm _
  · filter_upwards [eventually_gt_atTop 0] with R hR
    rw [sub_neg_eq_add, ← two_mul, abs_of_pos (by positivity)]

lemma limit_real_line :
    Tendsto (fun R : ℝ ↦ ∫ x in -R..R, integrand x) atTop (𝓝 (↑Real.pi / 2)) := by
  have h_eq : ∀ᶠ R : ℝ in atTop, ∫ x in -R..R, integrand x =
      (((↑Real.pi / 2 : ℂ) +
      ∫ x in -R..R, integrand (↑x + ↑R * I)) -
      I * ∫ y in 0..R, integrand (↑R + ↑y * I)) +
      I * ∫ y in 0..R, integrand (-↑R + ↑y * I) := by
    filter_upwards [eventually_gt_atTop 1] with R hR
    have h_cont := contour_integral R hR
    unfold rectIntegral bottomLeft topRight at h_cont
    simp only [neg_im, ofReal_im, neg_zero, ofReal_zero, zero_mul, add_zero, neg_re, ofReal_re,
      add_re, mul_re, I_re, mul_zero, I_im, mul_one, sub_self, smul_eq_mul, add_im, im_ofReal_mul,
      ofReal_neg, zero_add] at h_cont
    generalize ∫ x in -R..R, integrand x = A at h_cont ⊢
    generalize ∫ x in -R..R, integrand (↑x + ↑R * I) = B at h_cont ⊢
    generalize I * ∫ y in 0..R, integrand (↑R + ↑y * I) = C at h_cont ⊢
    generalize I * ∫ y in 0..R, integrand (-↑R + ↑y * I) = D at h_cont ⊢
    calc A
      _ = (A - B + C - D) + B - C + D := by ring
      _ = (↑Real.pi / 2 : ℂ) + B - C + D := by rw [h_cont]
  have h_lim := (((tendsto_const_nhds (x := (↑Real.pi / 2 : ℂ))).add
    limit_top_edge).sub (limit_right_edge.const_mul I)).add
    (limit_left_edge.const_mul I)
  have h_eq_symm : ∀ᶠ R : ℝ in atTop,
      (((↑Real.pi / 2 : ℂ) +
      ∫ x in -R..R, integrand (↑x + ↑R * I)) -
      I * ∫ y in 0..R, integrand (↑R + ↑y * I)) +
      I * ∫ y in 0..R, integrand (-↑R + ↑y * I) = ∫ x in -R..R, integrand x := by
    filter_upwards [h_eq] with R hR_eq
    exact hR_eq.symm
  simp only [mul_zero, add_zero, sub_zero] at h_lim
  exact Filter.Tendsto.congr' h_eq_symm h_lim

theorem integral_cpv_integrand : Tendsto (fun R : ℝ ↦ ∫ x in -R..R, 1 / ((x^2 + 1) ^ 2))
    atTop (𝓝 (Real.pi / 2)) := by
  have h_re := (continuous_re.tendsto (↑Real.pi / 2 : ℂ)).comp limit_real_line
  have h_RHS : (↑Real.pi / 2 : ℂ).re = Real.pi / 2 := by norm_cast
  rw [h_RHS] at h_re
  have h_LHS : (fun R : ℝ ↦ (∫ x in -R..R, integrand x).re) =
      (fun R : ℝ ↦ ∫ x in -R..R, 1 / ((x^2 + 1) ^ 2)) := by
    ext R
    have h_int : IntervalIntegrable (fun x : ℝ ↦ integrand x) volume (-R) R := by
      apply ContinuousOn.intervalIntegrable
      unfold integrand
      fun_prop (disch := intro x _; norm_cast; nlinarith)
    have h_comm : (∫ x in -R..R, integrand x).re = ∫ x in -R..R, (integrand x).re :=
      (ContinuousLinearMap.intervalIntegral_comp_comm reCLM h_int).symm
    rw [h_comm]
    apply intervalIntegral.integral_congr
    have h_re_eq (x : ℝ) : (integrand x).re = 1 / ((x^2 + 1) ^ 2) := by
      unfold integrand
      have h_denom : ((x : ℂ)^2 + 1) ^ 2 = (((x^2 + 1) ^ 2 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [h_denom]
      have h_div : 1 / (((x^2 + 1) ^ 2 : ℝ) : ℂ) =
          ((1 / ((x^2 + 1) ^ 2) : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [h_div, ofReal_re]
    intro x _
    exact h_re_eq x
  change Tendsto (fun R : ℝ ↦ (∫ x in -R..R, integrand x).re) atTop (𝓝 (Real.pi / 2)) at h_re
  rw [h_LHS] at h_re
  exact h_re

lemma integrand_integrable : Integrable (fun x : ℝ ↦ 1 / ((x^2 + 1) ^ 2)) := by
  have h_bound_integrable : Integrable (fun x : ℝ ↦ 1 / (x^2 + 1)) := by
    have h_eq : (fun x : ℝ ↦ 1 / (x^2 + 1)) = fun x ↦ (1 + x^2)⁻¹ := by ring_nf
    rw [h_eq]
    exact integrable_inv_one_add_sq
  apply h_bound_integrable.mono
  · apply Continuous.aestronglyMeasurable
    refine Continuous.div continuous_const (by fun_prop) ?_
    intro x
    nlinarith
  · filter_upwards with x
    have h1 : 0 < x^2 + 1 := by positivity
    simp only [norm_div, norm_one, Real.norm_eq_abs, abs_sq, abs_of_pos h1]
    gcongr
    nlinarith

theorem lebesgue_integral_integrand :
    ∫ x : ℝ, 1 / ((x^2 + 1) ^ 2) = Real.pi / 2 := by
  have h_CPV := integral_cpv_integrand
  have h_Lebesgue : Tendsto (fun R : ℝ ↦ ∫ x in -R..R, 1 / ((x^2 + 1) ^ 2))
      atTop (𝓝 (∫ x : ℝ, 1 / ((x^2 + 1) ^ 2))) := by
    apply intervalIntegral_tendsto_integral
    · exact integrand_integrable
    · exact tendsto_neg_atTop_atBot
    · exact tendsto_id
  exact tendsto_nhds_unique h_Lebesgue h_CPV

end Test3
