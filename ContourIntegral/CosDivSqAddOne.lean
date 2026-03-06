import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import ContourIntegral.ResidueTheorem

open Complex Topology MeasureTheory Filter Set Polynomial ContourIntegral

namespace Test1

/--
The specific complex integrand `e^{itz} / (z^2 + 1)` used to evaluate
the improper integral `∫ cos(tx) / (x^2 + 1) dx`.
-/
noncomputable def integrand (t : ℝ) (z : ℂ) : ℂ := exp (I * t * z) / (z ^ 2 + 1)

/--
The bottom-left corner `-R` of the rectangular contour used to integrate `integrand`.
-/
noncomputable def bottomLeft (R : ℝ) : ℂ := -R

/--
The top-right corner `R + R*I` of the rectangular contour used to integrate `integrand`.
The height `R` is chosen so that `e^{itz}` decays sufficiently fast as `R → ∞`.
-/
noncomputable def topRight (R : ℝ) : ℂ := R + R * I

lemma contour_integral (t : ℝ) (R : ℝ) (hR : 1 < R) :
    rectIntegral (integrand t) (bottomLeft R) (topRight R) = ↑Real.pi * Real.exp (-t) := by
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
  let g : ℂ → ℂ := fun z ↦ Complex.exp (I * t * z) / (z + I)
  have h_holo : DifferentiableOn ℂ g U := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.div (by fun_prop) (by fun_prop)
    intro contra
    have : z = -I := by linear_combination contra
    exact hz this
  have h_thm := residue_theorem_rect_pole g 1 I (bottomLeft R) (topRight R)
    hz_re hw_re hz_im hw_im U hU_open h_filled h_holo
  have h_f_eq : (fun x ↦ g x / (x - I) ^ 1) = integrand t := by
    ext x
    simp only [pow_one, integrand]
    change Complex.exp (I * t * x) / (x + I) / (x - I) = Complex.exp (I * t * x) / (x^2 + 1)
    rw [div_div, ← sq_sub_sq, I_sq, sub_neg_eq_add]
  rw [h_f_eq] at h_thm
  have h_res : residue_pole g I 1 = g I := rfl
  have h_g_I : g I = Real.exp (-t) / (2 * I) := by
    change Complex.exp (I * t * I) / (I + I) = _
    rw [mul_comm, ← mul_assoc, I_mul_I, neg_one_mul]
    push_cast
    ring
  rw [h_thm, h_res, h_g_I]
  have h_pi : 2 * ↑Real.pi * I * (Real.exp (-t) / (2 * I) : ℂ) = ↑Real.pi * Real.exp (-t) := by
    rw [Real.exp_neg]
    push_cast
    field_simp
  push_cast at h_pi ⊢
  exact h_pi

lemma norm_integrand_le {t : ℝ} (ht : 0 ≤ t) {z : ℂ} {R : ℝ} (hR : 1 < R) (hz_im : 0 ≤ z.im)
    (hz_norm : R ≤ ‖z‖) : ‖integrand t z‖ ≤ 1 / (R^2 - 1) := by
  unfold integrand
  rw [norm_div]
  have h_num : ‖Complex.exp (I * t * z)‖ ≤ 1 := by
    rw [norm_exp]
    simp only [mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self, mul_im,
      one_mul, zero_add, zero_sub, Real.exp_le_one_iff, Left.neg_nonpos_iff]
    exact mul_nonneg ht hz_im
  have h_den : R^2 - 1 ≤ ‖z^2 + 1‖ := by
    calc R^2 - 1 ≤ ‖z‖^2 - 1 := by gcongr
    _ = ‖z^2‖ - 1 := by rw [norm_pow]
    _ ≤ ‖z^2 + 1‖ := by simpa [← norm_pow] using norm_sub_norm_le (z^2) (-1)
  have H1 : 0 < R^2 - 1 := by nlinarith
  have H2 : 0 < ‖z^2 + 1‖ := by nlinarith
  calc ‖Complex.exp (I * t * z)‖ / ‖z^2 + 1‖ ≤ 1 / (R^2 - 1) := by gcongr

lemma tendsto_bound : Tendsto (fun R : ℝ ↦ R / (R^2 - 1)) atTop (𝓝 0) := by
  rw [← Asymptotics.isLittleO_iff_tendsto']
  · convert_to (X : ℝ[X]).eval =o[atTop] (X^2 - 1 : ℝ[X]).eval
    · ext
      simp
    · ext
      simp
    apply Polynomial.isLittleO_atTop_of_degree_lt
    convert_to (1 : WithBot ℕ) < 2 <;> (try compute_degree) <;> (norm_num; try decide)
  · filter_upwards [eventually_gt_atTop 1] with R hR h_zero
    nlinarith

lemma tendsto_integral_of_bound_isO
    (a b : ℝ → ℝ) (f : ℝ → ℝ → ℂ) (c : ℝ)
    (h_bound : ∀ᶠ R in atTop, ∀ t ∈ uIoc (a R) (b R), ‖f R t‖ ≤ 1 / (R ^ 2 - 1))
    (h_len : ∀ᶠ R in atTop, |b R - a R| ≤ c * R) :
    Tendsto (fun R ↦ ∫ y in a R..b R, f R y) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
  · filter_upwards with R using norm_nonneg _
  · filter_upwards [h_bound, h_len, eventually_gt_atTop 1] with R hB hL hR1
    have h_norm_le := intervalIntegral.norm_integral_le_of_norm_le_const hB
    have h_denom_pos : 0 < R^2 - 1 := by nlinarith
    calc ‖∫ (y : ℝ) in a R..b R, f R y‖
      _ ≤ 1 / (R^2 - 1) * |b R - a R| := h_norm_le
      _ ≤ 1 / (R^2 - 1) * (c * R) := by gcongr
      _ = c * (R / (R^2 - 1)) := by ring
  · have : 𝓝 (0 : ℝ) = 𝓝 (c * 0) := by rw [mul_zero]
    rw [this]
    exact tendsto_bound.const_mul c

lemma limit_right_edge {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun R : ℝ ↦ ∫ (y : ℝ) in 0..R, integrand t (↑R + ↑y * I)) atTop (𝓝 0) := by
  apply tendsto_integral_of_bound_isO (fun _ ↦ 0) (fun R ↦ R)
    (fun R y ↦ integrand t (↑R + ↑y * I)) 1
  · filter_upwards [eventually_gt_atTop 1] with R hR y hy
    apply norm_integrand_le ht hR
    · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add]
      rw [mem_uIoc] at hy
      rcases hy with ⟨hy1, _⟩ | ⟨_, hy2⟩ <;> linarith
    · calc R
      _ = |(R + y * I).re| := by rw [add_re, ofReal_re, re_ofReal_mul, I_re, mul_zero,
        add_zero, abs_of_pos (by linarith)]
      _ ≤ ‖R + y * I‖ := abs_re_le_norm _
  · filter_upwards [eventually_gt_atTop 0] with R hR
    rw [sub_zero, abs_of_pos hR, one_mul]

lemma limit_left_edge {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun R : ℝ ↦ ∫ (y : ℝ) in 0..R, integrand t (-↑R + ↑y * I)) atTop (𝓝 0) := by
  apply tendsto_integral_of_bound_isO (fun _ ↦ 0) (fun R ↦ R)
    (fun R y ↦ integrand t (-↑R + ↑y * I)) 1
  · filter_upwards [eventually_gt_atTop 1] with R hR y hy
    apply norm_integrand_le ht hR
    · simp only [add_im, neg_im, ofReal_im, neg_zero, mul_im, ofReal_re, I_im, mul_one, I_re,
        mul_zero, add_zero, zero_add]
      rw [mem_uIoc] at hy
      rcases hy with ⟨hy1, _⟩ | ⟨_, hy2⟩ <;> linarith
    · calc R
      _ = |(-R + y * I).re| := by rw [add_re, neg_re, ofReal_re, re_ofReal_mul, I_re,
        mul_zero, add_zero, abs_of_neg (by linarith), neg_neg]
      _ ≤ ‖-R + y * I‖ := abs_re_le_norm _
  · filter_upwards [eventually_gt_atTop 0] with R hR
    rw [sub_zero, abs_of_pos hR, one_mul]

lemma limit_top_edge {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun R : ℝ ↦ ∫ (x : ℝ) in -R..R, integrand t (↑x + ↑R * I)) atTop (𝓝 0) := by
  apply tendsto_integral_of_bound_isO (fun R ↦ -R) (fun R ↦ R)
    (fun R x ↦ integrand t (↑x + ↑R * I)) 2
  · filter_upwards [eventually_gt_atTop 1] with R hR x _
    apply norm_integrand_le ht hR
    · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add]
      linarith
    · calc R
      _ = |(x + R * I).im| := by rw [add_im, ofReal_im, im_ofReal_mul, I_im, mul_one, zero_add,
        abs_of_pos (by linarith)]
      _ ≤ ‖x + R * I‖ := abs_im_le_norm _
  · filter_upwards [eventually_gt_atTop 0] with R hR
    rw [sub_neg_eq_add, ← two_mul, abs_of_pos (by positivity)]

lemma limit_real_line {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun R : ℝ ↦ ∫ (x : ℝ) in -R..R, integrand t (x : ℂ)) atTop
    (𝓝 (↑Real.pi * Real.exp (-t))) := by
  have h_eq : ∀ᶠ R : ℝ in atTop, ∫ (x : ℝ) in -R..R, integrand t (x : ℂ) =
      (((↑Real.pi * Real.exp (-t) : ℂ) +
      ∫ (x : ℝ) in -R..R, integrand t (↑x + ↑R * I)) -
      I * ∫ (y : ℝ) in 0..R, integrand t (↑R + ↑y * I)) +
      I * ∫ (y : ℝ) in 0..R, integrand t (-↑R + ↑y * I) := by
    filter_upwards [eventually_gt_atTop 1] with R hR
    have h_cont := contour_integral t R hR
    unfold rectIntegral bottomLeft topRight at h_cont
    simp only [neg_im, ofReal_im, neg_zero, ofReal_zero, zero_mul, add_zero, neg_re, ofReal_re,
      add_re, mul_re, I_re, mul_zero, I_im, mul_one, sub_self, smul_eq_mul, add_im, im_ofReal_mul,
      ofReal_neg, zero_add] at h_cont
    generalize ∫ (x : ℝ) in -R..R, integrand t (x : ℂ) = A at h_cont ⊢
    generalize ∫ (x : ℝ) in -R..R, integrand t (↑x + ↑R * I) = B at h_cont ⊢
    generalize I * ∫ (y : ℝ) in 0..R, integrand t (↑R + ↑y * I) = C at h_cont ⊢
    generalize I * ∫ (y : ℝ) in 0..R, integrand t (-↑R + ↑y * I) = D at h_cont ⊢
    calc A
      _ = (A - B + C - D) + B - C + D := by ring
      _ = (↑Real.pi * Real.exp (-t) : ℂ) + B - C + D := by rw [h_cont]
  have h_lim := (((tendsto_const_nhds (x := (↑Real.pi * Real.exp (-t) : ℂ))).add
    (limit_top_edge ht)).sub ((limit_right_edge ht).const_mul I)).add
    ((limit_left_edge ht).const_mul I)
  have h_eq_symm : ∀ᶠ R : ℝ in atTop,
      (((↑Real.pi * Real.exp (-t) : ℂ) +
      ∫ (x : ℝ) in -R..R, integrand t (↑x + ↑R * I)) -
      I * ∫ (y : ℝ) in 0..R, integrand t (↑R + ↑y * I)) +
      I * ∫ (y : ℝ) in 0..R, integrand t (-↑R + ↑y * I) =
      ∫ (x : ℝ) in -R..R, integrand t (x : ℂ) := by
    filter_upwards [h_eq] with R hR_eq
    exact hR_eq.symm
  simp only [mul_zero, add_zero, sub_zero] at h_lim
  exact Filter.Tendsto.congr' h_eq_symm h_lim

theorem integral_cpv_integrand {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun R : ℝ ↦ ∫ (x : ℝ) in -R..R, Real.cos (t * x) / (x^2 + 1))
    atTop (𝓝 (Real.pi * Real.exp (-t))) := by
  have h_re := (continuous_re.tendsto (↑Real.pi * Real.exp (-t) : ℂ)).comp
    (limit_real_line ht)
  have h_RHS : (↑Real.pi * (Real.exp (-t) : ℂ)).re = Real.pi * Real.exp (-t) := by norm_cast
  rw [h_RHS] at h_re
  have h_LHS : (fun R : ℝ ↦ (∫ (x : ℝ) in -R..R, integrand t (x : ℂ)).re) =
      (fun R : ℝ ↦ ∫ (x : ℝ) in -R..R, Real.cos (t * x) / (x^2 + 1)) := by
    ext R
    have h_int : IntervalIntegrable (fun x : ℝ ↦ integrand t (x : ℂ)) volume (-R) R := by
      apply ContinuousOn.intervalIntegrable
      unfold integrand
      fun_prop (disch := intro x _; norm_cast; nlinarith)
    have h_comm : (∫ (x : ℝ) in -R..R, integrand t (x : ℂ)).re = ∫ (x : ℝ) in -R..R,
        (integrand t (x : ℂ)).re :=
      (ContinuousLinearMap.intervalIntegral_comp_comm reCLM h_int).symm
    rw [h_comm]
    apply intervalIntegral.integral_congr
    have h_re (x : ℝ) : (integrand t (x : ℂ)).re = Real.cos (t * x) / (x^2 + 1) := by
      unfold integrand
      rw_mod_cast [div_ofReal_re, ← exp_ofReal_mul_I_re]
      have h_exp : I * ↑t * ↑x = ↑(t * x) * I := by push_cast; ring
      rw [h_exp]
    intro x _
    exact h_re x
  change Tendsto (fun R : ℝ ↦ (∫ (x : ℝ) in -R..R, integrand t (x : ℂ)).re)
    atTop (𝓝 (Real.pi * Real.exp (-t))) at h_re
  rw [h_LHS] at h_re
  exact h_re

lemma integrand_integrable (t : ℝ) : Integrable (fun x : ℝ ↦ Real.cos (t * x) / (x^2 + 1)) := by
  have h_bound_integrable : Integrable (fun x : ℝ ↦ 1 / (x^2 + 1)) := by
    have h_eq : (fun x : ℝ ↦ 1 / (x^2 + 1)) = fun x ↦ (1 + x^2)⁻¹ := by ring_nf
    rw [h_eq]
    exact integrable_inv_one_add_sq
  apply h_bound_integrable.mono
  · apply Continuous.aestronglyMeasurable
    refine Continuous.div (by fun_prop) (by fun_prop) ?_
    intro x
    positivity
  · filter_upwards with x
    have : ‖Real.cos (t * x)‖ ≤ 1 := Real.abs_cos_le_one (t * x)
    rw [norm_div, norm_div, norm_one]
    gcongr

theorem lebesgue_integral_integrand_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    ∫ x : ℝ, Real.cos (t * x) / (x^2 + 1) = Real.pi * Real.exp (-t) := by
  have h_CPV := integral_cpv_integrand ht
  have h_Lebesgue : Tendsto (fun R : ℝ ↦ ∫ x in -R..R, Real.cos (t * x) / (x^2 + 1))
      atTop (𝓝 (∫ x : ℝ, Real.cos (t * x) / (x^2 + 1))) := by
    apply intervalIntegral_tendsto_integral
    · exact integrand_integrable t
    · exact tendsto_neg_atTop_atBot
    · exact tendsto_id
  exact tendsto_nhds_unique h_Lebesgue h_CPV

theorem lebesgue_integral_integrand (t : ℝ) :
    ∫ x : ℝ, Real.cos (t * x) / (x^2 + 1) = Real.pi * Real.exp (-|t|) := by
  rcases le_total 0 t with ht | ht
  · have : |t| = t := abs_of_nonneg ht
    rw [this]
    exact lebesgue_integral_integrand_of_nonneg ht
  · have : |t| = -t := abs_of_nonpos ht
    rw [this]
    have h_cos : (fun x : ℝ ↦ Real.cos (t * x) / (x^2 + 1)) =
                 (fun x : ℝ ↦ Real.cos (-t * x) / (x^2 + 1)) := by
      ext x
      congr 1
      have : -t * x = -(t * x) := by ring
      rw [this, Real.cos_neg]
    rw [h_cos]
    exact lebesgue_integral_integrand_of_nonneg (by linarith)

end Test1
