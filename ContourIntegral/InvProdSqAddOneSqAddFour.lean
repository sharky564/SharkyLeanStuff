import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import ContourIntegral.ResidueTheorem

open Complex Topology MeasureTheory Filter Set Finset Polynomial ContourIntegral

namespace Test2

/--
The specific complex integrand `1 / ((z^2 + 1)(z^2 + 4))`.
-/
noncomputable def integrand (z : ℂ) : ℂ := 1 / ((z ^ 2 + 1) * (z ^ 2 + 4))

/--
The bottom-left corner `-R` of the rectangular contour used to integrate `integrand`.
-/
noncomputable def bottomLeft (R : ℝ) : ℂ := -R

/--
The top-right corner `R + R*I` of the rectangular contour used to integrate `integrand`.
-/
noncomputable def topRight (R : ℝ) : ℂ := R + R * I

/--
The poles of `integrand` inside the rectangular contour
-/
noncomputable def c2 (i : Fin 2) : ℂ := if i = 0 then I else 2 * I

/--
Non-holomorphic components of `integrand`
-/
noncomputable def g2 (i : Fin 2) (z : ℂ) : ℂ :=
  if i = 0 then 1 / (3 * (z + I)) else -1 / (3 * (z + 2 * I))

set_option linter.unusedVariables false
/--
Degree of each pole of `integrand`
-/
noncomputable def n2 (i : Fin 2) : ℕ := 1
set_option linter.unusedVariables true

lemma integrand_eq_sum (z : ℂ) (hz1 : z ≠ I) (hz2 : z ≠ -I) (hz3 : z ≠ 2 * I) (hz4 : z ≠ -2 * I) :
    integrand z = ∑ i : Fin 2, g2 i z / (z - c2 i) ^ (n2 i) := by
  rw [Fin.sum_univ_two]
  have h0 : (0 : Fin 2) = 0 := rfl
  have h1 : (1 : Fin 2) ≠ 0 := by decide
  simp only [n2, pow_one, c2, if_true, g2, h1, if_false]
  unfold integrand
  have h_sq1 : z^2 + 1 = (z + I) * (z - I) := by
    rw [← sq_sub_sq, I_sq, sub_neg_eq_add]
  have h_sq2 : z^2 + 4 = (z + 2*I) * (z - 2*I) := by
    rw [← sq_sub_sq]
    ring_nf
    rw [I_sq, neg_mul, one_mul, sub_neg_eq_add, add_comm]
  rw [h_sq1, h_sq2]
  have hd1 : z + I ≠ 0 := by
    intro c
    apply hz2
    exact add_eq_zero_iff_eq_neg.mp c
  have hd2 : z + 2*I ≠ 0 := by
    intro c
    apply hz4
    rw [neg_mul]
    apply add_eq_zero_iff_eq_neg.mp c
  have hd3 : z - I ≠ 0 := sub_ne_zero.mpr hz1
  have hd4 : z - 2*I ≠ 0 := sub_ne_zero.mpr hz3
  rw [mul_comm 2 I] at hd2 hd4
  field_simp
  rw [mul_comm I 2, ← h_sq1, ← h_sq2]
  ring

lemma contour_integral (R : ℝ) (hR : 2 < R) :
    rectIntegral integrand (bottomLeft R) (topRight R) = ↑Real.pi / 6 := by
  let U : Set ℂ := {-I}ᶜ ∩ {-2*I}ᶜ
  have hU_open : IsOpen U := IsOpen.inter isOpen_compl_singleton isOpen_compl_singleton
  have h_filled : filledRect (bottomLeft R) (topRight R) ⊆ U := by
    rintro z hz
    rw [mem_inter_iff, mem_compl_iff, mem_compl_iff, mem_singleton_iff, mem_singleton_iff]
    have hz_im := hz.2
    unfold bottomLeft topRight at hz_im
    simp only [neg_im, ofReal_im, neg_zero, add_im, mul_im, ofReal_re, I_im, mul_one, I_re,
      mul_zero, add_zero, zero_add] at hz_im
    rw [Set.mem_uIcc] at hz_im
    have hz_im_nonneg : 0 ≤ z.im := by
      rcases hz_im with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    constructor
    · intro contra
      rw [contra] at hz_im_nonneg
      have : (-I).im = -1 := rfl
      linarith
    · intro contra
      rw [contra] at hz_im_nonneg
      simp only [neg_mul, neg_im, mul_im, re_ofNat, I_im, mul_one, im_ofNat, I_re, mul_zero,
        add_zero] at hz_im_nonneg
      linarith
  have h_ci_re (i : Fin 2) : (c2 i).re = 0 := by
    by_cases h : i = 0 <;> simp [c2, h, I_re]
  have hc_re1 : ∀ i ∈ Finset.univ, (bottomLeft R).re < (c2 i).re := by
    intro i _
    rw [h_ci_re i]
    simp [bottomLeft]
    linarith
  have hc_re2 : ∀ i ∈ Finset.univ, (c2 i).re < (topRight R).re := by
    intro i _
    rw [h_ci_re i]
    simp [topRight]
    linarith
  have h_ci_im (i : Fin 2) : (c2 i).im ≤ 2 := by
    by_cases h : i = 0 <;> simp [c2, h, I_im]
  have hc_im1 : ∀ i ∈ Finset.univ, (bottomLeft R).im < (c2 i).im := by
    intro i _
    have hz_pos : 0 < (c2 i).im := by by_cases h : i = 0 <;> simp [c2, h, I_im]
    simp only [bottomLeft, neg_im, ofReal_im, neg_zero]
    exact hz_pos
  have hc_im2 : ∀ i ∈ Finset.univ, (c2 i).im < (topRight R).im := by
    intro i _
    have hwR : (topRight R).im = R := by simp [topRight]
    rw [hwR]
    linarith [h_ci_im i]
  have hH_holo : DifferentiableOn ℂ (fun _ ↦ (0 : ℂ)) U := differentiableOn_const 0
  have h_holo : ∀ i ∈ Finset.univ, DifferentiableOn ℂ (g2 i) U := by
    intro i _
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]
      apply DifferentiableOn.div
      · fun_prop
      · fun_prop
      · intro z hz h
        simp only [neg_mul, mem_inter_iff, mem_compl_iff, mem_singleton_iff, U] at hz
        apply hz.1
        rw [eq_neg_iff_add_eq_zero]
        simpa using h
    · simp only [Fin.mk_one, Fin.isValue]
      apply DifferentiableOn.div
      · fun_prop
      · fun_prop
      · intro z hz h
        simp only [neg_mul, mem_inter_iff, mem_compl_iff, mem_singleton_iff, U] at hz
        apply hz.2
        rw [eq_neg_iff_add_eq_zero]
        simpa using h
  have h_eq : ∀ x ∈ boundaryRect (bottomLeft R) (topRight R),
      integrand x = 0 + ∑ i ∈ Finset.univ, g2 i x / (x - c2 i) ^ (n2 i) := by
    intro x hx
    have h_not_poles : x ≠ I ∧ x ≠ -I ∧ x ≠ 2*I ∧ x ≠ -2*I := by
      rcases hx with ⟨h_re, h_im⟩ | ⟨h_im, h_re⟩
      · have h_x_re : x.re ≠ 0 := by
          rcases h_re with hr | hr
          all_goals
            rw [hr]
            try unfold bottomLeft
            try unfold topRight
            simp only [neg_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
              sub_self, add_zero, ne_eq, neg_eq_zero]
            linarith
        refine ⟨?_, ?_, ?_, ?_⟩ <;>
          (intro contra; rw [contra] at h_x_re; exact h_x_re (by norm_num))
      · have h_x_im : x.im ≠ 1 ∧ x.im ≠ -1 ∧ x.im ≠ 2 ∧ x.im ≠ -2 := by
          rcases h_im with hi | hi
          all_goals
            rw [hi]
            try unfold bottomLeft
            try unfold topRight
            simp only [neg_im, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, neg_zero, I_re,
              mul_zero, ne_eq, zero_ne_one, not_false_eq_true, zero_eq_neg, one_ne_zero,
              OfNat.zero_ne_ofNat, OfNat.ofNat_ne_zero, and_self]
            try refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
        refine ⟨?_, ?_, ?_, ?_⟩ <;> (intro contra; rw [contra] at h_x_im; norm_num at h_x_im)
    rw [zero_add]
    apply integrand_eq_sum
    · exact h_not_poles.1
    · exact h_not_poles.2.1
    · exact h_not_poles.2.2.1
    · exact h_not_poles.2.2.2
  have h_thm := residue_theorem_rect_meromorphic' Finset.univ integrand (fun _ ↦ 0) c2 g2 n2
    (bottomLeft R) (topRight R) hc_re1 hc_re2 hc_im1 hc_im2 U hU_open h_filled hH_holo h_holo h_eq
  have h_sum : (∑ i ∈ Finset.univ, residue_pole (g2 i) (c2 i) (n2 i)) = 1 / (12 * I) := by
    rw [Fin.sum_univ_two]
    have h0 : (0 : Fin 2) = 0 := rfl
    have h1 : (1 : Fin 2) ≠ 0 := by decide
    have h_res0 : residue_pole (g2 0) (c2 0) (n2 0) = 1 / (6 * I) := by
      unfold g2
      simp only [n2, c2, if_true, residue_pole, Nat.sub_self, Fin.isValue]
      dsimp [dslope_iter]
      congr 1
      ring
    have h_res1 : residue_pole (g2 1) (c2 1) (n2 1) = -1 / (12 * I) := by
      unfold g2
      simp only [n2, c2, residue_pole, Nat.sub_self, Fin.isValue]
      dsimp [dslope_iter]
      congr 1
      ring
    rw [h_res0, h_res1]
    have hI : I ≠ 0 := I_ne_zero
    have hd1 : (6 * I) ≠ 0 := mul_ne_zero (by norm_num) hI
    have hd2 : (12 * I) ≠ 0 := mul_ne_zero (by norm_num) hI
    field_simp
    ring
  have h_eq_pi : 2 * ↑Real.pi * I * (1 / (12 * I)) = ↑Real.pi / 6 := by
    have hI : I ≠ 0 := I_ne_zero
    calc 2 * ↑Real.pi * I * (1 / (12 * I))
      _ = (2 * ↑Real.pi * I) / (12 * I) := mul_one_div _ _
      _ = (2 * ↑Real.pi) / 12 := mul_div_mul_right (2 * ↑Real.pi) 12 hI
      _ = ↑Real.pi / 6 := by ring
  rw [h_sum] at h_thm
  rw [h_thm, h_eq_pi]

lemma norm_integrand_le {z : ℂ} {R : ℝ} (hR : 2 < R) (hz_norm : R ≤ ‖z‖) :
    ‖integrand z‖ ≤ 1 / ((R^2 - 1) * (R^2 - 4)) := by
  unfold integrand
  have h_R_pos : 0 < R := by linarith
  rw [norm_div, norm_mul]
  have h1 : R^2 - 1 ≤ ‖z^2 + 1‖ := by
    calc R^2 - 1 ≤ ‖z‖^2 - 1 := by gcongr
    _ = ‖z^2‖ - 1 := by rw [norm_pow]
    _ ≤ ‖z^2 + 1‖ := by simpa [← norm_pow] using norm_sub_norm_le (z^2) (-1)
  have h2 : R^2 - 4 ≤ ‖z^2 + 4‖ := by
    calc R^2 - 4 ≤ ‖z‖^2 - 4 := by gcongr
    _ = ‖z^2‖ - 4 := by rw [norm_pow]
    _ ≤ ‖z^2 + 4‖ := by simpa [← norm_pow] using norm_sub_norm_le (z^2) (-4)
  have h3 : 0 < R^2 - 1 := by nlinarith
  have h4 : 0 < R^2 - 4 := by nlinarith
  norm_num
  gcongr

lemma tendsto_bound :
    Tendsto (fun R : ℝ ↦ R / ((R^2 - 1) * (R^2 - 4))) atTop (𝓝 0) := by
  rw [← Asymptotics.isLittleO_iff_tendsto']
  · convert_to (X : ℝ[X]).eval =o[atTop] (X^4 - 5 * X^2 + 4 : ℝ[X]).eval
    · ext
      simp
    · ext
      simp
      ring
    apply Polynomial.isLittleO_atTop_of_degree_lt
    convert_to (1 : WithBot ℕ) < 4 <;> (try compute_degree) <;> (norm_num; try decide)
  · filter_upwards [eventually_gt_atTop 2] with R hR
    simp only [mul_eq_zero]
    intro h
    rcases h with h | h <;> nlinarith

lemma tendsto_integral_of_bound_isO
    (a b : ℝ → ℝ) (f : ℝ → ℝ → ℂ) (c : ℝ)
    (h_bound : ∀ᶠ R in atTop, ∀ t ∈ uIoc (a R) (b R), ‖f R t‖ ≤ 1 / ((R ^ 2 - 1) * (R ^ 2 - 4)))
    (h_len : ∀ᶠ R in atTop, |b R - a R| ≤ c * R) :
    Tendsto (fun R ↦ ∫ y in a R..b R, f R y) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
  · filter_upwards with R using norm_nonneg _
  · filter_upwards [h_bound, h_len, eventually_gt_atTop 2] with R hB hL hR2
    have h_norm_le := intervalIntegral.norm_integral_le_of_norm_le_const hB
    have h_denom_pos1 : 0 < R^2 - 4 := by nlinarith
    have h_denom_pos : 0 < (R^2 - 1) * (R^2 - 4) := by nlinarith
    calc ‖∫ (y : ℝ) in a R..b R, f R y‖
      _ ≤ 1 / ((R^2 - 1) * (R^2 - 4)) * |b R - a R| := h_norm_le
      _ ≤ 1 / ((R^2 - 1) * (R^2 - 4)) * (c * R) := by gcongr
      _ = c * (R / ((R^2 - 1) * (R^2 - 4))) := by ring
  · have : 𝓝 (0 : ℝ) = 𝓝 (c * 0) := by rw [mul_zero]
    rw [this]
    exact tendsto_bound.const_mul c

lemma limit_right_edge :
    Tendsto (fun R : ℝ ↦ ∫ y in 0..R, integrand (↑R + ↑y * I)) atTop (𝓝 0) := by
  apply tendsto_integral_of_bound_isO (fun _ ↦ 0) (fun R ↦ R) (fun R y ↦ integrand (↑R + ↑y * I)) 1
  · filter_upwards [eventually_gt_atTop 2] with R hR y hy
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
  · filter_upwards [eventually_gt_atTop 2] with R hR y hy
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
  · filter_upwards [eventually_gt_atTop 2] with R hR x _
    apply norm_integrand_le hR
    calc R
    _ = |(x + R * I).im| := by rw [add_im, ofReal_im, im_ofReal_mul, I_im, mul_one, zero_add,
      abs_of_pos (by linarith)]
    _ ≤ ‖x + R * I‖ := abs_im_le_norm _
  · filter_upwards [eventually_gt_atTop 0] with R hR
    rw [sub_neg_eq_add, ← two_mul, abs_of_pos (by positivity)]

lemma limit_real_line :
    Tendsto (fun R : ℝ ↦ ∫ x in -R..R, integrand x) atTop (𝓝 (↑Real.pi / 6)) := by
  have h_eq : ∀ᶠ R : ℝ in atTop, ∫ x in -R..R, integrand x =
      (((↑Real.pi / 6 : ℂ) +
      ∫ x in -R..R, integrand (↑x + ↑R * I)) -
      I * ∫ y in 0..R, integrand (↑R + ↑y * I)) +
      I * ∫ y in 0..R, integrand (-↑R + ↑y * I) := by
    filter_upwards [eventually_gt_atTop 2] with R hR
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
      _ = (↑Real.pi / 6 : ℂ) + B - C + D := by rw [h_cont]
  have h_lim := (((tendsto_const_nhds (x := (↑Real.pi / 6 : ℂ))).add
    limit_top_edge).sub (limit_right_edge.const_mul I)).add
    (limit_left_edge.const_mul I)
  have h_eq_symm : ∀ᶠ R : ℝ in atTop,
      (((↑Real.pi / 6 : ℂ) +
      ∫ x in -R..R, integrand (↑x + ↑R * I)) -
      I * ∫ y in 0..R, integrand (↑R + ↑y * I)) +
      I * ∫ y in 0..R, integrand (-↑R + ↑y * I) = ∫ x in -R..R, integrand x := by
    filter_upwards [h_eq] with R hR_eq
    exact hR_eq.symm
  simp only [mul_zero, add_zero, sub_zero] at h_lim
  exact Filter.Tendsto.congr' h_eq_symm h_lim

theorem integral_cpv_integrand : Tendsto (fun R : ℝ ↦ ∫ x in -R..R, 1 / ((x^2 + 1) * (x^2 + 4)))
    atTop (𝓝 (Real.pi / 6)) := by
  have h_re := (continuous_re.tendsto (↑Real.pi / 6 : ℂ)).comp limit_real_line
  have h_RHS : (↑Real.pi / 6 : ℂ).re = Real.pi / 6 := by norm_cast
  rw [h_RHS] at h_re
  have h_LHS : (fun R : ℝ ↦ (∫ x in -R..R, integrand x).re) =
      (fun R : ℝ ↦ ∫ x in -R..R, 1 / ((x^2 + 1) * (x^2 + 4))) := by
    ext R
    have h_int : IntervalIntegrable (fun x : ℝ ↦ integrand x) volume (-R) R := by
      apply ContinuousOn.intervalIntegrable
      unfold integrand
      fun_prop (disch := intro x _; norm_cast; nlinarith)
    have h_comm : (∫ x in -R..R, integrand x).re = ∫ x in -R..R, (integrand x).re :=
      (ContinuousLinearMap.intervalIntegral_comp_comm reCLM h_int).symm
    rw [h_comm]
    apply intervalIntegral.integral_congr
    have h_re_eq (x : ℝ) : (integrand x).re = 1 / ((x^2 + 1) * (x^2 + 4)) := by
      unfold integrand
      have h_denom : ((x : ℂ)^2 + 1) * (x^2 + 4) = (((x^2 + 1) * (x^2 + 4) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [h_denom]
      have h_div : 1 / (((x^2 + 1) * (x^2 + 4) : ℝ) : ℂ) =
          ((1 / ((x^2 + 1) * (x^2 + 4)) : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [h_div, ofReal_re]
    intro x _
    exact h_re_eq x
  change Tendsto (fun R : ℝ ↦ (∫ x in -R..R, integrand x).re) atTop (𝓝 (Real.pi / 6)) at h_re
  rw [h_LHS] at h_re
  exact h_re

lemma integrand_integrable : Integrable (fun x : ℝ ↦ 1 / ((x^2 + 1) * (x^2 + 4))) := by
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
    rw [norm_div, norm_one, norm_div, norm_one]
    have h1 : 0 < x^2 + 1 := by positivity
    have h2 : 1 ≤ x^2 + 4 := by linarith [sq_nonneg x]
    have h3 : x^2 + 1 ≤ (x^2 + 1) * (x^2 + 4) := by
      calc x^2 + 1 = (x^2 + 1) * 1 := by ring
      _ ≤ (x^2 + 1) * (x^2 + 4) := mul_le_mul_of_nonneg_left h2 (by linarith)
    have h4 : 0 < (x^2 + 1) * (x^2 + 4) := by positivity
    rw [Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (by linarith)]
    gcongr

theorem lebesgue_integral_integrand :
    ∫ x : ℝ, 1 / ((x^2 + 1) * (x^2 + 4)) = Real.pi / 6 := by
  have h_CPV := integral_cpv_integrand
  have h_Lebesgue : Tendsto (fun R : ℝ ↦ ∫ x in -R..R, 1 / ((x^2 + 1) * (x^2 + 4)))
      atTop (𝓝 (∫ x : ℝ, 1 / ((x^2 + 1) * (x^2 + 4)))) := by
    apply intervalIntegral_tendsto_integral
    · exact integrand_integrable
    · exact tendsto_neg_atTop_atBot
    · exact tendsto_id
  exact tendsto_nhds_unique h_Lebesgue h_CPV

end Test2
