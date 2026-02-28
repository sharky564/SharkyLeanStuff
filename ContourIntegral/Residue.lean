import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope

open Complex Topology Function

noncomputable def g (z : ℂ) : ℂ := exp (I * z) / (z + I)

noncomputable def f (z : ℂ) : ℂ := g z / (z - I)

lemma g_I : g I = exp (-1) / (2 * I) := by
  simp only [g, I_mul_I]
  ring

lemma re_f_eq_cos (x : ℝ) : (f (x : ℂ)).re = Real.cos x / (x^2 + 1) := by
  unfold f g
  rw [div_div, ← sq_sub_sq, I_sq, sub_neg_eq_add]
  rw_mod_cast [div_ofReal_re, ← exp_ofReal_mul_I_re]
  ring_nf

noncomputable def rectIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (((∫ (x : ℝ) in z.re..w.re, f (↑x + ↑z.im * I)) -
     ∫ (x : ℝ) in z.re..w.re, f (↑x + ↑w.im * I)) +
     I • ∫ (y : ℝ) in z.im..w.im, f (↑w.re + ↑y * I)) -
     I • ∫ (y : ℝ) in z.im..w.im, f (↑z.re + ↑y * I)

noncomputable def zR (R : ℝ) : ℂ := -R

noncomputable def wR (R : ℝ) : ℂ := R + R * I

noncomputable def h (z : ℂ) : ℂ :=
  if z = I then deriv g I else f z - g I / (z - I)

lemma h_eq_dslope (z : ℂ) : h z = dslope g I z := by
  unfold h f dslope slope
  split_ifs with hz
  · rw [hz, Function.update_self]
  · rw [Function.update_of_ne hz]
    rw [vsub_eq_sub, smul_eq_mul]
    ring

lemma g_diff_at {z : ℂ} (hz : z + I ≠ 0) : DifferentiableAt ℂ g z := by
  unfold g
  fun_prop (disch := assumption)

lemma integral_h_eq_zero (R : ℝ) (hR : 1 < R) :
    rectIntegral h (zR R) (wR R) = 0 := by
  unfold rectIntegral
  apply Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    h (zR R) (wR R) {I} (Set.countable_singleton I)
  · rintro z ⟨_, hz_im⟩
    by_cases hzi : z = I
    · subst hzi
      apply ContinuousAt.continuousWithinAt
      have h_eq : h = dslope g I := funext h_eq_dslope
      rw [h_eq]
      have hgI : DifferentiableAt ℂ g I := by
        apply g_diff_at
        norm_num
      exact continuousAt_dslope_same.mpr hgI
    · apply ContinuousAt.continuousWithinAt
      have h_eq_local : ∀ᶠ w in 𝓝 z, h w = f w - g I / (w - I) := by
        have h_ne_nhds : ∀ᶠ w in 𝓝 z, w ≠ I := IsOpen.mem_nhds isOpen_ne hzi
        filter_upwards [h_ne_nhds] with w hw
        unfold h
        rw [if_neg hw]
      apply ContinuousAt.congr_of_eventuallyEq _ h_eq_local
      unfold f g
      have hz_plus_I : z + I ≠ 0 := by
        intro contra
        have him : (z + I).im = 0 := congrArg Complex.im contra
        unfold zR wR at hz_im
        simp only [neg_im, ofReal_im, neg_zero, add_im, mul_im, ofReal_re, I_im, mul_one, I_re,
          mul_zero, add_zero, zero_add, Set.mem_preimage, Set.mem_uIcc] at hz_im him
        rcases hz_im with _ | _ <;> linarith
      have hz_minus_I : z - I ≠ 0 := sub_ne_zero.mpr hzi
      fun_prop (disch := assumption)
  · rintro z ⟨⟨_, hz_im⟩, hzi_mem⟩
    have hzi : z ≠ I := hzi_mem
    have h_eq_local : ∀ᶠ w in 𝓝 z, h w = f w - g I / (w - I) := by
      have h_ne_nhds : ∀ᶠ w in 𝓝 z, w ≠ I := IsOpen.mem_nhds isOpen_ne hzi
      filter_upwards [h_ne_nhds] with w hw
      unfold h
      rw [if_neg hw]
    apply DifferentiableAt.congr_of_eventuallyEq _ h_eq_local
    unfold f g
    have hz_plus_I : z + I ≠ 0 := by
      intro contra
      have him : (z + I).im = 0 := congrArg Complex.im contra
      unfold zR wR at hz_im
      simp only [neg_im, ofReal_im, neg_zero, add_im, mul_im, ofReal_re, I_im, mul_one, I_re,
        mul_zero, add_zero, zero_add, Set.mem_preimage, Set.mem_Ioo, inf_lt_iff, lt_sup_iff]
      at hz_im him
      rcases hz_im with ⟨_ | _, _ | _⟩ <;> linarith
    have hz_minus_I : z - I ≠ 0 := sub_ne_zero.mpr hzi
    fun_prop (disch := assumption)

lemma integral_inv_sub_I_unfolded (R : ℝ) :
    rectIntegral (fun z ↦ 1 / (z - I)) (zR R) (wR R) =
      (∫ x in -R..R, 1 / ((x : ℂ) - I)) -
      (∫ x in -R..R, 1 / ((x : ℂ) + R * I - I)) +
      I * (∫ y in 0..R, 1 / ((R : ℂ) + y * I - I)) -
      I * (∫ y in 0..R, 1 / (-(R : ℂ) + y * I - I)) := by
  unfold rectIntegral zR wR
  simp only [neg_im, ofReal_im, neg_zero, ofReal_zero, zero_mul, add_zero, one_div, neg_re,
    ofReal_re, add_re, mul_re, I_re, mul_zero, I_im, mul_one, sub_self, add_im, mul_im, zero_add,
    smul_eq_mul, ofReal_neg]

lemma int_horizontal {a b : ℝ} {w : ℂ} (h_slit : ∀ x ∈ Set.uIcc a b, (x : ℂ) - w ∈ slitPlane) :
    ∫ x in a..b, 1 / ((x : ℂ) - w) = Complex.log (b - w) - Complex.log (a - w) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x ↦ Complex.log ((x : ℂ) - w))
  · intro x hx
    have h_inner : HasDerivAt (fun r : ℝ ↦ (r : ℂ) - w) 1 x := by
      simpa using (ContinuousLinearMap.hasDerivAt Complex.ofRealCLM).sub_const w
    have h_outer : HasDerivAt Complex.log (1 / ((x : ℂ) - w)) ((x : ℂ) - w) := by
      simp only [one_div]
      exact Complex.hasDerivAt_log (h_slit x hx)
    simpa using HasDerivAt.comp x h_outer h_inner
  · apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.div continuousOn_const
      (Complex.continuous_ofReal.sub continuous_const).continuousOn ?_
    rintro x hx contra
    have h_in_slit := h_slit x hx
    rw [contra] at h_in_slit
    have h_zero : (0 : ℂ) ∉ slitPlane := by simp [Complex.mem_slitPlane_iff]
    exact h_zero h_in_slit

lemma int_vertical_no_branch_cut {a b : ℝ} {w : ℂ}
    (h_slit : ∀ y ∈ Set.uIcc a b, (y : ℂ) * I - w ∈ slitPlane) :
    ∫ y in a..b, I * (1 / ((y : ℂ) * I - w)) =
    Complex.log (b * I - w) - Complex.log (a * I - w) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y ↦ Complex.log ((y : ℂ) * I - w))
  · intro y hy
    have h_inner : HasDerivAt (fun r : ℝ ↦ (r : ℂ) * I - w) I y := by
      simpa using ((ContinuousLinearMap.hasDerivAt Complex.ofRealCLM).mul_const I).sub_const w
    have h_outer : HasDerivAt Complex.log (1 / ((y : ℂ) * I - w)) ((y : ℂ) * I - w) := by
      simp only [one_div]
      exact Complex.hasDerivAt_log (h_slit y hy)
    simpa [mul_comm] using HasDerivAt.comp y h_outer h_inner
  · apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.div continuousOn_const ?_ ?_)
    · exact ((Complex.continuous_ofReal.mul continuous_const).sub continuous_const).continuousOn
    · rintro y hy contra
      have h_in_slit := h_slit y hy
      rw [contra] at h_in_slit
      have h_zero : (0 : ℂ) ∉ slitPlane := by simp [Complex.mem_slitPlane_iff]
      exact h_zero h_in_slit

lemma int_vertical_branch_cut {a b : ℝ} {w : ℂ}
    (h_slit : ∀ y ∈ Set.uIcc a b, -((y : ℂ) * I - w) ∈ slitPlane) :
    ∫ y in a..b, I * (1 / ((y : ℂ) * I - w)) =
    Complex.log (-(b * I - w)) - Complex.log (-(a * I - w)) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y ↦ Complex.log (-((y : ℂ) * I - w)))
  · intro y hy
    have h_inner : HasDerivAt (fun r : ℝ ↦ -((r : ℂ) * I - w)) (-I) y := by
      simpa using HasDerivAt.const_sub w ((ContinuousLinearMap.hasDerivAt
        Complex.ofRealCLM).mul_const I)
    have h_outer : HasDerivAt Complex.log (1 / (-((y : ℂ) * I - w))) (-((y : ℂ) * I - w)) := by
      simp only [one_div]
      exact Complex.hasDerivAt_log (h_slit y hy)
    have h_alg : (1 / -((y : ℂ) * I - w)) * -I = I * (1 / ((y : ℂ) * I - w)) := by
      calc (1 / -((y : ℂ) * I - w)) * -I
        _ = -(1 / ((y : ℂ) * I - w)) * -I := by rw [div_neg]
        _ = I * (1 / ((y : ℂ) * I - w)) := by ring
    exact (HasDerivAt.comp y h_outer h_inner).congr_deriv h_alg
  · apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.div continuousOn_const ?_ ?_)
    · exact ((Complex.continuous_ofReal.mul continuous_const).sub continuous_const).continuousOn
    · rintro y hy contra
      have h_in_slit := h_slit y hy
      rw [contra, neg_zero] at h_in_slit
      have h_zero : (0 : ℂ) ∉ slitPlane := by simp [Complex.mem_slitPlane_iff]
      exact h_zero h_in_slit

lemma int_bottom (R : ℝ) :
    (∫ x in -R..R, 1 / ((x : ℂ) - I)) = Complex.log (R - I) - Complex.log (-R - I) := by
  have h := int_horizontal (a := -R) (b := R) (w := I) (by
    intro x _
    rw [Complex.mem_slitPlane_iff]; right
    simp
  )
  rw [← ofReal_neg]
  exact h

lemma int_top (R : ℝ) (hR : 1 < R) :
    (∫ x in -R..R, 1 / ((x : ℂ) + R * I - I)) =
    Complex.log (R + R * I - I) - Complex.log (-R + R * I - I) := by
  have h := int_horizontal (a := -R) (b := R) (w := (-R * I + I)) (by
    intro x _
    rw [Complex.mem_slitPlane_iff]; right
    simp
    linarith
  )
  have h_align : ∀ x : ℂ, x - (-(R : ℂ) * I + I) = x + R * I - I := by
    intro x
    ring
  simp only [h_align] at h
  rw [← ofReal_neg]
  exact h

lemma int_right (R : ℝ) (hR : 1 < R) :
    (∫ y in 0..R, I * (1 / (R + (y : ℂ) * I - I))) =
    Complex.log (R + R * I - I) - Complex.log (R - I) := by
  have h := int_vertical_no_branch_cut (a := 0) (b := R) (w := -(R : ℂ) + I) (by
    intro y _
    rw [Complex.mem_slitPlane_iff]; left
    have hre : ((y : ℂ) * I - (-(R : ℂ) + I)).re > 0 := by
      simp only [sub_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_re, neg_re, add_zero, sub_neg_eq_add, zero_add, gt_iff_lt]
      linarith
    exact hre
  )
  have h_align : ∀ y : ℂ, y * I - (-(R : ℂ) + I) = (R : ℂ) + y * I - I := fun y ↦ by ring
  simp only [h_align] at h
  have h_zero : ((0 : ℝ) : ℂ) * I = 0 := by simp
  rw [h_zero, add_zero] at h
  exact h

lemma int_left (R : ℝ) (hR : 1 < R) :
    (∫ y in 0..R, I * (1 / (-(R : ℂ) + y * I - I))) =
      Complex.log (R - R * I + I) - Complex.log (R + I) := by
  have h := int_vertical_branch_cut (a := 0) (b := R) (w := (R : ℂ) + I) (by
    intro y _
    rw [Complex.mem_slitPlane_iff]; left
    have hre : (-((y : ℂ) * I - ((R : ℂ) + I))).re > 0 := by
      simp only [neg_sub, sub_re, add_re, ofReal_re, I_re, add_zero, mul_re, mul_zero, ofReal_im,
        I_im, mul_one, sub_self, sub_zero, gt_iff_lt]
      linarith
    exact hre
  )
  have h_align : ∀ y : ℂ, y * I - ((R : ℂ) + I) = -(R : ℂ) + y * I - I := fun y ↦ by ring
  simp only [h_align] at h
  have h_zero : ((0 : ℝ) : ℂ) * I = 0 := by simp
  rw [h_zero, add_zero] at h
  have h_inner1 : -(-(R : ℂ) + R * I - I) = R - R * I + I := by ring
  have h_inner2 : -(-(R : ℂ) - I) = R + I := by ring
  rw [h_inner1, h_inner2] at h
  exact h

lemma log_sub_log_neg_eq_pi_I_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    Complex.log z - Complex.log (-z) = ↑Real.pi * I := by
  rw [log, log]
  rw [norm_neg]
  simp only [add_sub_add_left_eq_sub]
  rw [← sub_mul]
  congr 1
  rw [arg_neg_eq_arg_sub_pi_of_im_pos hz]
  simp_all only [ofReal_sub, sub_sub_cancel]

lemma log_identity (R : ℝ) (hR : 1 < R) :
    (Complex.log (R - I) - Complex.log (-R - I)) -
    (Complex.log (R + R * I - I) - Complex.log (-R + R * I - I)) +
    (Complex.log (R + R * I - I) - Complex.log (R - I)) -
    (Complex.log (R - R * I + I) - Complex.log (R + I)) = 2 * ↑Real.pi * I := by
  have h_cancel : (Complex.log (R - I) - Complex.log (-R - I)) -
      (Complex.log (R + R * I - I) - Complex.log (-R + R * I - I)) +
      (Complex.log (R + R * I - I) - Complex.log (R - I)) -
      (Complex.log (R - R * I + I) - Complex.log (R + I)) =
    (Complex.log (-R + R * I - I) - Complex.log (R - R * I + I)) +
    (Complex.log (R + I) - Complex.log (-R - I)) := by ring
  rw [h_cancel]
  have h_Z : -R + R * I - I = -(R - R * I + I) := by ring
  rw [h_Z]
  have h_W : -R - I = -(R + I) := by ring
  rw [h_W]
  have h_log_Z : Complex.log (-(R - R * I + I)) - Complex.log (R - R * I + I) = I * ↑Real.pi := by
    have h_double_neg : Complex.log (R - R * I + I) = Complex.log (- -(R - R * I + I)) := by
      rw [neg_neg]
    rw [h_double_neg]
    have hz_im : 0 < (-(R - R * I + I)).im := by
      simp only [neg_add_rev, neg_sub, add_im, neg_im, I_im, sub_im, mul_im, ofReal_re, mul_one,
        ofReal_im, I_re, mul_zero, add_zero, sub_zero, lt_neg_add_iff_add_lt]
      linarith
    have h_helper := log_sub_log_neg_eq_pi_I_of_im_pos hz_im
    rw [h_helper]
    ring
  have h_log_W : Complex.log (R + I) - Complex.log (-(R + I)) = I * ↑Real.pi := by
    have hw_im : 0 < (R + I).im := by
      simp only [add_im, ofReal_im, I_im, zero_add]
      linarith
    have h_helper := log_sub_log_neg_eq_pi_I_of_im_pos hw_im
    rw [h_helper]
    ring
  rw [h_log_Z, h_log_W]
  ring

lemma integral_inv_sub_I (R : ℝ) (hR : 1 < R) :
    rectIntegral (fun z ↦ 1 / (z - I)) (zR R) (wR R) = 2 * ↑Real.pi * I := by
  rw [integral_inv_sub_I_unfolded R]
  have h_right_I : I * ∫ (y : ℝ) in 0..R, 1 / (↑R + ↑y * I - I) =
    ∫ (y : ℝ) in 0..R, I * (1 / (↑R + ↑y * I - I)) :=
    (intervalIntegral.integral_const_mul I _).symm
  have h_left_I : I * ∫ (y : ℝ) in 0..R, 1 / (-↑R + ↑y * I - I) =
    ∫ (y : ℝ) in 0..R, I * (1 / (-↑R + ↑y * I - I)) :=
    (intervalIntegral.integral_const_mul I _).symm
  rw [h_right_I, h_left_I]
  rw [int_bottom R, int_top R hR, int_right R hR, int_left R hR]
  exact log_identity R hR
