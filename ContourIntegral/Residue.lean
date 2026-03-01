import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Complex Topology MeasureTheory Filter Polynomial

section RectIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

noncomputable def rectIntegral (f : ℂ → E) (z w : ℂ) : E :=
  (((∫ (x : ℝ) in z.re..w.re, f (↑x + ↑z.im * I)) -
     ∫ (x : ℝ) in z.re..w.re, f (↑x + ↑w.im * I)) +
     I • ∫ (y : ℝ) in z.im..w.im, f (↑w.re + ↑y * I)) -
     I • ∫ (y : ℝ) in z.im..w.im, f (↑z.re + ↑y * I)

lemma rectIntegral_add {z w : ℂ} {f1 f2 : ℂ → E}
    (h1B : IntervalIntegrable (fun x : ℝ ↦ f1 (↑x + ↑z.im * I)) volume z.re w.re)
    (h2B : IntervalIntegrable (fun x : ℝ ↦ f2 (↑x + ↑z.im * I)) volume z.re w.re)
    (h1T : IntervalIntegrable (fun x : ℝ ↦ f1 (↑x + ↑w.im * I)) volume z.re w.re)
    (h2T : IntervalIntegrable (fun x : ℝ ↦ f2 (↑x + ↑w.im * I)) volume z.re w.re)
    (h1R : IntervalIntegrable (fun y : ℝ ↦ f1 (↑w.re + ↑y * I)) volume z.im w.im)
    (h2R : IntervalIntegrable (fun y : ℝ ↦ f2 (↑w.re + ↑y * I)) volume z.im w.im)
    (h1L : IntervalIntegrable (fun y : ℝ ↦ f1 (↑z.re + ↑y * I)) volume z.im w.im)
    (h2L : IntervalIntegrable (fun y : ℝ ↦ f2 (↑z.re + ↑y * I)) volume z.im w.im) :
    rectIntegral (fun z ↦ f1 z + f2 z) z w = rectIntegral f1 z w + rectIntegral f2 z w := by
  unfold rectIntegral
  rw [intervalIntegral.integral_add h1B h2B, intervalIntegral.integral_add h1T h2T,
    intervalIntegral.integral_add h1R h2R, intervalIntegral.integral_add h1L h2L]
  simp only [smul_add]
  abel

lemma rectIntegral_const_smul {z w : ℂ} (f1 : ℂ → E) (c : ℂ) :
    rectIntegral (fun z ↦ c • f1 z) z w = c • rectIntegral f1 z w := by
  unfold rectIntegral
  simp only [intervalIntegral.integral_smul]
  simp only [smul_sub, smul_add, ← smul_assoc, smul_comm c I]

lemma rectIntegral_congr_cofinite {f1 f2 : ℂ → E} {z w : ℂ}
    (h : f1 =ᶠ[.cofinite] f2) :
    rectIntegral f1 z w = rectIntegral f2 z w := by
  unfold rectIntegral
  congrm ?_ - ?_ + I • ?_ - I • ?_
    <;> apply intervalIntegral.integral_congr_ae
  all_goals
    suffices ∀ᵐ (x : ℝ), _ = _ from this.mono (fun _ h _ => h)
    apply Filter.EventuallyEq.filter_mono (l := .cofinite) _ <|
      Filter.le_cofinite_iff_eventually_ne.mpr MeasureTheory.volume.ae_ne
    apply h.comap _ |>.filter_mono _
    rw [Function.Injective.comap_cofinite_eq]
    simp [Function.Injective]

end RectIntegral

lemma rectIntegral_const_mul {z w : ℂ} (f1 : ℂ → ℂ) (c : ℂ) :
    rectIntegral (fun z ↦ c * f1 z) z w = c * rectIntegral f1 z w :=
  rectIntegral_const_smul f1 c

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

noncomputable def zR (R : ℝ) : ℂ := -R

noncomputable def wR (R : ℝ) : ℂ := R + R * I

noncomputable def h (z : ℂ) : ℂ :=
  if z = I then deriv g I else f z - g I / (z - I)

lemma h_eq_dslope (z : ℂ) : h z = dslope g I z := by
  unfold h f dslope slope
  split_ifs with hz
  · rw [hz, Function.update_self]
  · rw [Function.update_of_ne hz, vsub_eq_sub, smul_eq_mul]
    ring

lemma g_diff_at {z : ℂ} (hz : z + I ≠ 0) : DifferentiableAt ℂ g z := by
  unfold g
  fun_prop (disch := assumption)

lemma integral_h_eq_zero (R : ℝ) (hR : 1 < R) :
    rectIntegral h (zR R) (wR R) = 0 := by
  unfold rectIntegral
  apply integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
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
    have h_zero : (0 : ℂ) ∉ slitPlane := by simp [mem_slitPlane_iff]
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
      have h_zero : (0 : ℂ) ∉ slitPlane := by simp [mem_slitPlane_iff]
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
      calc (1 / -((y : ℂ) * I - w)) * -I  = -(1 / ((y : ℂ) * I - w)) * -I := by rw [div_neg]
        _ = I * (1 / ((y : ℂ) * I - w)) := by ring
    exact (HasDerivAt.comp y h_outer h_inner).congr_deriv h_alg
  · apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.div continuousOn_const ?_ ?_)
    · exact ((Complex.continuous_ofReal.mul continuous_const).sub continuous_const).continuousOn
    · rintro y hy contra
      have h_in_slit := h_slit y hy
      rw [contra, neg_zero] at h_in_slit
      have h_zero : (0 : ℂ) ∉ slitPlane := by simp [mem_slitPlane_iff]
      exact h_zero h_in_slit

lemma int_bottom (R : ℝ) :
    (∫ x in -R..R, 1 / ((x : ℂ) - I)) = Complex.log (R - I) - Complex.log (-R - I) := by
  have h := int_horizontal (a := -R) (b := R) (w := I) (by
    intro x _
    rw [mem_slitPlane_iff]
    right
    simp
  )
  rw [← ofReal_neg]
  exact h

lemma int_top (R : ℝ) (hR : 1 < R) :
    (∫ x in -R..R, 1 / ((x : ℂ) + R * I - I)) =
    Complex.log (R + R * I - I) - Complex.log (-R + R * I - I) := by
  have h := int_horizontal (a := -R) (b := R) (w := (-R * I + I)) (by
    intro x _
    rw [mem_slitPlane_iff]
    right
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
    rw [mem_slitPlane_iff]
    left
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
    rw [mem_slitPlane_iff]
    left
    have hre : (-((y : ℂ) * I - ((R : ℂ) + I))).re > 0 := by
      simp only [neg_sub, sub_re, add_re, ofReal_re, I_re, add_zero, mul_re, mul_zero, ofReal_im,
        I_im, mul_one, sub_self, sub_zero, gt_iff_lt]
      linarith
    exact hre
  )
  have h_align : ∀ y : ℂ, y * I - ((R : ℂ) + I) = -(R : ℂ) + y * I - I := fun y ↦ by ring
  simp only [h_align] at h
  have h_zero : ((0 : ℝ) : ℂ) * I = 0 := by simp
  have h_inner1 : -(-(R : ℂ) + R * I - I) = R - R * I + I := by ring
  have h_inner2 : -(-(R : ℂ) - I) = R + I := by ring
  rw [h_zero, add_zero, h_inner1, h_inner2] at h
  exact h

lemma log_sub_log_neg_eq_pi_I_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    Complex.log z - Complex.log (-z) = ↑Real.pi * I := by
  rw [log, log, norm_neg]
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
  have h_Z : -R + R * I - I = -(R - R * I + I) := by ring
  have h_W : -R - I = -(R + I) := by ring
  rw [h_cancel, h_Z, h_W]
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
  rw [h_right_I, h_left_I, int_bottom R, int_top R hR, int_right R hR, int_left R hR]
  exact log_identity R hR

local macro "no_poles_in_domain" : tactic => `(tactic|
· intro var _ contra
  have hre := congrArg Complex.re contra
  have him := congrArg Complex.im contra
  simp only [add_re, add_im, sub_re, sub_im, neg_re, neg_im, mul_re, mul_im, ofReal_re, ofReal_im,
    I_re, I_im, zero_re, zero_im, mul_zero, mul_one, zero_mul, one_mul, add_zero, zero_add,
    sub_zero, zero_sub, neg_zero, sub_self] at hre him
  linarith
)

lemma contour_integral_f (R : ℝ) (hR : 1 < R) :
    rectIntegral f (zR R) (wR R) = ↑Real.pi / Real.exp 1 := by
  have h_add : rectIntegral f (zR R) (wR R) =
      rectIntegral (fun z ↦ (f z - g I * (1 / (z - I)))) (zR R) (wR R) +
      rectIntegral (fun z ↦ g I * (1 / (z - I))) (zR R) (wR R) := by
    have h_sum : f = fun z ↦ (f z - g I * (1 / (z - I))) + g I * (1 / (z - I)) := by ext z; ring
    conv_lhs => rw [h_sum]
    apply rectIntegral_add
    all_goals
    · apply ContinuousOn.intervalIntegrable
      try unfold f
      unfold g zR wR
      simp only [neg_im, ofReal_im, neg_zero, ofReal_zero, zero_mul, add_zero, zero_add, I_mul_I,
        one_div, neg_re, ofReal_re, add_re, mul_re, I_re, mul_zero, I_im, mul_one, sub_self, add_im,
        im_ofReal_mul]
      fun_prop (disch := no_poles_in_domain)
  have h_f1_eq_h : rectIntegral (fun z ↦ f z - g I * (1 / (z - I))) (zR R) (wR R) =
      rectIntegral h (zR R) (wR R) := by
    apply rectIntegral_congr_cofinite
    filter_upwards [show {I}ᶜ ∈ Filter.cofinite by simp] with z hz
    unfold h
    split_ifs with h_eq
    · exact False.elim (hz h_eq)
    · ring
  rw [h_f1_eq_h] at h_add
  rw [h_add, integral_h_eq_zero R hR, rectIntegral_const_mul, integral_inv_sub_I R hR, g_I]
  have h_pi : (Real.exp (-1) / (2 * I)) * (2 * ↑Real.pi * I) = ↑Real.pi / Real.exp 1 := by
    rw [Real.exp_neg]
    push_cast
    field_simp
  push_cast at h_pi ⊢
  rw [zero_add]
  exact h_pi

lemma norm_f_le {z : ℂ} {R : ℝ} (hR : 1 < R) (hz_im : 0 ≤ z.im) (hz_norm : R ≤ ‖z‖) :
    ‖f z‖ ≤ 1 / (R^2 - 1) := by
  unfold f g
  have h_denom : (z + I) * (z - I) = z ^ 2 + 1 := by
    calc (z + I) * (z - I) = z^2 - I^2 := by ring
    _ = z^2 - (-1) := by rw [I_sq]
    _ = z^2 + 1 := by ring
  rw [div_div, h_denom, norm_div]
  have h_num : ‖Complex.exp (I * z)‖ ≤ 1 := by
    rw [norm_exp]
    have h2 : (I * z).re = -z.im := by simp [mul_re]
    rw [h2]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have h_tri : ‖z^2‖ - 1 ≤ ‖z^2 + 1‖ := by
    have ht := norm_add_le (z^2 + 1) (-1 : ℂ)
    have h_z2 : z^2 + 1 + (-1 : ℂ) = z^2 := by ring
    rw [h_z2] at ht
    simp only [norm_neg, norm_one] at ht
    linarith
  have h_R_pos : 0 < R := by positivity
  have h_R_sq : R^2 ≤ ‖z‖^2 := by gcongr
  have h_norm_sq : ‖z^2‖ = ‖z‖^2 := norm_pow z 2
  have h_den : R^2 - 1 ≤ ‖z^2 + 1‖ := by linarith [h_tri, h_R_sq, h_norm_sq]
  have H1 : 0 < R^2 - 1 := by nlinarith
  have H2 : 0 < ‖z^2 + 1‖ := by nlinarith
  calc ‖Complex.exp (I * z)‖ / ‖z^2 + 1‖ ≤ 1 / (R^2 - 1) := by gcongr

lemma tendsto_R_div_R_sq_sub_one_zero : Tendsto (fun R : ℝ ↦ R / (R^2 - 1)) atTop (𝓝 0) := by
  rw [← Asymptotics.isLittleO_iff_tendsto']
  · convert_to (X : ℝ[X]).eval =o[atTop] (X^2 - 1 : ℝ[X]).eval
    · ext; simp
    · ext; simp
    apply Polynomial.isLittleO_atTop_of_degree_lt
    convert_to (1 : WithBot ℕ) < 2 <;> (try compute_degree) <;> (norm_num; try decide)
  · filter_upwards [eventually_gt_atTop 1] with R hR h_zero
    nlinarith

lemma tendsto_integral_of_bound_isO
    (a b : ℝ → ℝ) (f : ℝ → ℝ → ℂ) (c : ℝ)
    (h_bound : ∀ᶠ R in atTop, ∀ t ∈ Set.uIoc (a R) (b R), ‖f R t‖ ≤ 1 / (R ^ 2 - 1))
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
    exact tendsto_R_div_R_sq_sub_one_zero.const_mul c

lemma limit_right_edge :
    Tendsto (fun R : ℝ ↦ ∫ (y : ℝ) in 0..R, f (↑R + ↑y * I)) atTop (𝓝 0) := by
  apply tendsto_integral_of_bound_isO (fun _ ↦ 0) (fun R ↦ R) (fun R y ↦ f (↑R + ↑y * I)) 1
  · filter_upwards [eventually_gt_atTop 1] with R hR y hy
    apply norm_f_le hR
    · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add]
      rw [Set.mem_uIoc] at hy
      rcases hy with ⟨hy1, _⟩ | ⟨_, hy2⟩ <;> linarith
    · calc R = |((R : ℂ) + y * I).re| := by rw [add_re, ofReal_re, re_ofReal_mul, I_re, mul_zero,
        add_zero, abs_of_pos (by linarith)]
      _ ≤ ‖(R : ℂ) + y * I‖ := Complex.abs_re_le_norm _
  · filter_upwards [eventually_gt_atTop 0] with R hR
    rw [sub_zero, abs_of_pos hR, one_mul]

lemma limit_left_edge :
    Tendsto (fun R : ℝ ↦ ∫ (y : ℝ) in 0..R, f (-↑R + ↑y * I)) atTop (𝓝 0) := by
  apply tendsto_integral_of_bound_isO (fun _ ↦ 0) (fun R ↦ R) (fun R y ↦ f (-↑R + ↑y * I)) 1
  · filter_upwards [eventually_gt_atTop 1] with R hR y hy
    apply norm_f_le hR
    · simp only [add_im, neg_im, ofReal_im, neg_zero, mul_im, ofReal_re, I_im, mul_one, I_re,
        mul_zero, add_zero, zero_add]
      rw [Set.mem_uIoc] at hy
      rcases hy with ⟨hy1, _⟩ | ⟨_, hy2⟩ <;> linarith
    · calc R = |(-(R : ℂ) + y * I).re| := by rw [add_re, neg_re, ofReal_re, re_ofReal_mul, I_re,
        mul_zero, add_zero, abs_of_neg (by linarith), neg_neg]
      _ ≤ ‖-(R : ℂ) + y * I‖ := Complex.abs_re_le_norm _
  · filter_upwards [eventually_gt_atTop 0] with R hR
    rw [sub_zero, abs_of_pos hR, one_mul]

lemma limit_top_edge :
    Tendsto (fun R : ℝ ↦ ∫ (x : ℝ) in -R..R, f (↑x + ↑R * I)) atTop (𝓝 0) := by
  apply tendsto_integral_of_bound_isO (fun R ↦ -R) (fun R ↦ R) (fun R x ↦ f (↑x + ↑R * I)) 2
  · filter_upwards [eventually_gt_atTop 1] with R hR x _
    apply norm_f_le hR
    · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add]
      linarith
    · calc R = |((x : ℂ) + R * I).im| := by rw [add_im, ofReal_im, im_ofReal_mul, I_im, mul_one,
        zero_add, abs_of_pos (by linarith)]
      _ ≤ ‖(x : ℂ) + R * I‖ := Complex.abs_im_le_norm _
  · filter_upwards [eventually_gt_atTop 0] with R hR
    rw [sub_neg_eq_add, ← two_mul, abs_of_pos (by positivity)]

lemma limit_real_line :
    Tendsto (fun R : ℝ ↦ ∫ (x : ℝ) in -R..R, f (x : ℂ)) atTop (𝓝 (↑Real.pi / Real.exp 1)) := by
  have h_eq : ∀ᶠ R : ℝ in atTop, ∫ (x : ℝ) in -R..R, f (x : ℂ) =
      (((↑Real.pi / Real.exp 1 : ℂ) +
      ∫ (x : ℝ) in -R..R, f (↑x + ↑R * I)) -
      I * ∫ (y : ℝ) in 0..R, f (↑R + ↑y * I)) +
      I * ∫ (y : ℝ) in 0..R, f (-↑R + ↑y * I) := by
    filter_upwards [eventually_gt_atTop 1] with R hR
    have h_cont := contour_integral_f R hR
    unfold rectIntegral zR wR at h_cont
    simp only [neg_im, ofReal_im, neg_zero, ofReal_zero, zero_mul, add_zero, neg_re, ofReal_re,
      add_re, mul_re, I_re, mul_zero, I_im, mul_one, sub_self, smul_eq_mul, add_im, im_ofReal_mul,
      ofReal_neg, zero_add] at h_cont
    generalize ∫ (x : ℝ) in -R..R, f (x : ℂ) = A at h_cont ⊢
    generalize ∫ (x : ℝ) in -R..R, f (↑x + ↑R * I) = B at h_cont ⊢
    generalize I * ∫ (y : ℝ) in 0..R, f (↑R + ↑y * I) = C at h_cont ⊢
    generalize I * ∫ (y : ℝ) in 0..R, f (-↑R + ↑y * I) = D at h_cont ⊢
    calc A = (A - B + C - D) + B - C + D := by ring
      _ = (↑Real.pi / Real.exp 1 : ℂ) + B - C + D := by rw [h_cont]
  have h_lim := (((tendsto_const_nhds (x := (↑Real.pi / Real.exp 1 : ℂ))).add limit_top_edge).sub
    (limit_right_edge.const_mul I)).add (limit_left_edge.const_mul I)
  have h_eq_symm : ∀ᶠ R : ℝ in atTop,
      (((↑Real.pi / Real.exp 1 : ℂ) +
      ∫ (x : ℝ) in -R..R, f (↑x + ↑R * I)) -
      I * ∫ (y : ℝ) in 0..R, f (↑R + ↑y * I)) +
      I * ∫ (y : ℝ) in 0..R, f (-↑R + ↑y * I) = ∫ (x : ℝ) in -R..R, f (x : ℂ) := by
    filter_upwards [h_eq] with R hR_eq
    exact hR_eq.symm
  simp only [mul_zero, add_zero, sub_zero] at h_lim
  exact Filter.Tendsto.congr' h_eq_symm h_lim

theorem integral_cpv_cos_div_sq_add_one :
    Tendsto (fun R : ℝ ↦ ∫ (x : ℝ) in -R..R, Real.cos x / (x^2 + 1))
    atTop (𝓝 (Real.pi / Real.exp 1)) := by
  have h_re := (Complex.continuous_re.tendsto (↑Real.pi / Real.exp 1 : ℂ)).comp limit_real_line
  have h_RHS : (↑Real.pi / (Real.exp 1 : ℂ)).re = Real.pi / Real.exp 1 := by norm_cast
  rw [h_RHS] at h_re
  have h_LHS : (fun R : ℝ ↦ (∫ (x : ℝ) in -R..R, f (x : ℂ)).re) =
      (fun R : ℝ ↦ ∫ (x : ℝ) in -R..R, Real.cos x / (x^2 + 1)) := by
    ext R
    have h_int : IntervalIntegrable (fun x : ℝ ↦ f (x : ℂ)) volume (-R) R := by
      apply ContinuousOn.intervalIntegrable
      unfold f g
      fun_prop (disch := no_poles_in_domain)
    have h_comm : (∫ (x : ℝ) in -R..R, f (x : ℂ)).re = ∫ (x : ℝ) in -R..R, (f (x : ℂ)).re :=
      (ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM h_int).symm
    rw [h_comm]
    apply intervalIntegral.integral_congr
    intro x _
    exact re_f_eq_cos x
  change Tendsto (fun R : ℝ ↦ (∫ (x : ℝ) in -R..R, f (x : ℂ)).re)
    atTop (𝓝 (Real.pi / Real.exp 1)) at h_re
  rw [h_LHS] at h_re
  exact h_re

lemma integrable_cos_div : Integrable (fun x : ℝ ↦ Real.cos x / (x^2 + 1)) := by
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
    have : ‖Real.cos x‖ ≤ 1 := Real.abs_cos_le_one x
    rw [norm_div, norm_div, norm_one]
    gcongr

theorem lebesgue_integral_cos_div_sq_add_one :
    ∫ x : ℝ, Real.cos x / (x^2 + 1) = Real.pi / Real.exp 1 := by
  have h_CPV := integral_cpv_cos_div_sq_add_one
  have h_Lebesgue : Tendsto (fun R : ℝ ↦ ∫ x in -R..R, Real.cos x / (x^2 + 1))
      atTop (𝓝 (∫ x : ℝ, Real.cos x / (x^2 + 1))) := by
    apply intervalIntegral_tendsto_integral
    · exact integrable_cos_div
    · exact tendsto_neg_atTop_atBot
    · exact tendsto_id
  exact tendsto_nhds_unique h_Lebesgue h_CPV
