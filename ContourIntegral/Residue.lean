import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Complex Topology MeasureTheory Filter Polynomial Set

section RectIntegral

variable
  {𝕜 E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E] [SMulCommClass ℂ 𝕜 E]

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

lemma rectIntegral_const_smul {z w : ℂ} (f1 : ℂ → E) (c : 𝕜) :
    rectIntegral (fun z ↦ c • f1 z) z w = c • rectIntegral f1 z w := by
  unfold rectIntegral
  simp only [intervalIntegral.integral_smul, smul_comm, smul_sub, smul_add]

lemma rectIntegral_finset_sum {ι : Type*} (s : Finset ι) (F : ι → ℂ → E) (z w : ℂ)
    (hB : ∀ i ∈ s, IntervalIntegrable (fun x : ℝ ↦ F i (↑x + ↑z.im * I)) volume z.re w.re)
    (hT : ∀ i ∈ s, IntervalIntegrable (fun x : ℝ ↦ F i (↑x + ↑w.im * I)) volume z.re w.re)
    (hR : ∀ i ∈ s, IntervalIntegrable (fun y : ℝ ↦ F i (↑w.re + ↑y * I)) volume z.im w.im)
    (hL : ∀ i ∈ s, IntervalIntegrable (fun y : ℝ ↦ F i (↑z.re + ↑y * I)) volume z.im w.im) :
    rectIntegral (fun x ↦ ∑ i ∈ s, F i x) z w = ∑ i ∈ s, rectIntegral (F i) z w := by
  unfold rectIntegral
  simp_rw [intervalIntegral.integral_finset_sum hB, intervalIntegral.integral_finset_sum hT,
    intervalIntegral.integral_finset_sum hR, intervalIntegral.integral_finset_sum hL]
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]

end RectIntegral

section Residue

def boundaryRect (z w : ℂ) : Set ℂ :=
  {p : ℂ | (p.re = z.re ∨ p.re = w.re) ∧ p.im ∈ uIcc z.im w.im} ∪
  {p : ℂ | (p.im = z.im ∨ p.im = w.im) ∧ p.re ∈ uIcc z.re w.re}

def interiorRect (z w : ℂ) : Set ℂ :=
  {p : ℂ | p.re ∈ Ioo (min z.re w.re) (max z.re w.re) ∧
           p.im ∈ Ioo (min z.im w.im) (max z.im w.im)}

def filledRect (z w : ℂ) : Set ℂ :=
  {p : ℂ | p.re ∈ uIcc z.re w.re ∧ p.im ∈ uIcc z.im w.im}

noncomputable def dslope_iter (g : ℂ → ℂ) (c : ℂ) : ℕ → (ℂ → ℂ)
| 0 => g
| (n + 1) => dslope (dslope_iter g c n) c

noncomputable def residue_pole (g : ℂ → ℂ) (c : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else dslope_iter g c (n - 1) c

noncomputable def F_pow (m : ℕ) (c s : ℂ) : ℂ := -1 / ((m + 1 : ℂ) * (s - c)^(m + 1))

lemma mem_boundaryRect_bottom (z w : ℂ) {x : ℝ} (hx : x ∈ uIcc z.re w.re) :
    (x : ℂ) + z.im * I ∈ boundaryRect z w := by
  right
  simp_all only [mem_setOf_eq, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
    add_zero, zero_add, true_or, add_re, mul_re, sub_self, and_self]

lemma mem_boundaryRect_top (z w : ℂ) {x : ℝ} (hx : x ∈ uIcc z.re w.re) :
    (x : ℂ) + w.im * I ∈ boundaryRect z w := by
  right
  simp_all only [mem_setOf_eq, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
    add_zero, zero_add, or_true, add_re, mul_re, sub_self, and_self]

lemma mem_boundaryRect_left (z w : ℂ) {y : ℝ} (hy : y ∈ uIcc z.im w.im) :
    (z.re : ℂ) + y * I ∈ boundaryRect z w := by
  left
  simp_all only [mem_setOf_eq, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, true_or, add_im, mul_im, zero_add, and_self]

lemma mem_boundaryRect_right (z w : ℂ) {y : ℝ} (hy : y ∈ uIcc z.im w.im) :
    (w.re : ℂ) + y * I ∈ boundaryRect z w := by
  left
  simp_all only [mem_setOf_eq, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, or_true, add_im, mul_im, zero_add, and_self]

lemma not_mem_boundaryRect_of_inside {c z w : ℂ}
    (hz_re : z.re < c.re) (hw_re : c.re < w.re)
    (hz_im : z.im < c.im) (hw_im : c.im < w.im) :
    c ∉ boundaryRect z w := by
  intro hc
  rcases hc with ⟨hc_re, _⟩ | ⟨hc_im, _⟩
  · rcases hc_re with h | h <;> linarith
  · rcases hc_im with h | h <;> linarith

lemma boundaryRect_subset_filledRect (z w : ℂ) : boundaryRect z w ⊆ filledRect z w := by
  rintro p (⟨h_re | h_re, h_im⟩ | ⟨h_im | h_im, h_re⟩) <;>
    simp_all [filledRect, left_mem_uIcc, right_mem_uIcc]

lemma g_div_pow_eq (g : ℂ → ℂ) (c : ℂ) (n : ℕ) (z : ℂ) (hz : z ≠ c) :
    g z / (z - c)^n = dslope_iter g c n z +
      ∑ k ∈ Finset.range n, dslope_iter g c k c / (z - c)^(n - k) := by
  induction n with
  | zero => simp [dslope_iter]
  | succ n ih =>
    have h_pow : n + 1 - n = 1 := by omega
    rw [Finset.sum_range_succ, h_pow, pow_one]
    have h_dslope : dslope_iter g c (n + 1) z =
        (dslope_iter g c n z - dslope_iter g c n c) / (z - c) := by
      change dslope _ _ _ = _
      unfold dslope slope
      rw [Function.update_of_ne hz, vsub_eq_sub, smul_eq_mul, ← div_eq_inv_mul]
    have h_alg : (dslope_iter g c n z - dslope_iter g c n c) / (z - c) +
      dslope_iter g c n c / (z - c) = dslope_iter g c n z / (z - c) := by ring
    have h_sum : (∑ x ∈ Finset.range n, dslope_iter g c x c / (z - c) ^ (n + 1 - x)) =
                 (∑ x ∈ Finset.range n, dslope_iter g c x c / (z - c) ^ (n - x)) / (z - c) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun x hx ↦ ?_
      rw [div_div, ← pow_succ, Nat.sub_add_comm (Finset.mem_range.mp hx).le]
    rw [h_dslope, ← add_assoc, add_right_comm, h_alg, h_sum, ← add_div, ← ih, pow_succ, ← div_div]

lemma hasDerivAt_F_pow (m : ℕ) (c x : ℂ) (hx : x ≠ c) :
    HasDerivAt (F_pow m c) (1 / (x - c)^(m + 2)) x := by
  have hx_sub : x - c ≠ 0 := sub_ne_zero.mpr hx
  have h_pow_ne : (x - c) ^ (m + 1) ≠ 0 := pow_ne_zero _ hx_sub
  have h_m_ne : (m + 1 : ℂ) ≠ 0 := Nat.cast_add_one_ne_zero m
  have hd1 : HasDerivAt (fun s ↦ (m + 1 : ℂ) * (s - c)^(m + 1)) ((m + 1 : ℂ) * (↑(m + 1) *
    (x - c)^m * 1)) x := (((hasDerivAt_id x).sub_const c).pow (m + 1)).const_mul (m + 1 : ℂ)
  have hd2 := (hasDerivAt_const x (-1 : ℂ)).div hd1 (mul_ne_zero h_m_ne h_pow_ne)
  apply hd2.congr_deriv
  simp only [zero_mul, Nat.cast_add, Nat.cast_one, mul_one, neg_mul, one_mul, sub_neg_eq_add,
    zero_add]
  have hA_ne : (m + 1 : ℂ) ^ 2 * (x - c) ^ m ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 h_m_ne) (pow_ne_zero m hx_sub)
  have h_den : ((m + 1 : ℂ) * (x - c) ^ (m + 1)) ^ 2 =
      ((m + 1) ^ 2 * (x - c) ^ m) * (x - c) ^ (m + 2) := by field_simp; ring
  rw [h_den]
  refine Eq.trans ?_ (mul_div_mul_left 1 ((x - c) ^ (m + 2)) hA_ne)
  congr 1
  ring

lemma continuousOn_inv_pow (m : ℕ) (c : ℂ) (s : Set ℝ) (g : ℝ → ℂ)
    (hg_cont : ContinuousOn g s) (hg_pole : ∀ x ∈ s, g x ≠ c) :
    ContinuousOn (fun x ↦ 1 / (g x - c)^(m + 2)) s := by
  fun_prop (disch := intro x hx; exact pow_ne_zero _ (sub_ne_zero.mpr (hg_pole x hx)))

lemma rectIntegral_pow_inv_eq_zero {n : ℕ} (hn : 2 ≤ n) (c z w : ℂ)
    (hc : c ∉ boundaryRect z w) :
    rectIntegral (fun x ↦ 1 / (x - c)^n) z w = 0 := by
  obtain ⟨m, hm⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  subst hm
  have int_horiz (Y : ℝ) (h_pole : ∀ x ∈ uIcc z.re w.re, (x : ℂ) + Y * I ≠ c) :
      ∫ x in z.re..w.re, 1 / (↑x + ↑Y * I - c) ^ (m + 2) =
      F_pow m c (↑w.re + ↑Y * I) - F_pow m c (↑z.re + ↑Y * I) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun r : ℝ ↦ F_pow m c (↑r + ↑Y * I))
    · intro x hx
      have h_inner : HasDerivAt (fun r : ℝ ↦ (r : ℂ) + ↑Y * I) 1 x := by
        simpa using (ContinuousLinearMap.hasDerivAt Complex.ofRealCLM).add_const (↑Y * I)
      exact (HasDerivAt.comp x (hasDerivAt_F_pow m c _ (h_pole x hx)) h_inner).congr_deriv
        (mul_one _)
    · apply ContinuousOn.intervalIntegrable
      exact continuousOn_inv_pow m c _ _
        (Complex.continuous_ofReal.add continuous_const).continuousOn h_pole
  have int_vert (X : ℝ) (h_pole : ∀ y ∈ uIcc z.im w.im, (X : ℂ) + ↑y * I ≠ c) :
      I * ∫ y in z.im..w.im, 1 / (↑X + ↑y * I - c) ^ (m + 2) =
      F_pow m c (↑X + ↑w.im * I) - F_pow m c (↑X + ↑z.im * I) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun r : ℝ ↦ F_pow m c (↑X + ↑r * I))
    · intro y hy
      have h_inner : HasDerivAt (fun r : ℝ ↦ (X : ℂ) + (r : ℂ) * I) I y := by
        simpa using ((ContinuousLinearMap.hasDerivAt Complex.ofRealCLM).mul_const I).const_add
          (X : ℂ)
      exact (HasDerivAt.comp y (hasDerivAt_F_pow m c _ (h_pole y hy)) h_inner).congr_deriv
        (mul_comm _ _)
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul continuousOn_const
      exact continuousOn_inv_pow m c _ _
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn h_pole
  unfold rectIntegral
  simp only [smul_eq_mul]
  have h_bottom := int_horiz z.im (fun x hx contra ↦ hc <| contra ▸ mem_boundaryRect_bottom z w hx)
  have h_top := int_horiz w.im (fun x hx contra ↦ hc <| contra ▸ mem_boundaryRect_top z w hx)
  have h_right := int_vert  w.re (fun y hy contra ↦ hc <| contra ▸ mem_boundaryRect_right z w hy)
  have h_left := int_vert  z.re (fun y hy contra ↦ hc <| contra ▸ mem_boundaryRect_left z w hy)
  rw [h_bottom, h_top, h_right, h_left]
  ring

lemma log_sub_log_neg_eq_pi_I_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    Complex.log z - Complex.log (-z) = ↑Real.pi * I := by
  simp only [log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos hz, ofReal_sub, sub_mul,
    add_sub_add_left_eq_sub, sub_sub_cancel]

lemma log_sub_log_neg_eq_neg_pi_I_of_im_neg {z : ℂ} (hz : z.im < 0) :
    Complex.log z - Complex.log (-z) = -(↑Real.pi * I) := by
  have h1 : 0 < (-z).im := by simp_all only [neg_im, Left.neg_pos_iff]
  calc Complex.log z - Complex.log (-z)
    _ = -(Complex.log (-z) - Complex.log z) := by ring
    _ = -(Complex.log (-z) - Complex.log (- -z)) := by rw [neg_neg]
    _ = -(↑Real.pi * I) := by rw [log_sub_log_neg_eq_pi_I_of_im_pos h1]

lemma int_horizontal {a b : ℝ} {w : ℂ} (h_slit : ∀ x ∈ uIcc a b, (x : ℂ) - w ∈ slitPlane) :
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
    simp_all only [zero_notMem_slitPlane]

lemma int_vertical_no_branch_cut {a b : ℝ} {w : ℂ}
    (h_slit : ∀ y ∈ uIcc a b, (y : ℂ) * I - w ∈ slitPlane) :
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
    (h_slit : ∀ y ∈ uIcc a b, -((y : ℂ) * I - w) ∈ slitPlane) :
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
    have h_alg : (1 / -((y : ℂ) * I - w)) * -I = I * (1 / (y * I - w)) := by field_simp
    exact (HasDerivAt.comp y h_outer h_inner).congr_deriv h_alg
  · apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.div continuousOn_const ?_ ?_)
    · exact ((Complex.continuous_ofReal.mul continuous_const).sub continuous_const).continuousOn
    · rintro y hy contra
      have h_in_slit := h_slit y hy
      rw [contra, neg_zero] at h_in_slit
      have h_zero : (0 : ℂ) ∉ slitPlane := by simp [mem_slitPlane_iff]
      exact h_zero h_in_slit

lemma rectIntegral_inv_sub_eq_two_pi_I (c z w : ℂ)
    (hz_re : z.re < c.re) (hw_re : c.re < w.re)
    (hz_im : z.im < c.im) (hw_im : c.im < w.im) :
    rectIntegral (fun x ↦ 1 / (x - c)) z w = 2 * ↑Real.pi * I := by
  have int_horiz (Y : ℝ) (hY : Y ≠ c.im) :
      ∫ x in z.re..w.re, 1 / (↑x + ↑Y * I - c) =
      Complex.log (w.re + Y * I - c) - Complex.log (z.re + Y * I - c) := by
    have h_align : ∀ x : ℂ, x + ↑Y * I - c = x - (c - ↑Y * I) := fun x ↦ by ring
    simp_rw [h_align]
    exact int_horizontal (by
      intro x _
      rw [mem_slitPlane_iff]
      right
      simp only [sub_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_sub, neg_sub]
      exact sub_ne_zero.mpr hY
    )
  have h_B := int_horiz z.im (ne_of_lt hz_im)
  have h_T := int_horiz w.im (ne_of_gt hw_im)
  have h_R : I * ∫ y in z.im..w.im, 1 / (↑w.re + ↑y * I - c) =
      Complex.log (w.re + w.im * I - c) - Complex.log (w.re + z.im * I - c) := by
    have h_align : ∀ y : ℂ, ↑w.re + y * I - c = y * I - (c - ↑w.re) := fun y ↦ by ring
    simp_rw [h_align]
    rw [← intervalIntegral.integral_const_mul]
    exact int_vertical_no_branch_cut (by
      intro y _
      rw [mem_slitPlane_iff]
      left
      simp only [sub_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        zero_sub, neg_sub]
      linarith
    )
  have h_L : I * ∫ y in z.im..w.im, 1 / (↑z.re + ↑y * I - c) =
      Complex.log (-(↑z.re + ↑w.im * I - c)) - Complex.log (-(↑z.re + ↑z.im * I - c)) := by
    have h_align : ∀ y : ℂ, ↑z.re + y * I - c = y * I - (c - ↑z.re) := fun y ↦ by ring
    simp_rw [h_align]
    rw [← intervalIntegral.integral_const_mul]
    exact int_vertical_branch_cut (by
      intro y _
      rw [mem_slitPlane_iff]
      left
      simp only [neg_sub, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, sub_zero]
      linarith
    )
  unfold rectIntegral
  simp only [smul_eq_mul]
  rw [h_B, h_T, h_R, h_L]
  have h_im_eval : ∀ y : ℝ, (↑z.re + ↑y * I - c).im = y - c.im := by
    intro y
    simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
      add_zero, zero_add]
  have h_TL : Complex.log (↑z.re + ↑w.im * I - c) - Complex.log (-(↑z.re + ↑w.im * I - c)) =
      ↑Real.pi * I := by
    apply log_sub_log_neg_eq_pi_I_of_im_pos
    rw [h_im_eval]
    linarith
  have h_BL : Complex.log (↑z.re + ↑z.im * I - c) - Complex.log (-(↑z.re + ↑z.im * I - c)) =
      -(↑Real.pi * I) := by
    apply log_sub_log_neg_eq_neg_pi_I_of_im_neg
    rw [h_im_eval]
    linarith
  linear_combination h_TL - h_BL

lemma rectIntegral_eq_zero_of_differentiableOn (H : ℂ → ℂ) (z w : ℂ)
    (U : Set ℂ) (hU_open : IsOpen U)
    (h_filled : filledRect z w ⊆ U)
    (hH_holo : DifferentiableOn ℂ H U) :
    rectIntegral H z w = 0 := by
  apply integral_boundary_rect_eq_zero_of_differentiable_on_off_countable _ z w ∅
      Set.countable_empty
  · rintro x ⟨hx_re, hx_im⟩
    have hx_in : x ∈ U := h_filled ⟨hx_re, hx_im⟩
    exact (hH_holo.differentiableAt (hU_open.mem_nhds hx_in)).continuousAt.continuousWithinAt
  · rintro x ⟨⟨hx_re, hx_im⟩, _⟩
    have hx_in : x ∈ U := h_filled ⟨Set.Ioo_subset_Icc_self hx_re, Set.Ioo_subset_Icc_self hx_im⟩
    exact hH_holo.differentiableAt (hU_open.mem_nhds hx_in)

lemma continuousOn_boundary_of_diffOn {f : ℂ → ℂ} {z w : ℂ} {U : Set ℂ}
    (h_filled : filledRect z w ⊆ U) (hf : DifferentiableOn ℂ f U) :
    ContinuousOn f (boundaryRect z w) :=
  hf.continuousOn.mono (Subset.trans (boundaryRect_subset_filledRect z w) h_filled)

lemma intervalIntegrable_edges {f : ℂ → ℂ} {z w : ℂ} (hf : ContinuousOn f (boundaryRect z w)) :
    IntervalIntegrable (fun x : ℝ ↦ f (↑x + ↑z.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun x : ℝ ↦ f (↑x + ↑w.im * I)) volume z.re w.re ∧
    IntervalIntegrable (fun y : ℝ ↦ f (↑w.re + ↑y * I)) volume z.im w.im ∧
    IntervalIntegrable (fun y : ℝ ↦ f (↑z.re + ↑y * I)) volume z.im w.im := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ContinuousOn.intervalIntegrable
      (hf.comp (Complex.continuous_ofReal.add continuous_const).continuousOn
      (fun x hx ↦ mem_boundaryRect_bottom z w hx))
  · exact ContinuousOn.intervalIntegrable
      (hf.comp (Complex.continuous_ofReal.add continuous_const).continuousOn
      (fun x hx ↦ mem_boundaryRect_top z w hx))
  · exact ContinuousOn.intervalIntegrable
      (hf.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
      (fun y hy ↦ mem_boundaryRect_right z w hy))
  · exact ContinuousOn.intervalIntegrable
      (hf.comp (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
      (fun y hy ↦ mem_boundaryRect_left z w hy))

lemma rectIntegral_add' {f1 f2 : ℂ → ℂ} {z w : ℂ}
    (hf1 : ContinuousOn f1 (boundaryRect z w))
    (hf2 : ContinuousOn f2 (boundaryRect z w)) :
    rectIntegral (fun x ↦ f1 x + f2 x) z w = rectIntegral f1 z w + rectIntegral f2 z w := by
  rcases intervalIntegrable_edges hf1 with ⟨h1B, h1T, h1R, h1L⟩
  rcases intervalIntegrable_edges hf2 with ⟨h2B, h2T, h2R, h2L⟩
  exact rectIntegral_add h1B h2B h1T h2T h1R h2R h1L h2L

lemma rectIntegral_finset_sum' {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (z w : ℂ)
    (hF : ∀ i ∈ s, ContinuousOn (F i) (boundaryRect z w)) :
    rectIntegral (fun x ↦ ∑ i ∈ s, F i x) z w = ∑ i ∈ s, rectIntegral (F i) z w := by
  apply rectIntegral_finset_sum
  · intro i hi
    exact (intervalIntegrable_edges (hF i hi)).1
  · intro i hi
    exact (intervalIntegrable_edges (hF i hi)).2.1
  · intro i hi
    exact (intervalIntegrable_edges (hF i hi)).2.2.1
  · intro i hi
    exact (intervalIntegrable_edges (hF i hi)).2.2.2

lemma rectIntegral_congr {f1 f2 : ℂ → ℂ} {z w : ℂ} (h : ∀ x ∈ boundaryRect z w, f1 x = f2 x) :
    rectIntegral f1 z w = rectIntegral f2 z w := by
  unfold rectIntegral
  congrm ?_ - ?_ + I * ?_ - I * ?_
  · apply intervalIntegral.integral_congr; intro x hx; exact h _ (mem_boundaryRect_bottom z w hx)
  · apply intervalIntegral.integral_congr; intro x hx; exact h _ (mem_boundaryRect_top z w hx)
  · apply intervalIntegral.integral_congr; intro y hy; exact h _ (mem_boundaryRect_right z w hy)
  · apply intervalIntegral.integral_congr; intro y hy; exact h _ (mem_boundaryRect_left z w hy)

lemma differentiableOn_dslope_iter (g : ℂ → ℂ) (c : ℂ) (n : ℕ) (U : Set ℂ)
    (hU : IsOpen U) (hc : c ∈ U) (hg : DifferentiableOn ℂ g U) :
    DifferentiableOn ℂ (dslope_iter g c n) U := by
  induction n with
  | zero => exact hg
  | succ n ih =>
    unfold dslope_iter
    refine (differentiableOn_dslope ?_).mpr ih
    exact hU.mem_nhds hc

lemma continuousOn_inv_pow_bound (m : ℕ) (c z w : ℂ) (hc : c ∉ boundaryRect z w) :
    ContinuousOn (fun x ↦ 1 / (x - c)^m) (boundaryRect z w) := by
  apply ContinuousOn.div continuousOn_const
  · exact (continuous_id.sub continuous_const).continuousOn.pow m
  · intro x hx
    apply pow_ne_zero
    rw [sub_ne_zero]
    exact ne_of_mem_of_not_mem hx hc

theorem residue_theorem_rect_pole (g : ℂ → ℂ) (n : ℕ) (c z w : ℂ)
    (hz_re : z.re < c.re) (hw_re : c.re < w.re)
    (hz_im : z.im < c.im) (hw_im : c.im < w.im)
    (U : Set ℂ) (hU_open : IsOpen U)
    (h_filled : filledRect z w ⊆ U)
    (h_holo : DifferentiableOn ℂ g U) :
    rectIntegral (fun x ↦ g x / (x - c)^n) z w = 2 * ↑Real.pi * I * residue_pole g c n := by
  have hc_bound : c ∉ boundaryRect z w := by
    intro hc
    rcases hc with ⟨hc_re, _⟩ | ⟨hc_im, _⟩
    · rcases hc_re with _ | _ <;> linarith
    · rcases hc_im with _ | _ <;> linarith
  have hc_in : c ∈ U := by
    apply h_filled
    refine ⟨?_, ?_⟩
    · rw [mem_uIcc]
      left
      exact ⟨le_of_lt hz_re, le_of_lt hw_re⟩
    · rw [mem_uIcc]
      left
      exact ⟨le_of_lt hz_im, le_of_lt hw_im⟩
  cases n with
  | zero =>
    simp only [pow_zero, div_one, residue_pole, if_pos, mul_zero]
    exact rectIntegral_eq_zero_of_differentiableOn g z w U hU_open h_filled h_holo
  | succ m =>
    have h_congr := rectIntegral_congr (f1 := fun x ↦ g x / (x - c)^(m + 1))
      (f2 := fun x ↦ dslope_iter g c (m + 1) x +
      ∑ k ∈ Finset.range (m + 1), dslope_iter g c k c / (x - c)^(m + 1 - k)) (by
        intro x hx
        exact g_div_pow_eq g c (m + 1) x (fun contra ↦ hc_bound (contra ▸ hx))
      )
    rw [h_congr]
    have h_diff_iter := differentiableOn_dslope_iter g c (m + 1) U hU_open hc_in h_holo
    have h_cont_dslope := continuousOn_boundary_of_diffOn h_filled h_diff_iter
    have h_div_mul :
        (fun x ↦ ∑ k ∈ Finset.range (m + 1), dslope_iter g c k c / (x - c)^(m + 1 - k)) =
        (fun x ↦ ∑ k ∈ Finset.range (m + 1), dslope_iter g c k c * (1 / (x - c)^(m + 1 - k))) := by
      ext x
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_one_div]
    have h_cont_sum : ContinuousOn
        (fun x ↦ ∑ k ∈ Finset.range (m + 1), dslope_iter g c k c / (x - c)^(m + 1 - k))
        (boundaryRect z w) := by
      rw [h_div_mul]
      apply continuousOn_finset_sum
      intro k _
      apply ContinuousOn.mul continuousOn_const
      exact continuousOn_inv_pow_bound (m + 1 - k) c z w hc_bound
    rw [rectIntegral_add' h_cont_dslope h_cont_sum]
    have h_analytic_zero : rectIntegral (dslope_iter g c (m + 1)) z w = 0 := by
      apply integral_boundary_rect_eq_zero_of_differentiable_on_off_countable _ z w ∅
          countable_empty
      · rintro x ⟨hx_re, hx_im⟩
        have hx_in : x ∈ U := h_filled ⟨hx_re, hx_im⟩
        exact
          (h_diff_iter.differentiableAt (hU_open.mem_nhds hx_in)).continuousAt.continuousWithinAt
      · rintro x ⟨⟨hx_re, hx_im⟩, _⟩
        have hx_in : x ∈ U := h_filled
          ⟨Ioo_subset_Icc_self hx_re, Ioo_subset_Icc_self hx_im⟩
        exact h_diff_iter.differentiableAt (hU_open.mem_nhds hx_in)
    rw [h_analytic_zero, zero_add]
    have h_div_mul :
        (fun x ↦ ∑ k ∈ Finset.range (m + 1), dslope_iter g c k c / (x - c)^(m + 1 - k)) =
        (fun x ↦ ∑ k ∈ Finset.range (m + 1), dslope_iter g c k c * (1 / (x - c)^(m + 1 - k))) := by
      ext x
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_one_div]
    rw [h_div_mul]
    rw [rectIntegral_finset_sum']
    · have h_extract_const : ∑ i ∈ Finset.range (m + 1),
          rectIntegral (fun x ↦ dslope_iter g c i c * (1 / (x - c) ^ (m + 1 - i))) z w =
          ∑ i ∈ Finset.range (m + 1),
          dslope_iter g c i c * rectIntegral (fun x ↦ 1 / (x - c) ^ (m + 1 - i)) z w := by
        apply Finset.sum_congr rfl
        intro k _
        exact rectIntegral_const_smul _ (dslope_iter g c k c)
      rw [h_extract_const]
      rw [Finset.sum_range_succ]
      have h_higher_orders_zero : ∑ k ∈ Finset.range m,
          dslope_iter g c k c * rectIntegral (fun x ↦ 1 / (x - c)^(m + 1 - k)) z w = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        have h_pow : 2 ≤ m + 1 - k := by
          rw [Finset.mem_range] at hk
          omega
        have h_zero := rectIntegral_pow_inv_eq_zero h_pow c z w hc_bound
        rw [h_zero, mul_zero]
      rw [h_higher_orders_zero, zero_add]
      have h_residue_pow : m + 1 - m = 1 := by omega
      rw [h_residue_pow]
      simp only [pow_one]
      rw [rectIntegral_inv_sub_eq_two_pi_I c z w hz_re hw_re hz_im hw_im]
      unfold residue_pole
      simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, add_tsub_cancel_right]
      ring
    · intro k _
      apply ContinuousOn.mul continuousOn_const
      exact continuousOn_inv_pow_bound (m + 1 - k) c z w hc_bound

theorem residue_theorem_rect_poles_finset_multiple {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (g : ι → ℂ → ℂ) (n : ι → ℕ) (z w : ℂ)
    (hc_re1 : ∀ i ∈ s, z.re < (c i).re) (hc_re2 : ∀ i ∈ s, (c i).re < w.re)
    (hc_im1 : ∀ i ∈ s, z.im < (c i).im) (hc_im2 : ∀ i ∈ s, (c i).im < w.im)
    (U : Set ℂ) (hU_open : IsOpen U)
    (h_filled : filledRect z w ⊆ U)
    (h_holo : ∀ i ∈ s, DifferentiableOn ℂ (g i) U) :
    rectIntegral (fun x ↦ ∑ i ∈ s, g i x / (x - c i)^(n i)) z w =
    2 * ↑Real.pi * I * ∑ i ∈ s, residue_pole (g i) (c i) (n i) := by
  rw [rectIntegral_finset_sum']
  · have h_sum : (∑ i ∈ s, rectIntegral (fun x ↦ g i x / (x - c i) ^ n i) z w) =
        ∑ i ∈ s, 2 * ↑Real.pi * I * residue_pole (g i) (c i) (n i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact residue_theorem_rect_pole (g i) (n i) (c i) z w
        (hc_re1 i hi) (hc_re2 i hi) (hc_im1 i hi) (hc_im2 i hi)
        U hU_open h_filled (h_holo i hi)
    rw [h_sum, ← Finset.mul_sum]
  · intro i hi
    apply ContinuousOn.div
    · exact continuousOn_boundary_of_diffOn h_filled (h_holo i hi)
    · exact (continuous_id.sub continuous_const).continuousOn.pow (n i)
    · intro x hx
      apply pow_ne_zero
      rw [sub_ne_zero]
      have hc_bound := not_mem_boundaryRect_of_inside
        (hc_re1 i hi) (hc_re2 i hi) (hc_im1 i hi) (hc_im2 i hi)
      exact ne_of_mem_of_not_mem hx hc_bound

theorem residue_theorem_rect_poles_finset {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (g : ℂ → ℂ) (n : ι → ℕ) (z w : ℂ)
    (hc_re1 : ∀ i ∈ s, z.re < (c i).re) (hc_re2 : ∀ i ∈ s, (c i).re < w.re)
    (hc_im1 : ∀ i ∈ s, z.im < (c i).im) (hc_im2 : ∀ i ∈ s, (c i).im < w.im)
    (U : Set ℂ) (hU_open : IsOpen U)
    (h_filled : filledRect z w ⊆ U)
    (h_holo : DifferentiableOn ℂ g U) :
    rectIntegral (fun x ↦ ∑ i ∈ s, g x / (x - c i)^(n i)) z w =
    2 * ↑Real.pi * I * ∑ i ∈ s, residue_pole g (c i) (n i) := by
  apply residue_theorem_rect_poles_finset_multiple s c (fun _ ↦ g) n z w
  · exact hc_re1
  · exact hc_re2
  · exact hc_im1
  · exact hc_im2
  · exact hU_open
  · exact h_filled
  · intro _ _
    exact h_holo

theorem residue_theorem_rect_meromorphic {ι : Type*} (s : Finset ι)
    (H : ℂ → ℂ) (c : ι → ℂ) (g : ι → ℂ → ℂ) (n : ι → ℕ) (z w : ℂ)
    (hc_re1 : ∀ i ∈ s, z.re < (c i).re) (hc_re2 : ∀ i ∈ s, (c i).re < w.re)
    (hc_im1 : ∀ i ∈ s, z.im < (c i).im) (hc_im2 : ∀ i ∈ s, (c i).im < w.im)
    (U : Set ℂ) (hU_open : IsOpen U)
    (h_filled : filledRect z w ⊆ U)
    (hH_holo : DifferentiableOn ℂ H U)
    (h_holo : ∀ i ∈ s, DifferentiableOn ℂ (g i) U) :
    rectIntegral (fun x ↦ H x + ∑ i ∈ s, g i x / (x - c i)^(n i)) z w =
    2 * ↑Real.pi * I * ∑ i ∈ s, residue_pole (g i) (c i) (n i) := by
  have h_cont_H : ContinuousOn H (boundaryRect z w) :=
    continuousOn_boundary_of_diffOn h_filled hH_holo
  have h_cont_sum : ContinuousOn (fun x ↦ ∑ i ∈ s, g i x / (x - c i) ^ n i) (boundaryRect z w) := by
    apply continuousOn_finset_sum
    intro i hi
    apply ContinuousOn.div
    · exact continuousOn_boundary_of_diffOn h_filled (h_holo i hi)
    · exact (continuous_id.sub continuous_const).continuousOn.pow (n i)
    · intro x hx
      apply pow_ne_zero
      rw [sub_ne_zero]
      have hc_bound := not_mem_boundaryRect_of_inside
        (hc_re1 i hi) (hc_re2 i hi) (hc_im1 i hi) (hc_im2 i hi)
      exact ne_of_mem_of_not_mem hx hc_bound
  rw [rectIntegral_add' h_cont_H h_cont_sum]
  have hH_zero : rectIntegral H z w = 0 :=
    rectIntegral_eq_zero_of_differentiableOn H z w U hU_open h_filled hH_holo
  rw [hH_zero, zero_add]
  exact residue_theorem_rect_poles_finset_multiple s c g n z w hc_re1 hc_re2 hc_im1
    hc_im2 U hU_open h_filled h_holo

theorem residue_theorem_rect_meromorphic' {ι : Type*} (s : Finset ι)
    (f : ℂ → ℂ) (H : ℂ → ℂ) (c : ι → ℂ) (g : ι → ℂ → ℂ) (n : ι → ℕ) (z w : ℂ)
    (hc_re1 : ∀ i ∈ s, z.re < (c i).re) (hc_re2 : ∀ i ∈ s, (c i).re < w.re)
    (hc_im1 : ∀ i ∈ s, z.im < (c i).im) (hc_im2 : ∀ i ∈ s, (c i).im < w.im)
    (U : Set ℂ) (hU_open : IsOpen U)
    (h_filled : filledRect z w ⊆ U)
    (hH_holo : DifferentiableOn ℂ H U)
    (h_holo : ∀ i ∈ s, DifferentiableOn ℂ (g i) U)
    (h_eq : ∀ x ∈ boundaryRect z w, f x = H x + ∑ i ∈ s, g i x / (x - c i) ^ (n i)) :
    rectIntegral f z w =
      2 * ↑Real.pi * I * ∑ i ∈ s, residue_pole (g i) (c i) (n i) := by
  have h_decomp := residue_theorem_rect_meromorphic s H c g n z w
    hc_re1 hc_re2 hc_im1 hc_im2 U hU_open h_filled hH_holo h_holo
  rw [← h_decomp]
  apply rectIntegral_congr
  intro x hx
  exact h_eq x hx

end Residue

noncomputable def f (t : ℝ) (z : ℂ) : ℂ := exp (I * t * z) / (z ^ 2 + 1)

noncomputable def zR (R : ℝ) : ℂ := -R

noncomputable def wR (R : ℝ) : ℂ := R + R * I

lemma contour_integral_f (t : ℝ) (R : ℝ) (hR : 1 < R) :
    rectIntegral (f t) (zR R) (wR R) = ↑Real.pi * Real.exp (-t) := by
  let U : Set ℂ := {-I}ᶜ
  have hU_open : IsOpen U := isOpen_compl_singleton
  have hz_re : (zR R).re < I.re := by simp [zR]; linarith
  have hz_im : (zR R).im < I.im := by simp [zR]
  have hw_re : I.re < (wR R).re := by simp [wR]; linarith
  have hw_im : I.im < (wR R).im := by simp [wR]; linarith
  have h_filled : filledRect (zR R) (wR R) ⊆ U := by
    rintro z hz contra
    have him : z.im = (-I).im := congrArg Complex.im contra
    simp only [neg_im, I_im] at him
    have hz_im_bounds := hz.2
    unfold zR wR at hz_im_bounds
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
  have h_thm := residue_theorem_rect_pole g 1 I (zR R) (wR R)
    hz_re hw_re hz_im hw_im U hU_open h_filled h_holo
  have h_f_eq : (fun x ↦ g x / (x - I) ^ 1) = f t := by
    ext x
    simp only [pow_one, f]
    change Complex.exp (I * t * x) / (x + I) / (x - I) = Complex.exp (I * t * x) / (x^2 + 1)
    rw [div_div, ← sq_sub_sq, Complex.I_sq, sub_neg_eq_add]
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

lemma norm_f_le {t : ℝ} (ht : 0 ≤ t) {z : ℂ} {R : ℝ} (hR : 1 < R) (hz_im : 0 ≤ z.im)
    (hz_norm : R ≤ ‖z‖) : ‖f t z‖ ≤ 1 / (R^2 - 1) := by
  unfold f
  rw [norm_div]
  have h_num : ‖Complex.exp (I * t * z)‖ ≤ 1 := by
    rw [norm_exp]
    simp only [mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self, mul_im,
      one_mul, zero_add, zero_sub, Real.exp_le_one_iff, Left.neg_nonpos_iff]
    exact mul_nonneg ht hz_im
  have h_tri : ‖z^2‖ - 1 ≤ ‖z^2 + 1‖ := by
    simpa [← norm_pow] using norm_sub_norm_le (z^2) (-1)
  have h_R_pos : 0 < R := by positivity
  have h_R_sq : R^2 ≤ ‖z‖^2 := by gcongr
  have h_norm_sq : ‖z^2‖ = ‖z‖^2 := norm_pow z 2
  have h_den : R^2 - 1 ≤ ‖z^2 + 1‖ := by linarith [h_tri, h_R_sq, h_norm_sq]
  have H1 : 0 < R^2 - 1 := by nlinarith
  have H2 : 0 < ‖z^2 + 1‖ := by nlinarith
  calc ‖Complex.exp (I * t * z)‖ / ‖z^2 + 1‖ ≤ 1 / (R^2 - 1) := by gcongr

lemma tendsto_R_div_R_sq_sub_one_zero : Tendsto (fun R : ℝ ↦ R / (R^2 - 1)) atTop (𝓝 0) := by
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
    exact tendsto_R_div_R_sq_sub_one_zero.const_mul c

lemma limit_right_edge {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun R : ℝ ↦ ∫ (y : ℝ) in 0..R, f t (↑R + ↑y * I)) atTop (𝓝 0) := by
  apply tendsto_integral_of_bound_isO (fun _ ↦ 0) (fun R ↦ R) (fun R y ↦ f t (↑R + ↑y * I)) 1
  · filter_upwards [eventually_gt_atTop 1] with R hR y hy
    apply norm_f_le ht hR
    · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add]
      rw [mem_uIoc] at hy
      rcases hy with ⟨hy1, _⟩ | ⟨_, hy2⟩ <;> linarith
    · calc R
      _ = |((R : ℂ) + y * I).re| := by rw [add_re, ofReal_re, re_ofReal_mul, I_re, mul_zero,
        add_zero, abs_of_pos (by linarith)]
      _ ≤ ‖(R : ℂ) + y * I‖ := Complex.abs_re_le_norm _
  · filter_upwards [eventually_gt_atTop 0] with R hR
    rw [sub_zero, abs_of_pos hR, one_mul]

lemma limit_left_edge {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun R : ℝ ↦ ∫ (y : ℝ) in 0..R, f t (-↑R + ↑y * I)) atTop (𝓝 0) := by
  apply tendsto_integral_of_bound_isO (fun _ ↦ 0) (fun R ↦ R) (fun R y ↦ f t (-↑R + ↑y * I)) 1
  · filter_upwards [eventually_gt_atTop 1] with R hR y hy
    apply norm_f_le ht hR
    · simp only [add_im, neg_im, ofReal_im, neg_zero, mul_im, ofReal_re, I_im, mul_one, I_re,
        mul_zero, add_zero, zero_add]
      rw [mem_uIoc] at hy
      rcases hy with ⟨hy1, _⟩ | ⟨_, hy2⟩ <;> linarith
    · calc R
      _ = |(-(R : ℂ) + y * I).re| := by rw [add_re, neg_re, ofReal_re, re_ofReal_mul, I_re,
        mul_zero, add_zero, abs_of_neg (by linarith), neg_neg]
      _ ≤ ‖-(R : ℂ) + y * I‖ := Complex.abs_re_le_norm _
  · filter_upwards [eventually_gt_atTop 0] with R hR
    rw [sub_zero, abs_of_pos hR, one_mul]

lemma limit_top_edge {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun R : ℝ ↦ ∫ (x : ℝ) in -R..R, f t (↑x + ↑R * I)) atTop (𝓝 0) := by
  apply tendsto_integral_of_bound_isO (fun R ↦ -R) (fun R ↦ R) (fun R x ↦ f t (↑x + ↑R * I)) 2
  · filter_upwards [eventually_gt_atTop 1] with R hR x _
    apply norm_f_le ht hR
    · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
        zero_add]
      linarith
    · calc R
      _ = |((x : ℂ) + R * I).im| := by rw [add_im, ofReal_im, im_ofReal_mul, I_im, mul_one,
        zero_add, abs_of_pos (by linarith)]
      _ ≤ ‖(x : ℂ) + R * I‖ := Complex.abs_im_le_norm _
  · filter_upwards [eventually_gt_atTop 0] with R hR
    rw [sub_neg_eq_add, ← two_mul, abs_of_pos (by positivity)]

lemma limit_real_line {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun R : ℝ ↦ ∫ (x : ℝ) in -R..R, f t (x : ℂ)) atTop (𝓝 (↑Real.pi * Real.exp (-t))) := by
  have h_eq : ∀ᶠ R : ℝ in atTop, ∫ (x : ℝ) in -R..R, f t (x : ℂ) =
      (((↑Real.pi * Real.exp (-t) : ℂ) +
      ∫ (x : ℝ) in -R..R, f t (↑x + ↑R * I)) -
      I * ∫ (y : ℝ) in 0..R, f t (↑R + ↑y * I)) +
      I * ∫ (y : ℝ) in 0..R, f t (-↑R + ↑y * I) := by
    filter_upwards [eventually_gt_atTop 1] with R hR
    have h_cont := contour_integral_f t R hR
    unfold rectIntegral zR wR at h_cont
    simp only [neg_im, ofReal_im, neg_zero, ofReal_zero, zero_mul, add_zero, neg_re, ofReal_re,
      add_re, mul_re, I_re, mul_zero, I_im, mul_one, sub_self, smul_eq_mul, add_im, im_ofReal_mul,
      ofReal_neg, zero_add] at h_cont
    generalize ∫ (x : ℝ) in -R..R, f t (x : ℂ) = A at h_cont ⊢
    generalize ∫ (x : ℝ) in -R..R, f t (↑x + ↑R * I) = B at h_cont ⊢
    generalize I * ∫ (y : ℝ) in 0..R, f t (↑R + ↑y * I) = C at h_cont ⊢
    generalize I * ∫ (y : ℝ) in 0..R, f t (-↑R + ↑y * I) = D at h_cont ⊢
    calc A
      _ = (A - B + C - D) + B - C + D := by ring
      _ = (↑Real.pi * Real.exp (-t) : ℂ) + B - C + D := by rw [h_cont]
  have h_lim := (((tendsto_const_nhds (x := (↑Real.pi * Real.exp (-t) : ℂ))).add
    (limit_top_edge ht)).sub ((limit_right_edge ht).const_mul I)).add
    ((limit_left_edge ht).const_mul I)
  have h_eq_symm : ∀ᶠ R : ℝ in atTop,
      (((↑Real.pi * Real.exp (-t) : ℂ) +
      ∫ (x : ℝ) in -R..R, f t (↑x + ↑R * I)) -
      I * ∫ (y : ℝ) in 0..R, f t (↑R + ↑y * I)) +
      I * ∫ (y : ℝ) in 0..R, f t (-↑R + ↑y * I) = ∫ (x : ℝ) in -R..R, f t (x : ℂ) := by
    filter_upwards [h_eq] with R hR_eq
    exact hR_eq.symm
  simp only [mul_zero, add_zero, sub_zero] at h_lim
  exact Filter.Tendsto.congr' h_eq_symm h_lim

theorem integral_cpv_cos_div_sq_add_one {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun R : ℝ ↦ ∫ (x : ℝ) in -R..R, Real.cos (t * x) / (x^2 + 1))
    atTop (𝓝 (Real.pi * Real.exp (-t))) := by
  have h_re := (Complex.continuous_re.tendsto (↑Real.pi * Real.exp (-t) : ℂ)).comp
    (limit_real_line ht)
  have h_RHS : (↑Real.pi * (Real.exp (-t) : ℂ)).re = Real.pi * Real.exp (-t) := by norm_cast
  rw [h_RHS] at h_re
  have h_LHS : (fun R : ℝ ↦ (∫ (x : ℝ) in -R..R, f t (x : ℂ)).re) =
      (fun R : ℝ ↦ ∫ (x : ℝ) in -R..R, Real.cos (t * x) / (x^2 + 1)) := by
    ext R
    have h_int : IntervalIntegrable (fun x : ℝ ↦ f t (x : ℂ)) volume (-R) R := by
      apply ContinuousOn.intervalIntegrable
      unfold f
      fun_prop (disch := intro x _; norm_cast; nlinarith)
    have h_comm : (∫ (x : ℝ) in -R..R, f t (x : ℂ)).re = ∫ (x : ℝ) in -R..R, (f t (x : ℂ)).re :=
      (ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM h_int).symm
    rw [h_comm]
    apply intervalIntegral.integral_congr
    have h_re (x : ℝ) : (f t (x : ℂ)).re = Real.cos (t * x) / (x^2 + 1) := by
      unfold f
      rw_mod_cast [div_ofReal_re, ← exp_ofReal_mul_I_re]
      have h_exp : I * ↑t * ↑x = ↑(t * x) * I := by push_cast; ring
      rw [h_exp]
    intro x _
    exact h_re x
  change Tendsto (fun R : ℝ ↦ (∫ (x : ℝ) in -R..R, f t (x : ℂ)).re)
    atTop (𝓝 (Real.pi * Real.exp (-t))) at h_re
  rw [h_LHS] at h_re
  exact h_re

lemma integrable_cos_div (t : ℝ) : Integrable (fun x : ℝ ↦ Real.cos (t * x) / (x^2 + 1)) := by
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

theorem lebesgue_integral_cos_div_sq_add_one_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    ∫ x : ℝ, Real.cos (t * x) / (x^2 + 1) = Real.pi * Real.exp (-t) := by
  have h_CPV := integral_cpv_cos_div_sq_add_one ht
  have h_Lebesgue : Tendsto (fun R : ℝ ↦ ∫ x in -R..R, Real.cos (t * x) / (x^2 + 1))
      atTop (𝓝 (∫ x : ℝ, Real.cos (t * x) / (x^2 + 1))) := by
    apply intervalIntegral_tendsto_integral
    · exact integrable_cos_div t
    · exact tendsto_neg_atTop_atBot
    · exact tendsto_id
  exact tendsto_nhds_unique h_Lebesgue h_CPV

theorem lebesgue_integral_cos_div_sq_add_one (t : ℝ) :
    ∫ x : ℝ, Real.cos (t * x) / (x^2 + 1) = Real.pi * Real.exp (-|t|) := by
  rcases le_total 0 t with ht | ht
  · have : |t| = t := abs_of_nonneg ht
    rw [this]
    exact lebesgue_integral_cos_div_sq_add_one_of_nonneg ht
  · have : |t| = -t := abs_of_nonpos ht
    rw [this]
    have h_cos : (fun x : ℝ ↦ Real.cos (t * x) / (x^2 + 1)) =
                 (fun x : ℝ ↦ Real.cos (-t * x) / (x^2 + 1)) := by
      ext x
      congr 1
      have : -t * x = -(t * x) := by ring
      rw [this, Real.cos_neg]
    rw [h_cos]
    exact lebesgue_integral_cos_div_sq_add_one_of_nonneg (by linarith)
