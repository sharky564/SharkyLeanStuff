import Mathlib.Data.Complex.Basic
import Mathlib.Data.Set.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Complex Topology MeasureTheory Filter Set

namespace ContourIntegral

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

def boundaryRect (z w : ℂ) : Set ℂ :=
  {p : ℂ | (p.re = z.re ∨ p.re = w.re) ∧ p.im ∈ uIcc z.im w.im} ∪
  {p : ℂ | (p.im = z.im ∨ p.im = w.im) ∧ p.re ∈ uIcc z.re w.re}

def interiorRect (z w : ℂ) : Set ℂ :=
  {p : ℂ | p.re ∈ Ioo (min z.re w.re) (max z.re w.re) ∧
           p.im ∈ Ioo (min z.im w.im) (max z.im w.im)}

def filledRect (z w : ℂ) : Set ℂ :=
  {p : ℂ | p.re ∈ uIcc z.re w.re ∧ p.im ∈ uIcc z.im w.im}

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

end ContourIntegral
