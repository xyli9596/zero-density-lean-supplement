import ZeroDensity.AngularFaceJumps
import Mathlib.Tactic

/-!
# Local hinge representation of a polygon support function

At each nonzero point, the actual support function of a finite nonempty
polygon agrees locally with a linear function plus its true supporting-face
length times a positive-part linear function. Collinear defining points and
degenerate segments or singleton hulls are included.
-/
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace V10.LocalSupportFace
open ZeroDensity PolygonFaces

def projection (ν z : ℂ) : ℝ := (ν * star z).re

def support (s : Finset ℂ) (hs : s.Nonempty) (z : ℂ) : ℝ :=
  s.sup' hs (fun ν => projection ν z)

theorem projection_continuous (ν : ℂ) : Continuous (projection ν) := by
  unfold projection
  fun_prop

theorem support_continuous (s : Finset ℂ) (hs : s.Nonempty) :
    Continuous (support s hs) :=
  Continuous.finset_sup'_apply hs fun ν _ => projection_continuous ν

theorem tangent_coordinates (θ : ℝ) (z : ℂ) :
    angularTangent θ z = -Real.sin θ * z.re + Real.cos θ * z.im := by
  simp [angularTangent, SupportingGeometry.tangent, Complex.mul_re,
    Complex.mul_im, Complex.exp_re, Complex.exp_im]
  ring

theorem projection_rotated (θ : ℝ) (ν z : ℂ) :
    projection ν z = normalLinear θ ν * normalLinear θ z +
      angularTangent θ ν * angularTangent θ z := by
  simp only [tangent_coordinates]
  have h : ν.re * z.re + ν.im * z.im =
    (Real.cos θ * ν.re + Real.sin θ * ν.im) *
      (Real.cos θ * z.re + Real.sin θ * z.im) +
    (-Real.sin θ * ν.re + Real.cos θ * ν.im) *
      (-Real.sin θ * z.re + Real.cos θ * z.im) := by
    calc
      _ = (Real.sin θ ^ 2 + Real.cos θ ^ 2) * (ν.re * z.re + ν.im * z.im) := by
        rw [Real.sin_sq_add_cos_sq, one_mul]
      _ = _ := by ring
  simpa [projection, normalLinear, Complex.mul_re] using h

theorem projection_ray (r θ : ℝ) (ν : ℂ) :
    projection ν ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
      r * normalLinear θ ν := by
  simp [projection, normalLinear, Complex.mul_re, Complex.mul_im,
    Complex.exp_re, Complex.exp_im]
  ring

/-- Every point on the actual maximizing face lies between its two extreme
tangential coordinates, in every linear projection. -/
theorem projection_le_max_of_face {s : Finset ℂ} {hs : s.Nonempty}
    {θ : ℝ} {p q y : ℂ}
    (hp : p ∈ maximizingPoints s hs (normalLinear θ))
    (hq : q ∈ maximizingPoints s hs (normalLinear θ))
    (hy : y ∈ maximizingPoints s hs (normalLinear θ))
    (hlo : angularTangent θ p ≤ angularTangent θ y)
    (hhi : angularTangent θ y ≤ angularTangent θ q) (z : ℂ) :
    projection y z ≤ max (projection p z) (projection q z) := by
  have hnp : normalLinear θ y = normalLinear θ p :=
    (Finset.mem_filter.mp hy).2.trans (Finset.mem_filter.mp hp).2.symm
  have hnq : normalLinear θ y = normalLinear θ q :=
    (Finset.mem_filter.mp hy).2.trans (Finset.mem_filter.mp hq).2.symm
  by_cases hz : 0 ≤ angularTangent θ z
  · apply le_trans _ (le_max_right _ _)
    rw [projection_rotated θ y z, projection_rotated θ q z, hnq]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hhi hz)
  · apply le_trans _ (le_max_left _ _)
    rw [projection_rotated θ y z, projection_rotated θ p z, hnp]
    exact add_le_add le_rfl (mul_le_mul_of_nonpos_right hlo (le_of_not_ge hz))

/-- The local linear-plus-hinge formula. The coefficient is the Euclidean
diameter of the actual supporting face, not an assumed jump. -/
theorem support_eventually_hinge (s : Finset ℂ) (hs : s.Nonempty)
    {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    ∃ p ∈ s, ∃ q ∈ s,
      p ∈ maximizingPoints s hs (normalLinear θ) ∧
      q ∈ maximizingPoints s hs (normalLinear θ) ∧
      angularTangent θ q - angularTangent θ p =
        MainTheorem.faceLength (convexHull ℝ (s : Set ℂ)) θ ∧
      ∀ᶠ z in 𝓝 ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)),
        support s hs z = projection p z +
          MainTheorem.faceLength (convexHull ℝ (s : Set ℂ)) θ *
            max 0 (angularTangent θ z) := by
  classical
  let F := maximizingPoints s hs (normalLinear θ)
  have hF : F.Nonempty := maximizingPoints_nonempty s hs (normalLinear θ)
  obtain ⟨p, hp, hmin⟩ := Finset.exists_mem_eq_inf' hF (angularTangent θ)
  obtain ⟨q, hq, hmax⟩ := Finset.exists_mem_eq_sup' hF (angularTangent θ)
  have hlo : ∀ y ∈ F, angularTangent θ p ≤ angularTangent θ y := by
    intro y hy
    rw [← hmin]
    exact Finset.inf'_le _ hy
  have hhi : ∀ y ∈ F, angularTangent θ y ≤ angularTangent θ q := by
    intro y hy
    rw [← hmax]
    exact Finset.le_sup' _ hy
  have hd : angularTangent θ q - angularTangent θ p =
      MainTheorem.faceLength (convexHull ℝ (s : Set ℂ)) θ := by
    rw [actualFace_length_range s hs θ, hmax, hmin]
  have hnpq : normalLinear θ p = normalLinear θ q :=
    (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
  have hmembers : ∀ y ∈ s, ∀ᶠ z in
      𝓝 ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)),
      projection y z ≤ max (projection p z) (projection q z) := by
    intro y hy
    by_cases hf : y ∈ F
    · exact Filter.Eventually.of_forall fun z =>
        projection_le_max_of_face hp hq hf (hlo y hf) (hhi y hf) z
    · have hlt : normalLinear θ y < normalLinear θ p := by
        rw [(Finset.mem_filter.mp hp).2]
        exact lt_of_le_of_ne (Finset.le_sup' _ hy) (fun he =>
          hf (Finset.mem_filter.mpr ⟨hy, he⟩))
      have hlt' : projection y ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) <
          projection p ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
        rw [projection_ray, projection_ray]
        exact mul_lt_mul_of_pos_left hlt hr
      filter_upwards [(projection_continuous y).continuousAt.eventually_lt
        (projection_continuous p).continuousAt hlt'] with z hz
      exact hz.le.trans (le_max_left _ _)
  have hall : ∀ᶠ z in 𝓝 ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)),
      ∀ y ∈ s, projection y z ≤ max (projection p z) (projection q z) := by
    rw [Filter.eventually_all_finset]
    exact hmembers
  refine ⟨p, (Finset.mem_filter.mp hp).1, q, (Finset.mem_filter.mp hq).1,
    hp, hq, hd, ?_⟩
  filter_upwards [hall] with z hz
  have he : support s hs z = max (projection p z) (projection q z) := by
    unfold support
    apply le_antisymm
    · exact Finset.sup'_le hs _ hz
    · exact max_le (Finset.le_sup' (fun ν => projection ν z) (Finset.mem_filter.mp hp).1)
        (Finset.le_sup' (fun ν => projection ν z) (Finset.mem_filter.mp hq).1)
  rw [he, ← hd]
  have hproj : projection q z - projection p z =
      (angularTangent θ q - angularTangent θ p) * angularTangent θ z := by
    rw [projection_rotated θ q z, projection_rotated θ p z, hnpq]
    ring
  have hd0 : 0 ≤ angularTangent θ q - angularTangent θ p :=
    sub_nonneg.mpr (hhi p hp)
  by_cases ht : 0 ≤ angularTangent θ z
  · rw [max_eq_right ht, max_eq_right (by nlinarith [mul_nonneg hd0 ht])]
    linarith
  · rw [max_eq_left (le_of_not_ge ht), mul_zero, add_zero,
      max_eq_left (by nlinarith [mul_nonpos_of_nonneg_of_nonpos hd0 (le_of_not_ge ht)])]

#print axioms support_eventually_hinge
end V10.LocalSupportFace
