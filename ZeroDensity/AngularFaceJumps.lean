import ZeroDensity.PolygonFaces
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! One-sided derivatives of an actual finite polygon support function.
The right derivative is the greatest tangential coordinate on the face; the
left derivative is the least. Their difference is the exact face length.
No derivative-jump or face-endpoint hypothesis is supplied.
-/
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace ZeroDensity.AngularFaceJumps
open PolygonFaces

def support (s : Finset ℂ) (hs : s.Nonempty) (θ : ℝ) : ℝ :=
  s.sup' hs (normalLinear θ)

theorem normal_rotation (θ h : ℝ) (z : ℂ) :
    normalLinear (θ+h) z = normalLinear θ z * Real.cos h +
      angularTangent θ z * Real.sin h := by
  simp [normalLinear, angularTangent, SupportingGeometry.tangent,
    Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im,
    Real.cos_add, Real.sin_add]
  ring

theorem normal_continuous (z : ℂ) : Continuous (fun θ => normalLinear θ z) := by
  change Continuous (fun θ => Real.cos θ * z.re + Real.sin θ * z.im)
  fun_prop

theorem support_right_eventually_eq (s : Finset ℂ) (hs : s.Nonempty)
    (θ : ℝ) {p : ℂ} (hp : p ∈ maximizingPoints s hs (normalLinear θ))
    (hmax : ∀ y ∈ maximizingPoints s hs (normalLinear θ),
      angularTangent θ y ≤ angularTangent θ p) :
    support s hs =ᶠ[𝓝[Ici θ] θ] (fun η => normalLinear η p) := by
  classical
  have hmembers : ∀ y ∈ s, ∀ᶠ η in 𝓝 θ,
      θ ≤ η → η ≤ θ+Real.pi → normalLinear η y ≤ normalLinear η p := by
    intro y hy
    by_cases hf : y ∈ maximizingPoints s hs (normalLinear θ)
    · apply Filter.Eventually.of_forall
      intro η hη hupper
      have hn : normalLinear θ y = normalLinear θ p :=
        (Finset.mem_filter.mp hf).2.trans (Finset.mem_filter.mp hp).2.symm
      have hsin : 0 ≤ Real.sin (η-θ) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
      have hymax := hmax y hf
      have he : η = θ+(η-θ) := by ring
      rw [he, normal_rotation, normal_rotation, hn]
      exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hymax hsin)
    · have hlt : normalLinear θ y < normalLinear θ p := by
        have hle := Finset.le_sup' (normalLinear θ) hy
        have hne : normalLinear θ y ≠ s.sup' hs (normalLinear θ) := by
          intro he
          exact hf (Finset.mem_filter.mpr ⟨hy, he⟩)
        rw [(Finset.mem_filter.mp hp).2]
        exact lt_of_le_of_ne hle hne
      have hn := (normal_continuous y).continuousAt.eventually_lt
        (normal_continuous p).continuousAt hlt
      filter_upwards [hn] with η hη _ _
      exact hη.le
  have hall : ∀ᶠ η in 𝓝 θ, ∀ y ∈ s,
      θ ≤ η → η ≤ θ+Real.pi → normalLinear η y ≤ normalLinear η p := by
    rw [Filter.eventually_all_finset]
    exact hmembers
  have hu : ∀ᶠ η in 𝓝[Ici θ] θ, η < θ+Real.pi :=
    (eventually_lt_nhds (by linarith [Real.pi_pos] : θ < θ+Real.pi)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin, hu]
    with η hη hlo hhi
  apply le_antisymm
  · exact Finset.sup'_le hs (normalLinear η) fun y hy => hη y hy hlo hhi.le
  · exact Finset.le_sup' (normalLinear η) (Finset.mem_filter.mp hp).1

theorem support_left_eventually_eq (s : Finset ℂ) (hs : s.Nonempty)
    (θ : ℝ) {p : ℂ} (hp : p ∈ maximizingPoints s hs (normalLinear θ))
    (hmin : ∀ y ∈ maximizingPoints s hs (normalLinear θ),
      angularTangent θ p ≤ angularTangent θ y) :
    support s hs =ᶠ[𝓝[Iic θ] θ] (fun η => normalLinear η p) := by
  classical
  have hmembers : ∀ y ∈ s, ∀ᶠ η in 𝓝 θ,
      θ-Real.pi ≤ η → η ≤ θ → normalLinear η y ≤ normalLinear η p := by
    intro y hy
    by_cases hf : y ∈ maximizingPoints s hs (normalLinear θ)
    · apply Filter.Eventually.of_forall
      intro η hlower hη
      have hn : normalLinear θ y = normalLinear θ p :=
        (Finset.mem_filter.mp hf).2.trans (Finset.mem_filter.mp hp).2.symm
      have hsin : Real.sin (η-θ) ≤ 0 :=
        Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith)
      have hymin := hmin y hf
      have he : η = θ+(η-θ) := by ring
      rw [he, normal_rotation, normal_rotation, hn]
      exact add_le_add (le_refl _) (mul_le_mul_of_nonpos_right hymin hsin)
    · have hlt : normalLinear θ y < normalLinear θ p := by
        have hle := Finset.le_sup' (normalLinear θ) hy
        have hne : normalLinear θ y ≠ s.sup' hs (normalLinear θ) := by
          intro he
          exact hf (Finset.mem_filter.mpr ⟨hy, he⟩)
        rw [(Finset.mem_filter.mp hp).2]
        exact lt_of_le_of_ne hle hne
      have hn := (normal_continuous y).continuousAt.eventually_lt
        (normal_continuous p).continuousAt hlt
      filter_upwards [hn] with η hη _ _
      exact hη.le
  have hall : ∀ᶠ η in 𝓝 θ, ∀ y ∈ s,
      θ-Real.pi ≤ η → η ≤ θ → normalLinear η y ≤ normalLinear η p := by
    rw [Filter.eventually_all_finset]
    exact hmembers
  have hl : ∀ᶠ η in 𝓝[Iic θ] θ, θ-Real.pi < η :=
    (eventually_gt_nhds (by linarith [Real.pi_pos] : θ-Real.pi < θ)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hall.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin, hl]
    with η hη hhi hlo
  apply le_antisymm
  · exact Finset.sup'_le hs (normalLinear η) fun y hy => hη y hy hlo.le hhi
  · exact Finset.le_sup' (normalLinear η) (Finset.mem_filter.mp hp).1

/-- Actual one-sided derivatives, including every degenerate polygon. -/
theorem support_one_sided_derivatives (s : Finset ℂ) (hs : s.Nonempty) (θ : ℝ) :
    HasDerivWithinAt (support s hs)
      ((maximizingPoints s hs (normalLinear θ)).sup'
        (maximizingPoints_nonempty s hs (normalLinear θ)) (angularTangent θ)) (Ici θ) θ ∧
    HasDerivWithinAt (support s hs)
      ((maximizingPoints s hs (normalLinear θ)).inf'
        (maximizingPoints_nonempty s hs (normalLinear θ)) (angularTangent θ)) (Iic θ) θ := by
  classical
  let F := maximizingPoints s hs (normalLinear θ)
  have hF : F.Nonempty := maximizingPoints_nonempty s hs (normalLinear θ)
  obtain ⟨p, hp, hmax⟩ := Finset.exists_mem_eq_sup' hF (angularTangent θ)
  obtain ⟨q, hq, hmin⟩ := Finset.exists_mem_eq_inf' hF (angularTangent θ)
  constructor
  · rw [hmax]
    have hmp : ∀ y ∈ maximizingPoints s hs (normalLinear θ),
        angularTangent θ y ≤ angularTangent θ p := by
      intro y hy
      rw [← hmax]
      exact Finset.le_sup' (s := F) _ hy
    exact (normal_hasDeriv p θ).hasDerivWithinAt.congr_of_eventuallyEq
      (support_right_eventually_eq s hs θ hp hmp) (Finset.mem_filter.mp hp).2.symm
  · rw [hmin]
    have hmq : ∀ y ∈ maximizingPoints s hs (normalLinear θ),
        angularTangent θ q ≤ angularTangent θ y := by
      intro y hy
      rw [← hmin]
      exact Finset.inf'_le (s := F) _ hy
    exact (normal_hasDeriv q θ).hasDerivWithinAt.congr_of_eventuallyEq
      (support_left_eventually_eq s hs θ hq hmq) (Finset.mem_filter.mp hq).2.symm

/-- The actual derivatives, rather than named candidate slopes, give exactly
the Euclidean face-length coefficient in the manuscript formula. -/
theorem derivative_jump_eq_faceLength (s : Finset ℂ) (hs : s.Nonempty) (θ : ℝ) :
    derivWithin (support s hs) (Ici θ) θ -
      derivWithin (support s hs) (Iic θ) θ =
        MainTheorem.faceLength (convexHull ℝ (s : Set ℂ)) θ := by
  obtain ⟨hr, hl⟩ := support_one_sided_derivatives s hs θ
  rw [hr.derivWithin (uniqueDiffWithinAt_Ici θ),
    hl.derivWithin (uniqueDiffWithinAt_Iic θ)]
  exact (actualFace_length_range s hs θ).symm

theorem derivative_jump_nonnegative (s : Finset ℂ) (hs : s.Nonempty) (θ : ℝ) :
    0 ≤ derivWithin (support s hs) (Ici θ) θ -
      derivWithin (support s hs) (Iic θ) θ := by
  rw [derivative_jump_eq_faceLength]
  exact Metric.diam_nonneg

#print axioms support_one_sided_derivatives
#print axioms derivative_jump_eq_faceLength
end ZeroDensity.AngularFaceJumps
