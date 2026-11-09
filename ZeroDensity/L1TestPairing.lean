import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! The rigorous L¹-to-test-function bridge used before zero-measure convergence.
The weak Laplacian pairing uses mathlib's actual Euclidean Laplacian. Scalar
logarithmic L¹ existence and the Poincaré–Lelong identity are not assumed proved. -/
namespace ZeroDensity.L1TestPairing
open Filter MeasureTheory
open scoped Topology Laplacian
noncomputable section

lemma pairing_error_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u H w : α → ℝ} {C : ℝ} (hu : Integrable u μ) (hH : Integrable H μ)
    (hw : AEStronglyMeasurable w μ) (hbound : ∀ᵐ x ∂μ, ‖w x‖ ≤ C) :
    ‖(∫ x, w x * u x ∂μ) - ∫ x, w x * H x ∂μ‖ ≤
      C * ∫ x, ‖u x - H x‖ ∂μ := by
  have hwu := hu.bdd_mul hw hbound
  have hwH := hH.bdd_mul hw hbound
  rw [← integral_sub hwu hwH]
  have heq : (fun x => w x * u x - w x * H x) = fun x => w x * (u x - H x) := by
    funext x
    ring
  rw [heq]
  calc
    ‖∫ x, w x * (u x - H x) ∂μ‖ ≤ ∫ x, C * ‖u x - H x‖ ∂μ := by
      apply norm_integral_le_of_norm_le ((hu.sub hH).norm.const_mul C)
      filter_upwards [hbound] with x hx
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    _ = C * ∫ x, ‖u x - H x‖ ∂μ := integral_const_mul _ _

/-- Local L¹ convergence gives convergence against every bounded measurable
weight, including a smooth test function's Laplacian on a compact domain. -/
theorem pairing_tendsto {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {l : Filter ι} {u : ι → α → ℝ} {H w : α → ℝ} {C : ℝ}
    (hu : ∀ i, Integrable (u i) μ) (hH : Integrable H μ)
    (hw : AEStronglyMeasurable w μ) (hbound : ∀ᵐ x ∂μ, ‖w x‖ ≤ C)
    (hL1 : Tendsto (fun i => ∫ x, ‖u i x - H x‖ ∂μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, w x * u i x ∂μ) l (𝓝 (∫ x, w x * H x ∂μ)) := by
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) _
    (by simpa using hL1.const_mul C)
  exact Eventually.of_forall fun i => pairing_error_bound (hu i) hH hw hbound

/-- The local weak distributional Laplacian is defined by its genuine test
pairing against the Euclidean Laplacian of the test function. -/
def weakLaplacianPairing (μ : Measure ℂ) (u φ : ℂ → ℝ) : ℝ :=
  ∫ z, (Δ φ) z * u z ∂μ

theorem weakLaplacianPairing_tendsto {ι : Type*} {l : Filter ι} {μ : Measure ℂ}
    {u : ι → ℂ → ℝ} {H φ : ℂ → ℝ} {C : ℝ}
    (hu : ∀ i, Integrable (u i) μ) (hH : Integrable H μ)
    (hφ : AEStronglyMeasurable (Δ φ) μ)
    (hbound : ∀ᵐ z ∂μ, ‖(Δ φ) z‖ ≤ C)
    (hL1 : Tendsto (fun i => ∫ z, ‖u i z - H z‖ ∂μ) l (𝓝 0)) :
    Tendsto (fun i => weakLaplacianPairing μ (u i) φ) l
      (𝓝 (weakLaplacianPairing μ H φ)) :=
  pairing_tendsto hu hH hφ hbound hL1

/-- On a compact test domain the bound on the genuine test Laplacian is derived
from continuity, so it need not be supplied as an independent estimate. -/
theorem weakLaplacianPairing_tendsto_on_compact {ι : Type*} {l : Filter ι}
    {K : Set ℂ} (hK : IsCompact K) {u : ι → ℂ → ℝ} {H φ : ℂ → ℝ}
    (hu : ∀ i, Integrable (u i) (volume.restrict K))
    (hH : Integrable H (volume.restrict K)) (hφ : Continuous (Δ φ))
    (hL1 : Tendsto (fun i => ∫ z, ‖u i z - H z‖ ∂(volume.restrict K)) l (𝓝 0)) :
    Tendsto (fun i => weakLaplacianPairing (volume.restrict K) (u i) φ) l
      (𝓝 (weakLaplacianPairing (volume.restrict K) H φ)) := by
  obtain ⟨C, hC⟩ := hK.bddAbove_image hφ.norm.continuousOn
  apply weakLaplacianPairing_tendsto (C := C) hu hH hφ.aestronglyMeasurable ?_ hL1
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  exact hC ⟨z, hz, rfl⟩

#print axioms pairing_error_bound
#print axioms pairing_tendsto
#print axioms weakLaplacianPairing_tendsto
#print axioms weakLaplacianPairing_tendsto_on_compact
end
end ZeroDensity.L1TestPairing
