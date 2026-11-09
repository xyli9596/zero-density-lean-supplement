import V10.SmoothTestApproximation
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Local mass bounds derived from smooth-test convergence

The cutoff is genuinely constructed inside the open domain and equals one
near the given compact set. Positivity of measures then bounds the compact
mass by this one convergent test integral. No uniform mass bound is assumed.
The limiting smooth-test functional need not yet be represented by a measure.
-/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
namespace V10.SmoothMeasureMass

/-- A smooth compactly supported cutoff inside an open domain, equal to one
on a prescribed compact subset and taking values in `[0,1]`. -/
theorem exists_smooth_cutoff {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ U ∧
      (∀ z, 0 ≤ ψ z) ∧ (∀ z ∈ K, ψ z = 1) := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hKt : K ⊆ interior (cthickening δ K) :=
    (self_subset_thickening hδ K).trans (thickening_subset_interior_cthickening δ K)
  obtain ⟨ψ, hψ1, hψ0, hψrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (modelWithCornersSelf ℝ ℂ) (n := ⊤) hK.isClosed hKt
  have hs : Function.support (ψ : ℂ → ℝ) ⊆ cthickening δ K := by
    intro z hz
    by_contra hn
    exact hz (hψ0 z hn)
  have hts : tsupport (ψ : ℂ → ℝ) ⊆ cthickening δ K :=
    closure_minimal hs isClosed_cthickening
  exact ⟨ψ, ψ.contMDiff.contDiff,
    HasCompactSupport.of_support_subset_isCompact hK.cthickening hs,
    hts.trans hδU, fun z => (hψrange z).1, hψ1.self_of_nhdsSet⟩

/-- Smooth-test convergence itself forces eventual local bounds for positive
measures. The limit may be an arbitrary prescribed smooth-test functional. -/
theorem eventually_bounded_mass_on_compact
    {ι : Type*} {l : Filter ι} {μ : ι → Measure ℂ}
    [∀ i, IsFiniteMeasureOnCompacts (μ i)]
    {U : Set ℂ} (hU : IsOpen U) {L : (ℂ → ℝ) → ℝ}
    (htest : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      Tendsto (fun i => ∫ z, ψ z ∂μ i) l (𝓝 (L ψ)))
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ i in l, (μ i).real K ≤ M := by
  obtain ⟨ψ, hψ, hψc, hψU, hψnonneg, hψ1⟩ := exists_smooth_cutoff hK hU hKU
  let M := |L ψ| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have he : ∀ᶠ i in l, (∫ z, ψ z ∂μ i) < M :=
    (htest ψ hψ hψc hψU).eventually
      (eventually_lt_nhds (by dsimp [M]; linarith [le_abs_self (L ψ)]))
  refine ⟨M, hM, ?_⟩
  filter_upwards [he] with i hi
  have hbound := (hψ.continuous.integrable_of_hasCompactSupport hψc (μ := μ i)).measure_le_integral (ae_of_all _ hψnonneg) (fun z hz => (hψ1 z hz).ge)
  have hbound' : μ i K ≤ ENNReal.ofReal M :=
    hbound.trans (ENNReal.ofReal_le_ofReal hi.le)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound'
  simpa only [Measure.real, ENNReal.toReal_ofReal hM.le] using hreal

#print axioms exists_smooth_cutoff
#print axioms eventually_bounded_mass_on_compact
end V10.SmoothMeasureMass
