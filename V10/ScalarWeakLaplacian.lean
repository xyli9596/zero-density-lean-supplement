import V10.ScalarL1GlobalLimit
import ZeroDensity.L1TestPairing
import Mathlib.Tactic

/-!
# Actual scalar logarithms and weak Laplacian test pairings

Only eventual integrability is required. This matters on expanding analytic
domains: a fixed small scale need not map an entire compact test set into the
original exterior sector. The actual ODE endpoint below derives integrability,
the vector indicator, and scalar L¹ convergence before applying the genuine
Euclidean test Laplacian. No logarithmic Dirac identity is asserted here.
-/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal Laplacian
namespace V10.ScalarWeakLaplacian
set_option backward.isDefEq.respectTransparency false

/-- Eventual integrability suffices for the L¹-to-test-pairing bridge. -/
theorem pairing_tendsto_of_eventually_integrable
    {α ι : Type*} [MeasurableSpace α] {μ : Measure α} {l : Filter ι}
    {u : ι → α → ℝ} {H w : α → ℝ} {C : ℝ}
    (hu : ∀ᶠ i in l, Integrable (u i) μ) (hH : Integrable H μ)
    (hw : AEStronglyMeasurable w μ) (hbound : ∀ᵐ x ∂μ, ‖w x‖ ≤ C)
    (hL1 : Tendsto (fun i => ∫ x, ‖u i x - H x‖ ∂μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, w x * u i x ∂μ) l (𝓝 (∫ x, w x * H x ∂μ)) := by
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) _
    (by simpa using hL1.const_mul C)
  filter_upwards [hu] with i hi
  exact ZeroDensity.L1TestPairing.pairing_error_bound hi hH hw hbound

/-- A continuous actual test Laplacian is bounded on a compact test domain;
the scalar potentials need only be integrable at sufficiently large scales. -/
theorem weakLaplacianPairing_tendsto_on_compact_eventually
    {ι : Type*} {l : Filter ι} {K : Set ℂ} (hK : IsCompact K)
    {u : ι → ℂ → ℝ} {H φ : ℂ → ℝ}
    (hu : ∀ᶠ i in l, IntegrableOn (u i) K)
    (hH : IntegrableOn H K) (hφ : Continuous (Δ φ))
    (hL1 : Tendsto (fun i => ∫ z in K, ‖u i z - H z‖) l (𝓝 0)) :
    Tendsto (fun i => ZeroDensity.L1TestPairing.weakLaplacianPairing
      (volume.restrict K) (u i) φ) l
      (𝓝 (ZeroDensity.L1TestPairing.weakLaplacianPairing (volume.restrict K) H φ)) := by
  obtain ⟨C, hC⟩ := hK.bddAbove_image hφ.norm.continuousOn
  apply pairing_tendsto_of_eventually_integrable (C := C) hu hH
    hφ.aestronglyMeasurable _ hL1
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  exact hC ⟨z, hz, rfl⟩

/-- A finite cover turns eventual local assertions into one eventual
assertion on a compact set. No common threshold on the full domain is needed. -/
theorem eventually_on_compact_of_locally {X ι : Type*} [TopologicalSpace X]
    {l : Filter ι} {K : Set X} (hK : IsCompact K) {P : ι → X → Prop}
    (hlocal : ∀ x ∈ K, ∃ N : Set X, IsOpen N ∧ x ∈ N ∧
      ∀ᶠ i in l, ∀ y ∈ N, P i y) :
    ∀ᶠ i in l, ∀ x ∈ K, P i x := by
  classical
  choose N hNo hxN he using (fun x : K => hlocal x x.property)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover N hNo (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxN ⟨x, hx⟩⟩)
  have he' : ∀ᶠ i in l, ∀ x ∈ t, ∀ y ∈ N x, P i y :=
    (eventually_all_finset t).mpr (fun x _ => he x)
  filter_upwards [he'] with i hi x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (ht hx)
  exact hi y hy x hxy

/-- The actual jet ODE and coefficient hypotheses give convergence against
the genuine test Laplacian on every compact subset of the phase domain.
Neither scalar L¹ convergence nor any logarithmic-potential integrability is
assumed. The conclusion is a test pairing, not yet a zero-measure formula. -/
theorem actual_scalar_weakLaplacian_tendsto_on_compacts
    {n : ℕ} (hn : 0 < n) {v : ℂ → ℂ} {S D : Set ℂ}
    (hS : IsOpen S) (hconn : IsPreconnected S)
    {A : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)}
    {A₀ : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)}
    (hA : ContinuousOn A S)
    (hode : ∀ z ∈ S, HasDerivAt (ZeroDensity.ScalarLimit.jet n v)
      (A z (ZeroDensity.ScalarLimit.jet n v z)) z)
    (hnonzero : ∃ z ∈ S, ZeroDensity.ScalarLimit.jet n v z ≠ 0)
    (hlocal : ∀ x ∈ D, ∃ N : Set ℂ, IsOpen N ∧ x ∈ N ∧ N ⊆ D ∧
      Convex ℝ N ∧ (∀ z ∈ N, z ≠ 0) ∧ ∃ M : ℝ≥0,
        (∀ᶠ R : ℝ in atTop, ∀ z ∈ N, (R : ℂ) * z ∈ S) ∧
        (∀ᶠ R : ℝ in atTop, ∀ z ∈ N, ‖A ((R : ℂ) * z)‖ ≤ M) ∧
        (∀ z ∈ N, Tendsto (fun R : ℝ => A ((R : ℂ) * z)) atTop (𝓝 A₀)))
    {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ D)
    {φ : ℂ → ℝ} (hφ : Continuous (Δ φ)) :
    Tendsto (fun R : ℝ => ZeroDensity.L1TestPairing.weakLaplacianPairing
      (volume.restrict K) (ScalarAnalytic.potential v R) φ) atTop
      (𝓝 (ZeroDensity.L1TestPairing.weakLaplacianPairing (volume.restrict K)
        (PerronVectorLimit.indicator (ZeroDensity.ScalarLimit.jet n v)) φ)) := by
  have hv := ScalarAnalytic.analyticOnNhd_of_jet_ode hn hS hode
  have hne := PerronNonvanishing.nowhere_zero hS hconn hA hode hnonzero
  have hmap : ∀ᶠ R : ℝ in atTop, ∀ z ∈ K, (R : ℂ) * z ∈ S := by
    apply eventually_on_compact_of_locally hK
    intro x hx
    obtain ⟨N, hNo, hxN, _, _, _, M, hmap, _, _⟩ := hlocal x (hKD hx)
    exact ⟨N, hNo, hxN, hmap⟩
  have hH : ContinuousOn
      (PerronVectorLimit.indicator (ZeroDensity.ScalarLimit.jet n v)) K := by
    intro x hx
    obtain ⟨N, hNo, hxN, _, hNc, hNz, M, hmapN, hbound, hlim⟩ := hlocal x (hKD hx)
    have hsingle : ({x} : Set ℂ) ⊆ N := singleton_subset_iff.mpr hxN
    obtain ⟨_, _, hc, _⟩ := PerronVectorLimit.actual_vector_compact_limit
      hNc isCompact_singleton hsingle hNz hA hode hne hmapN hbound hlim
    exact (hc.continuousAt (hNo.mem_nhds hxN)).continuousWithinAt
  have hi : ∀ᶠ R : ℝ in atTop, IntegrableOn (ScalarAnalytic.potential v R) K := by
    obtain ⟨z₀, hz₀, hn₀⟩ := hnonzero
    filter_upwards [hmap, eventually_gt_atTop (0 : ℝ)] with R hRmap hR
    exact ScalarAnalytic.potential_integrableOn_compact hS hconn hv hz₀ hn₀
      hR.ne' hRmap Subset.rfl hK
  exact weakLaplacianPairing_tendsto_on_compact_eventually hK hi
    (hH.integrableOn_compact hK) hφ
    (ScalarL1GlobalLimit.actual_scalar_L1_on_compacts hn hS hconn hA hode hnonzero
      hlocal K hK hKD)

#print axioms pairing_tendsto_of_eventually_integrable
#print axioms weakLaplacianPairing_tendsto_on_compact_eventually
#print axioms eventually_on_compact_of_locally
#print axioms actual_scalar_weakLaplacian_tendsto_on_compacts
end V10.ScalarWeakLaplacian
