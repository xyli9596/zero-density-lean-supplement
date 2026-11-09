import V10.ScalarL1LocalLimit
import V10.ScalarL1LocalToGlobal
import V10.PerronNonvanishing
import Mathlib.Tactic

/-!
# Scalar L¹_loc convergence from the actual jet ODE

The local inputs concern only coefficients and scaled domains. Actual
nonvanishing follows from uniqueness of the ODE; analyticity of the scalar
function follows from its jet derivative. Perron supplies the actual vector
limit on each compact disk, and the proved scalar compactness/identification
theorems supply full scalar L¹ convergence. A finite cover then handles every
compact subset of the target phase domain.
-/

noncomputable section
open Filter Set Metric MeasureTheory
open scoped Topology NNReal
namespace V10.ScalarL1GlobalLimit
set_option backward.isDefEq.respectTransparency false

/-- Full real-parameter scalar L¹_loc convergence, with no assumed convergence
or compactness of logarithmic potentials. The limit is the actual limsup of
the actual jet potentials. -/
theorem actual_scalar_L1_on_compacts {n : ℕ} (hn : 0 < n)
    {v : ℂ → ℂ} {S D : Set ℂ}
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
        (∀ z ∈ N, Tendsto (fun R : ℝ => A ((R : ℂ) * z)) atTop (𝓝 A₀))) :
    ∀ K, IsCompact K → K ⊆ D →
      Tendsto (fun R : ℝ => ∫ z in K,
        ‖ScalarAnalytic.potential v R z -
          PerronVectorLimit.indicator (ZeroDensity.ScalarLimit.jet n v) z‖)
        atTop (𝓝 0) := by
  have hv := ScalarAnalytic.analyticOnNhd_of_jet_ode hn hS hode
  have hne := PerronNonvanishing.nowhere_zero hS hconn hA hode hnonzero
  apply ScalarL1LocalToGlobal.L1_on_compacts_of_eventual_local_disks
  intro x hx
  obtain ⟨N, hNo, hxN, hND, hNc, hNzero, M, hmap, hbound, hAlim⟩ := hlocal x hx
  obtain ⟨ε, hε, hεN⟩ := Metric.mem_nhds_iff.mp (hNo.mem_nhds hxN)
  let r : ℝ := ε / 20
  have hr : 0 < r := div_pos hε (by norm_num)
  have hbig : closedBall x (10 * r) ⊆ N := by
    apply subset_trans _ hεN
    apply closedBall_subset_ball
    dsimp [r]
    linarith
  have hsmall : closedBall x r ⊆ D :=
    (closedBall_subset_closedBall (by linarith : r ≤ 10 * r)).trans (hbig.trans hND)
  obtain ⟨hV, _, hH, _⟩ := PerronVectorLimit.actual_vector_compact_limit
    hNc (isCompact_closedBall x (10 * r)) hbig hNzero hA hode hne hmap hbound hAlim
  have hDS : ∀ᶠ R : ℝ in atTop, ∀ z ∈ closedBall x (10 * r), (R : ℂ) * z ∈ S :=
    hmap.mono fun R hR z hz => hR z (hbig hz)
  have hjet : ∀ᶠ R : ℝ in atTop, ∀ z ∈ closedBall x (10 * r),
      ZeroDensity.ScalarLimit.jet n v ((R : ℂ) * z) ≠ 0 :=
    hDS.mono fun R hR z hz => hne _ (hR z hz)
  obtain ⟨hi, ht⟩ := ScalarL1LocalLimit.actual_scalar_L1_on_closedBall hn hr hS hconn
    hv hDS (hH.mono hbig) hV hjet
  exact ⟨r, hr, hsmall, hi, ht⟩

#print axioms actual_scalar_L1_on_compacts
end V10.ScalarL1GlobalLimit
