import V10.ScalarL1GlobalLimit
import V10.ScalarCoefficientLimits
import V10.SectorScaledNeighborhood
import V10.PerronVectorSubharmonic
import V10.SubharmonicLocal
import Mathlib.Tactic

/-!+# Lemma 3.2: the actual scalar indicator and L¹_loc limit on the full sector

The input is the original scalar ODE and uniform coefficient convergence on
compact angle sets. The companion system, spectral rates, scalar/vector
identification, local analytic compactness, and full L¹_loc convergence are
derived. The scalar limsup uses `-∞` at zeros; its finite real value is taken
only after the proof identifies it with the Perron rate.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace V10.ScalarIndicatorLimit
open CompanionObservation PerronSector SectorScaledNeighborhood
set_option backward.isDefEq.respectTransparency false

def angularIndicator (v : ℂ → ℂ) (θ : ℝ) : ℝ :=
  (ScalarIndicator.rayIndicator v (Complex.exp ((θ : ℂ) * Complex.I))).toReal

def homogeneousIndicator (v : ℂ → ℂ) (ζ : ℂ) : ℝ :=
  (ScalarIndicator.rayIndicator v ζ).toReal

theorem unit_ray_mem_fullCone {J : Set ℝ} {θ : ℝ} (hθ : θ ∈ J) :
    Complex.exp ((θ : ℂ) * Complex.I) ∈ fullCone J := by
  exact ⟨(θ : ℂ) * Complex.I, by simpa using hθ, rfl⟩

theorem positive_ray_mem_fullCone {J : Set ℝ} {θ ρ : ℝ} (hθ : θ ∈ J) (hρ : 0 < ρ) :
    (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ fullCone J := by
  refine ⟨(Real.log ρ : ℂ) + (θ : ℂ) * Complex.I, ?_, ?_⟩
  · simpa using hθ
  · rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hρ]

/-- Complete scalar indicator and L¹_loc conclusions of Lemma 3.2. The order
is written `n+1`, so every positive order is covered. Continuity of the
coefficients is weaker than their analyticity in the manuscript. -/
theorem lemma_3_2 {n : ℕ} {v : ℂ → ℂ} {b : ℂ → Fin (n + 1) → ℂ}
    {c : Fin (n + 1) → ℂ} {R₀ : ℝ} {J : Set ℝ}
    (hR₀ : 0 < R₀) (hJo : IsOpen J) (hJc : IsPreconnected J)
    (hv : AnalyticOnNhd ℂ v (sector R₀ J))
    (hb : ContinuousOn b (sector R₀ J))
    (hscalar : ∀ z ∈ sector R₀ J, iteratedDeriv (n + 1) v z +
      ∑ j : Fin (n + 1), b z j * iteratedDeriv j.val v z = 0)
    (hnontrivial : ∃ z ∈ sector R₀ J, v z ≠ 0)
    (hlim : ∀ j (K : Set ℝ), K ⊆ J → IsCompact K →
      TendstoUniformlyOn
        (fun r : ℝ => fun θ : ℝ => b ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) j)
        (fun _ => c j) atTop K) :
    ContinuousOn (homogeneousIndicator v) (fullCone J) ∧
    SubharmonicOn (homogeneousIndicator v) (fullCone J) ∧
    (∀ K, IsCompact K → K ⊆ fullCone J →
      Tendsto (fun R : ℝ => ∫ z in K,
        ‖ScalarAnalytic.potential v R z - homogeneousIndicator v z‖) atTop (𝓝 0)) ∧
    (∀ ζ ∈ fullCone J, ∃ μ : ℂ,
      μ ^ (n + 1) + ∑ j : Fin (n + 1), c j * μ ^ j.val = 0 ∧
      ScalarIndicator.rayIndicator v ζ = ((μ * ζ).re : EReal) ∧
      homogeneousIndicator v ζ = (μ * ζ).re) ∧
    ContinuousOn (angularIndicator v) J ∧
    (∀ θ ∈ J, ∀ (ρ : ℝ), 0 < ρ →
      homogeneousIndicator v ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
        ρ * angularIndicator v θ) := by
  let S := sector R₀ J
  let D := fullCone J
  let Y := ZeroDensity.ScalarLimit.jet (n + 1) v
  let A : ℂ → (Fin (n + 1) → ℂ) →L[ℂ] (Fin (n + 1) → ℂ) := fun z => companion (b z)
  let A₀ := companion c
  let H := PerronVectorLimit.indicator Y
  have hS : IsOpen S := sector_isOpen R₀ hJo
  have hSc : IsPreconnected S := sector_isPreconnected R₀ hJc
  have hA : ContinuousOn A S := ScalarCompanionODE.companion_continuous.comp_continuousOn hb
  have hode : ∀ z ∈ S, HasDerivAt Y (A z (Y z)) z :=
    fun z hz => ScalarCompanionODE.jet_hasDerivAt_companion (hv z hz) (b z) (hscalar z hz)
  have hne : ∀ z ∈ S, Y z ≠ 0 :=
    ScalarCompanionODE.jet_nowhere_zero_of_scalar_nontrivial hS hSc hv hb hscalar hnontrivial
  have hnY : ∃ z ∈ S, Y z ≠ 0 := by
    obtain ⟨z, hz, _⟩ := hnontrivial
    exact ⟨z, hz, hne z hz⟩
  have hAlim : ∀ K : Set ℝ, K ⊆ J → IsCompact K →
      TendstoUniformlyOn
        (fun r : ℝ => fun θ : ℝ => A ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
        (fun _ => A₀) atTop K := fun K hKJ hK =>
    ScalarCoefficientLimits.companion_uniform_limit (fun j => hlim j K hKJ hK)
  have hlocal := exists_scaled_neighborhood hR₀ hJo hAlim
  have hL1 := ScalarL1GlobalLimit.actual_scalar_L1_on_compacts
    (Nat.succ_pos n) hS hSc hA hode hnY hlocal
  have hSH : SubharmonicOn H D := by
    apply SubharmonicLocal.subharmonicOn_of_local
    intro x hx
    obtain ⟨N, hNo, hxN, _, hNc, hNzero, M, hmap, hbound, hpoint⟩ := hlocal x hx
    exact ⟨N, hNo, hxN, PerronVectorSubharmonic.actual_indicator_subharmonic
      hNo hNc hNzero hA hode hne hmap hbound hpoint⟩
  have hclass : ∀ ζ ∈ D, ∃ μ : ℂ,
      μ ^ (n + 1) + ∑ j : Fin (n + 1), c j * μ ^ j.val = 0 ∧
      Tendsto (fun R => PerronVectorLimit.potential Y R ζ) atTop (𝓝 (H ζ)) ∧
      H ζ = (μ * ζ).re ∧ ScalarIndicator.rayIndicator v ζ = ((μ * ζ).re : EReal) := by
    intro ζ hζ
    obtain ⟨N, _, hζN, _, _, hNzero, _, hmap, _, hpoint⟩ := hlocal ζ hζ
    obtain ⟨T, hT⟩ := eventually_atTop.mp hmap
    have hray : ∀ R ≥ T, (R : ℂ) * ζ ∈ S := fun R hR => hT R hR ζ hζN
    obtain ⟨μ, hrate, hind⟩ := ScalarIndicator.actual_jet_ray_classification c
      (hNzero ζ hζN) hA hray (hpoint ζ hζN) hode (hne _ (hray T le_rfl))
    have hHμ : H ζ = (μ.val * ζ).re := hrate.limsup_eq
    refine ⟨μ.val, CompanionRoots.eigenvalue_root_equation c μ.property, ?_, hHμ, hind⟩
    rwa [hHμ]
  have heq : EqOn (homogeneousIndicator v) H D := by
    intro ζ hζ
    obtain ⟨μ, _, _, hHμ, hs⟩ := hclass ζ hζ
    simp only [homogeneousIndicator, hs, EReal.toReal_coe, hHμ]
  have hscalarSH : SubharmonicOn (homogeneousIndicator v) D := hSH.congr heq
  refine ⟨hscalarSH.cont, hscalarSH, ?_, ?_, ?_, ?_⟩
  · intro K hK hKD
    have heint : (fun R : ℝ => ∫ z in K,
        ‖ScalarAnalytic.potential v R z - homogeneousIndicator v z‖) =
        (fun R : ℝ => ∫ z in K, ‖ScalarAnalytic.potential v R z - H z‖) := by
      funext R
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
      rw [heq (hKD hz)]
    rw [heint]
    exact hL1 K hK hKD
  · intro ζ hζ
    obtain ⟨μ, hroot, _, hHμ, hs⟩ := hclass ζ hζ
    exact ⟨μ, hroot, hs, (heq hζ).trans hHμ⟩
  · exact hscalarSH.cont.comp (by fun_prop) (fun θ hθ => unit_ray_mem_fullCone hθ)
  · intro θ hθ ρ hρ
    have hθD := unit_ray_mem_fullCone hθ
    obtain ⟨_, _, hrate, _, _⟩ := hclass _ hθD
    rw [heq (positive_ray_mem_fullCone hθ hρ)]
    have hhom := PerronVectorLimit.indicator_pos_homogeneous hρ hrate
    change H ((ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) = _ at hhom
    rw [hhom]
    exact congrArg (fun t : ℝ => ρ * t) (heq hθD).symm

#print axioms lemma_3_2
end V10.ScalarIndicatorLimit
