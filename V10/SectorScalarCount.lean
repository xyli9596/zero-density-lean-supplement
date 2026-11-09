import V10.ScalarZeroMeasureSets
import V10.ExteriorSectorCount
import V10.RayMeasureGeometry

/-!
# Scalar ODE to the actual exterior sector count

The proof constructs one larger compact carrier around the dyadic annulus,
uses Lemma 3.2 and actual Poincaré–Lelong there, derives continuity-set mass
convergence, transports each actual zero multiplicity under dilation, and
accumulates the annular law. The remaining input is the independently proved
identification of the indicator's Laplacian with an explicit measure.
-/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal ContDiff
namespace V10.SectorScalarCount
open AnalyticZeroMeasureCompact SectorScaledNeighborhood RayMeasureGeometry
open DomainDivisorCount RadialCutoffGeometry ZeroDensity.SectorDivisorCount

/-- Actual scalar equation to actual open-sided exterior sector count. There
is no smooth-test convergence, count convergence, or compactness premise. -/
theorem sector_scalar_count_of_laplacian_measure
    {n : ℕ} {v : ℂ → ℂ} {b : ℂ → Fin (n + 1) → ℂ}
    {a : Fin (n + 1) → ℂ} {R₀ : ℝ} {J : Set ℝ}
    (hR₀ : 0 < R₀) (hJo : IsOpen J) (hJc : IsPreconnected J)
    (hv : AnalyticOnNhd ℂ v (PerronSector.sector R₀ J))
    (hb : ContinuousOn b (PerronSector.sector R₀ J))
    (hscalar : ∀ z ∈ PerronSector.sector R₀ J, iteratedDeriv (n + 1) v z +
      ∑ j : Fin (n + 1), b z j * iteratedDeriv j.val v z = 0)
    (hnontrivial : ∃ z ∈ PerronSector.sector R₀ J, v z ≠ 0)
    (hlim : ∀ j (K : Set ℝ), K ⊆ J → IsCompact K →
      TendstoUniformlyOn
        (fun t : ℝ => fun θ : ℝ => b ((t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) j)
        (fun _ => a j) atTop K)
    {ν : Measure ℂ} [IsFiniteMeasureOnCompacts ν]
    (hpair : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ fullCone J →
      (∫ z, Laplacian.laplacian φ z * ScalarIndicatorLimit.homogeneousIndicator v z) /
        (2 * Real.pi) = ∫ z, φ z ∂ν)
    {S α β : ℝ} (hS : R₀ < S) (hαβ : Icc α β ⊆ J)
    (hfront : ν (frontier (clippedSector (1 / 2) 1 α β)) = 0) :
    Tendsto (fun R : ℝ => domainPhaseCount v (PerronSector.sector R₀ J) S α β R / R)
      atTop (𝓝 (2 * ν.real (clippedSector (1 / 2) 1 α β))) := by
  let A := clippedSector (1 / 2) 1 α β
  have hAc : IsCompact (closure A) := clippedSector_closure_compact _ _ _ _
  have hAD : closure A ⊆ fullCone J :=
    clippedSector_closure_subset_fullCone (by norm_num : (0 : ℝ) < 1 / 2) hαβ
  have hDo := fullCone_isOpen hJo
  obtain ⟨δ, hδ, hδD⟩ := hAc.exists_cthickening_subset_open hDo hAD
  let K := cthickening δ (closure A)
  have hK : IsCompact K := hAc.cthickening
  have hKD : K ⊆ fullCone J := hδD
  have hAint : closure A ⊆ interior K :=
    (self_subset_thickening hδ _).trans (thickening_subset_interior_cthickening δ _)
  have hAK : A ⊆ K := subset_closure.trans (hAint.trans interior_subset)
  have hmeasure := ScalarZeroMeasureSets.sector_scalar_zero_measure_tendsto_set
    hR₀ hJo hJc hv hb hscalar hnontrivial hlim hK hKD isOpen_interior interior_subset
    (fun φ hφ hφc hs => hpair φ hφ hφc (hs.trans (interior_subset.trans hKD)))
    (clippedSector_isMeasurable (by norm_num : (0 : ℝ) < 1 / 2)) hAc hAint hfront
  have hνA : ν A ≠ (∞ : ℝ≥0∞) :=
    ne_top_of_le_ne_top hAc.measure_ne_top (measure_mono subset_closure)
  have hmass : Tendsto (fun R : ℝ =>
      (normalizedDivisorMeasure (fun z => v ((R : ℂ) * z)) hK R).real A)
      atTop (𝓝 (ν.real A)) := (ENNReal.tendsto_toReal hνA).comp hmeasure
  have hlocal := exists_scaled_neighborhood
    (A := fun z => b z 0) (A₀ := a 0) hR₀ hJo (hlim 0)
  have hmap : ∀ᶠ R : ℝ in atTop, MapsTo (fun z : ℂ => (R : ℂ) * z) K
      (PerronSector.sector R₀ J) := by
    apply ScalarWeakLaplacian.eventually_on_compact_of_locally hK
    intro x hx
    obtain ⟨N, hNo, hxN, _, _, _, M, hm, _, _⟩ := hlocal x (hKD hx)
    exact ⟨N, hNo, hxN, hm⟩
  have hcarrier : ∀ R, polarCarrier S R α β ⊆ PerronSector.sector R₀ J := by
    intro R z hz
    obtain ⟨r, hr, θ, hθ, he⟩ := mem_polarCarrier.mp hz
    exact (PerronSector.mem_sector_iff hR₀).mpr
      ⟨r, hS.trans_le hr.1, θ, hαβ hθ, he⟩
  exact ExteriorSectorCount.domainPhaseCount_tendsto_of_scaled_annulus hK
    (hR₀.trans hS).le hv hcarrier hmap hAK hmass

/-- Explicit weighted-ray version: the limiting coefficient is the sum of
actual ray weights inside the angular window, divided by 2π. -/
theorem sector_scalar_count_of_edge_measure
    {n : ℕ} {v : ℂ → ℂ} {b : ℂ → Fin (n + 1) → ℂ}
    {a : Fin (n + 1) → ℂ} {R₀ : ℝ} {J : Set ℝ}
    (hR₀ : 0 < R₀) (hJo : IsOpen J) (hJc : IsPreconnected J)
    (hv : AnalyticOnNhd ℂ v (PerronSector.sector R₀ J))
    (hb : ContinuousOn b (PerronSector.sector R₀ J))
    (hscalar : ∀ z ∈ PerronSector.sector R₀ J, iteratedDeriv (n + 1) v z +
      ∑ j : Fin (n + 1), b z j * iteratedDeriv j.val v z = 0)
    (hnontrivial : ∃ z ∈ PerronSector.sector R₀ J, v z ≠ 0)
    (hlim : ∀ j (K : Set ℝ), K ⊆ J → IsCompact K →
      TendstoUniformlyOn
        (fun t : ℝ => fun θ : ℝ => b ((t : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) j)
        (fun _ => a j) atTop K)
    (T : Finset ℝ) (w : ℝ → ℝ) (hw : ∀ θ ∈ T, 0 ≤ w θ)
    (hpair : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ fullCone J →
      (∫ z, Laplacian.laplacian φ z * ScalarIndicatorLimit.homogeneousIndicator v z) =
        ∫ z, φ z ∂edgeMeasure T w)
    {S α β : ℝ} (hS : R₀ < S) (hαβ : Icc α β ⊆ J)
    (hα : ∀ θ ∈ T, unitPoint θ = unitPoint α → w θ = 0)
    (hβ : ∀ θ ∈ T, unitPoint θ = unitPoint β → w θ = 0) :
    Tendsto (fun R : ℝ => domainPhaseCount v (PerronSector.sector R₀ J) S α β R / R)
      atTop (𝓝 (sectorWeight T w α β / (2 * Real.pi))) := by
  have hp : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ fullCone J →
      (∫ z, Laplacian.laplacian φ z * ScalarIndicatorLimit.homogeneousIndicator v z) /
        (2 * Real.pi) = ∫ z, φ z ∂normalizedEdgeMeasure T w := by
    intro φ hφ hφc hφD
    rw [hpair φ hφ hφc hφD, normalizedEdgeMeasure, integral_smul_measure,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi)), smul_eq_mul]
    ring
  have ht := sector_scalar_count_of_laplacian_measure
    hR₀ hJo hJc hv hb hscalar hnontrivial hlim hp hS hαβ
    (normalizedEdgeMeasure_frontier_clippedSector (by norm_num : (0 : ℝ) < 1 / 2) T w hα hβ)
  rw [normalizedEdgeMeasure_half_annulus T w α β hw] at ht
  convert ht using 1
  congr 1
  ring

#print axioms sector_scalar_count_of_laplacian_measure
#print axioms sector_scalar_count_of_edge_measure
end V10.SectorScalarCount
