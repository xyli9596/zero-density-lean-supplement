import V10.ScalarPolygonIndicator
import V10.SectorScalarCount
import V10.PolygonSupportLaplacian
import Mathlib.Tactic

/-! Actual scalar ODE to the explicit polygon-edge sector density. All
indicator, L¹, distributional, continuity-set, multiplicity-scaling, and
annular-to-radial inputs are derived. The divisor is evaluated on the
original exterior analytic sector, never on a disk crossing its inner hole. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
namespace V10.ScalarSectorCounting
open ScalarPolygonIndicator ScalarIndicatorLimit ScalarLocalRootSelection
open SectorScaledNeighborhood PerronSector PolygonEdgeNormals
open RayMeasureGeometry DomainDivisorCount
set_option backward.isDefEq.respectTransparency false

theorem sector_mono_angles {R : ℝ} {J J₀ : Set ℝ} (hJ : J ⊆ J₀) :
    sector R J ⊆ sector R J₀ := by
  rintro z ⟨w, hw, rfl⟩
  exact ⟨w, ⟨hw.1, hJ hw.2⟩, rfl⟩

/-- Nontriviality of the actual analytic solution persists on every
nonempty open subsector, by the identity theorem on its original domain. -/
theorem nontrivial_on_subsector {v : ℂ → ℂ} {R₀ l u : ℝ} {J₀ : Set ℝ}
    (hR₀ : 0 < R₀) (hJc : IsPreconnected J₀)
    (hv : AnalyticOnNhd ℂ v (sector R₀ J₀))
    (hn : ∃ z ∈ sector R₀ J₀, v z ≠ 0) (hlu : l < u) (hJ : Ioo l u ⊆ J₀) :
    ∃ z ∈ sector R₀ (Ioo l u), v z ≠ 0 := by
  by_contra! hzero
  let z := ((R₀ + 1 : ℝ) : ℂ) * Complex.exp ((((l + u) / 2 : ℝ) : ℂ) * Complex.I)
  have hz : z ∈ sector R₀ (Ioo l u) := by
    apply (mem_sector_iff hR₀).mpr
    exact ⟨R₀ + 1, by linarith, (l + u) / 2, ⟨by linarith, by linarith⟩, rfl⟩
  have hg : v =ᶠ[𝓝 z] 0 := by
    filter_upwards [(sector_isOpen R₀ isOpen_Ioo).mem_nhds hz] with w hw
    exact hzero w hw
  obtain ⟨w, hw, hne⟩ := hn
  exact hne ((hv.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (sector_isPreconnected R₀ hJc) (sector_mono_angles hJ hz) hg) hw)

/-- Proposition 3.1: the actual selected-root support limit and the actual
open-sided exterior-sector count, with the Euclidean polygon edge weights.
The finite ray sum uses direction membership, so angular windows crossing
the principal-argument cut are covered without a branch convention. -/
theorem proposition_3_1 {n : ℕ} {v : ℂ → ℂ}
    {b : ℂ → Fin (n + 1) → ℂ} {c : Fin (n + 1) → ℂ} {R₀ : ℝ} {J₀ : Set ℝ}
    (hR₀ : 0 < R₀) (hJo : IsOpen J₀) (hJc : IsPreconnected J₀)
    (hv : AnalyticOnNhd ℂ v (sector R₀ J₀))
    (hb : ContinuousOn b (sector R₀ J₀))
    (hscalar : ∀ z ∈ sector R₀ J₀, iteratedDeriv (n + 1) v z +
      ∑ j : Fin (n + 1), b z j * iteratedDeriv j.val v z = 0)
    (hnontrivial : ∃ z ∈ sector R₀ J₀, v z ≠ 0)
    (hlim : ∀ j (K : Set ℝ), K ⊆ J₀ → IsCompact K →
      TendstoUniformlyOn
        (fun r : ℝ => fun θ : ℝ => b ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) j)
        (fun _ => c j) atTop K)
    {l u : ℝ} (hlu : l < u) (hshort : u - l < Real.pi) (hJsub : Ioo l u ⊆ J₀) :
    ∃ hs : (indicatorVertices c v l u).Nonempty,
      EqOn (homogeneousIndicator v)
        (LocalSupportFace.support (indicatorVertices c v l u) hs) (fullCone (Ioo l u)) ∧
      (convexHull ℝ (indicatorVertices c v l u : Set ℂ)).extremePoints ℝ =
        (indicatorVertices c v l u : Set ℂ) ∧
      (∀ K : Set ℂ, IsCompact K → K ⊆ fullCone (Ioo l u) →
        Tendsto (fun R : ℝ => ∫ z in K,
          ‖ScalarAnalytic.potential v R z -
            LocalSupportFace.support (indicatorVertices c v l u) hs z‖)
          atTop (𝓝 0)) ∧
      ∀ S α β : ℝ, R₀ < S → α < β → Icc α β ⊆ Ioo l u →
        weight (indicatorVertices c v l u) α = 0 →
        weight (indicatorVertices c v l u) β = 0 →
        Tendsto (fun R : ℝ => domainPhaseCount v (sector R₀ J₀) S α β R / R)
          atTop (𝓝 (sectorWeight (normals (indicatorVertices c v l u) hs)
            (weight (indicatorVertices c v l u)) α β / (2 * Real.pi))) := by
  obtain ⟨hs, heq, hvertices, hL1⟩ := actual_indicator_eq_polygon_support
    hR₀ hJo hJc hv hb hscalar hnontrivial hlim hlu hshort hJsub
  refine ⟨hs, heq, hvertices, hL1, ?_⟩
  intro S α β hS _ hαβ hα hβ
  have hsub := sector_mono_angles (R := R₀) hJsub
  have hvs := hv.mono hsub
  have hbs := hb.mono hsub
  have hns := nontrivial_on_subsector hR₀ hJc hv hnontrivial hlu hJsub
  have hss : ∀ z ∈ sector R₀ (Ioo l u), iteratedDeriv (n + 1) v z +
      ∑ j : Fin (n + 1), b z j * iteratedDeriv j.val v z = 0 :=
    fun z hz => hscalar z (hsub hz)
  have hls : ∀ j (K : Set ℝ), K ⊆ Ioo l u → IsCompact K →
      TendstoUniformlyOn
        (fun r : ℝ => fun θ : ℝ => b ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) j)
        (fun _ => c j) atTop K := fun j K hK hKc => hlim j K (hK.trans hJsub) hKc
  have hp : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ fullCone (Ioo l u) →
      (∫ z, Laplacian.laplacian φ z * homogeneousIndicator v z) =
        ∫ z, φ z ∂edgeMeasure (normals (indicatorVertices c v l u) hs)
          (weight (indicatorVertices c v l u)) := by
    intro φ hφ hφc hφD
    have hφ0 : (0 : ℂ) ∉ tsupport φ := fun hz => fullCone_ne_zero (hφD hz) rfl
    calc
      _ = ∫ z, Laplacian.laplacian φ z *
          LocalSupportFace.support (indicatorVertices c v l u) hs z := by
        apply integral_congr_ae
        apply ae_of_all
        intro z
        dsimp only
        by_cases hz : z ∈ tsupport φ
        · rw [heq (hφD hz)]
        · simp [LogLaplacianLocal.laplacian_eq_zero_of_notMem_tsupport hz]
      _ = _ := PolygonSupportLaplacian.polygon_support_laplacian _ hs hφ hφc hφ0
  obtain ⟨ha', hb'⟩ := polygon_boundary_weights hs hα hβ
  have ht := SectorScalarCount.sector_scalar_count_of_edge_measure hR₀ isOpen_Ioo
    isPreconnected_Ioo hvs hbs hss hns hls (normals (indicatorVertices c v l u) hs)
    (weight (indicatorVertices c v l u)) (fun θ _ => weight_nonneg _ θ)
    hp hS hαβ ha' hb'
  have hc : ∀ R, ZeroDensity.SectorDivisorCount.polarCarrier S R α β ⊆
      sector R₀ (Ioo l u) := by
    intro R z hz
    obtain ⟨r, hr, θ, hθ, he⟩ := ZeroDensity.SectorDivisorCount.mem_polarCarrier.mp hz
    exact (mem_sector_iff hR₀).mpr ⟨r, hS.trans_le hr.1, θ, hαβ hθ, he⟩
  apply ht.congr
  intro R
  rw [domainPhaseCount_eq_phaseCount hvs (hc R),
    domainPhaseCount_eq_phaseCount hv ((hc R).trans hsub)]

#print axioms nontrivial_on_subsector
#print axioms proposition_3_1

/-- The paper's literal `linear main term + o(R)` formulation, from the
same original scalar ODE data. `sectorWeight` sums the actual geometric
normal rays inside the window, so it also covers intervals crossing the
principal-argument cut. -/
theorem proposition_3_1_littleO {n : ℕ} {v : ℂ → ℂ}
    {b : ℂ → Fin (n + 1) → ℂ} {c : Fin (n + 1) → ℂ} {R₀ : ℝ} {J₀ : Set ℝ}
    (hR₀ : 0 < R₀) (hJo : IsOpen J₀) (hJc : IsPreconnected J₀)
    (hv : AnalyticOnNhd ℂ v (sector R₀ J₀))
    (hb : ContinuousOn b (sector R₀ J₀))
    (hscalar : ∀ z ∈ sector R₀ J₀, iteratedDeriv (n + 1) v z +
      ∑ j : Fin (n + 1), b z j * iteratedDeriv j.val v z = 0)
    (hnontrivial : ∃ z ∈ sector R₀ J₀, v z ≠ 0)
    (hlim : ∀ j (K : Set ℝ), K ⊆ J₀ → IsCompact K →
      TendstoUniformlyOn
        (fun r : ℝ => fun θ : ℝ => b ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) j)
        (fun _ => c j) atTop K)
    {l u : ℝ} (hlu : l < u) (hshort : u - l < Real.pi) (hJsub : Ioo l u ⊆ J₀) :
    ∃ hs : (indicatorVertices c v l u).Nonempty,
      EqOn (homogeneousIndicator v)
        (LocalSupportFace.support (indicatorVertices c v l u) hs) (fullCone (Ioo l u)) ∧
      (∀ K : Set ℂ, IsCompact K → K ⊆ fullCone (Ioo l u) →
        Tendsto (fun R : ℝ => ∫ z in K,
          ‖ScalarAnalytic.potential v R z -
            LocalSupportFace.support (indicatorVertices c v l u) hs z‖)
          atTop (𝓝 0)) ∧
      ∀ S α β : ℝ, R₀ < S → α < β → Icc α β ⊆ Ioo l u →
        weight (indicatorVertices c v l u) α = 0 →
        weight (indicatorVertices c v l u) β = 0 →
        (fun R : ℝ => domainPhaseCount v (sector R₀ J₀) S α β R -
          (sectorWeight (normals (indicatorVertices c v l u) hs)
            (weight (indicatorVertices c v l u)) α β / (2 * Real.pi)) * R)
          =o[atTop] (fun R : ℝ => R) := by
  obtain ⟨hs, heq, _, hL1, hcount⟩ := proposition_3_1
    hR₀ hJo hJc hv hb hscalar hnontrivial hlim hlu hshort hJsub
  refine ⟨hs, heq, hL1, ?_⟩
  intro S α β hS hαβ hsub hα hβ
  exact (RadialTransfer.count_law_iff_littleO tendsto_id).mp
    (hcount S α β hS hαβ hsub hα hβ)

#print axioms proposition_3_1_littleO
end V10.ScalarSectorCounting
