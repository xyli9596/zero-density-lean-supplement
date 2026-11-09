import V10.ScalarLocalRootSelection
import V10.PolygonEdgeNormals
import V10.RayMeasureGeometry
import Mathlib.Tactic

/-! The polygon belonging to the actual scalar ODE solution. Its vertices
are exactly conjugates of characteristic roots selected on nonempty open
angle intervals. The equality of its support function with the actual
homogeneous scalar indicator is derived on the full cone, not assumed as
angular support data. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace V10.ScalarPolygonIndicator
open ScalarLocalRootSelection ScalarIndicatorLimit SectorScaledNeighborhood PerronSector
open ZeroDensity.LocalRootSelection
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable Classical.decEq

def indicatorVertices {n : ℕ} (c : Fin n → ℂ) (v : ℂ → ℂ) (l u : ℝ) : Finset ℂ :=
  (selected (characteristicRoots c) (angularIndicator v) l u).image star

/-- The original selected-root criterion, with the characteristic equation
and the nonempty open interval made explicit. -/
theorem mem_indicatorVertices {n : ℕ} (c : Fin n → ℂ) (v : ℂ → ℂ)
    (l u : ℝ) (ν : ℂ) :
    ν ∈ indicatorVertices c v l u ↔
      ∃ μ : ℂ, star μ = ν ∧
        (μ ^ n + ∑ j : Fin n, c j * μ ^ j.val = 0) ∧
        ∃ a b : ℝ, a < b ∧ Ioo a b ⊆ Ioo l u ∧
          ∀ θ ∈ Ioo a b, angularIndicator v θ =
            (μ * Complex.exp ((θ : ℂ) * Complex.I)).re := by
  simp only [indicatorVertices, Finset.mem_image, selected, Finset.mem_filter,
    mem_characteristicRoots, projection_eq]
  aesop

theorem conjugate_projection_ray (μ : ℂ) (r θ : ℝ) :
    LocalSupportFace.projection (star μ)
      ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
      r * projection μ θ := by
  rw [projection_eq]
  simp [LocalSupportFace.projection, Complex.mul_re, Complex.mul_im,
    Complex.exp_re, Complex.exp_im]
  ring

theorem conjugate_support_ray (s : Finset ℂ) (hs : s.Nonempty)
    {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    LocalSupportFace.support (s.image star) (hs.image star)
      ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) =
      r * s.sup' hs (fun μ => projection μ θ) := by
  unfold LocalSupportFace.support
  apply le_antisymm
  · apply Finset.sup'_le
    intro ν hν
    obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp hν
    rw [conjugate_projection_ray]
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun μ => projection μ θ) hμ) hr
  · obtain ⟨μ, hμ, he⟩ := Finset.exists_mem_eq_sup' hs (fun μ => projection μ θ)
    rw [he]
    have hμstar : star μ ∈ s.image star := Finset.mem_image.mpr ⟨μ, hμ, rfl⟩
    have hm := Finset.le_sup'
      (fun ν => LocalSupportFace.projection ν ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
      hμstar
    rwa [conjugate_projection_ray] at hm

/-- Actual scalar ODE to the actual selected polygon, including the planar
support identity, the exact vertex set, and the scalar L¹ limit rewritten
against that support function. -/
theorem actual_indicator_eq_polygon_support {n : ℕ} {v : ℂ → ℂ}
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
          atTop (𝓝 0)) := by
  obtain ⟨hne, hangular, hvertices⟩ := ScalarLocalRootSelection.lemma_3_3
    hR₀ hJo hJc hv hb hscalar hnontrivial hlim hlu hshort hJsub
  obtain ⟨_, _, hL1, _, _, hhom⟩ := ScalarIndicatorLimit.lemma_3_2
    hR₀ hJo hJc hv hb hscalar hnontrivial hlim
  let hs : (indicatorVertices c v l u).Nonempty := hne.image star
  have heq : EqOn (homogeneousIndicator v)
      (LocalSupportFace.support (indicatorVertices c v l u) hs) (fullCone (Ioo l u)) := by
    rintro z ⟨w, hw, rfl⟩
    have hp : Complex.exp w = (Real.exp w.re : ℂ) *
        Complex.exp ((w.im : ℂ) * Complex.I) := by
      conv_lhs => rw [← Complex.re_add_im w]
      rw [Complex.exp_add, ← Complex.ofReal_exp]
    rw [hp, hhom w.im (hJsub hw) (Real.exp w.re) (Real.exp_pos _), hangular w.im hw]
    exact (conjugate_support_ray _ hne (Real.exp_pos _).le w.im).symm
  refine ⟨hs, heq, hvertices, ?_⟩
  intro K hK hKD
  have hKD₀ : K ⊆ fullCone J₀ := by
    intro z hz
    obtain ⟨w, hw, he⟩ := hKD hz
    exact ⟨w, hJsub hw, he⟩
  have hh := hL1 K hK hKD₀
  convert hh using 1
  funext R
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  rw [heq (hKD hz)]

/-- Vanishing actual polygon face length on the two angular boundaries is
exactly the direction-invariant zero-weight input for the ray measure. -/
theorem polygon_boundary_weights {s : Finset ℂ} (hs : s.Nonempty) {a b : ℝ}
    (ha : PolygonEdgeNormals.weight s a = 0) (hb : PolygonEdgeNormals.weight s b = 0) :
    (∀ θ ∈ PolygonEdgeNormals.normals s hs,
      RayMeasureGeometry.unitPoint θ = RayMeasureGeometry.unitPoint a →
        PolygonEdgeNormals.weight s θ = 0) ∧
    (∀ θ ∈ PolygonEdgeNormals.normals s hs,
      RayMeasureGeometry.unitPoint θ = RayMeasureGeometry.unitPoint b →
        PolygonEdgeNormals.weight s θ = 0) := by
  constructor
  · intro θ _ he
    exact (PolygonEdgeNormals.weight_eq_of_exp_eq s he).trans ha
  · intro θ _ he
    exact (PolygonEdgeNormals.weight_eq_of_exp_eq s he).trans hb

theorem normalized_polygon_boundary_null {s : Finset ℂ} (hs : s.Nonempty)
    {S R a b : ℝ} (hS : 0 < S)
    (ha : PolygonEdgeNormals.weight s a = 0) (hb : PolygonEdgeNormals.weight s b = 0) :
    RayMeasureGeometry.normalizedEdgeMeasure (PolygonEdgeNormals.normals s hs)
      (PolygonEdgeNormals.weight s)
      (frontier (RadialCutoffGeometry.clippedSector S R a b)) = 0 := by
  obtain ⟨ha', hb'⟩ := polygon_boundary_weights hs ha hb
  exact RayMeasureGeometry.normalizedEdgeMeasure_frontier_clippedSector hS _ _ ha' hb'

#print axioms actual_indicator_eq_polygon_support
#print axioms mem_indicatorVertices
#print axioms normalized_polygon_boundary_null
end V10.ScalarPolygonIndicator
