import ZeroDensity.PolygonFaces
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The vertex assertion in v10 Lemma 3.3

Once the selected-root support inequalities have been established, every
locally selected root is exposed on a collision-free direction. Thus the
conjugate selected roots are exactly the extreme points of their convex
hull. This closes the geometric last assertion; the ODE/subharmonic
argument establishing the support inequalities is not assumed proved.
-/

noncomputable section
open Set
namespace V10.SelectedVertices
open ZeroDensity.LocalRootSelection ZeroDensity.PolygonFaces

theorem extreme_of_strict_linear_max (s : Finset ℂ) {x : ℂ}
    (hx : x ∈ s) (L : ℂ →ₗ[ℝ] ℝ)
    (hL : ∀ y ∈ s, y ≠ x → L y < L x) :
    x ∈ (convexHull ℝ (s : Set ℂ)).extremePoints ℝ := by
  classical
  let hs : s.Nonempty := ⟨x, hx⟩
  have he : s.sup' hs L = L x := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro y hy
      by_cases hyx : y = x
      · simp [hyx]
      · exact (hL y hy hyx).le
    · exact Finset.le_sup' L hx
  have hmax : maximizingPoints s hs L = {x} := by
    ext y
    simp only [maximizingPoints, Finset.mem_filter, Finset.mem_singleton, he]
    constructor
    · rintro ⟨hy, heq⟩
      by_contra hne
      exact (hL y hy hne).ne heq
    · rintro rfl
      exact ⟨hx, rfl⟩
  have hface : linearFace s L = {x} := by
    rw [linearFace_eq_convexHull s hs L, hmax]
    simp
  have hex : IsExposed ℝ (convexHull ℝ (s : Set ℂ)) (linearFace s L) := by
    intro _
    exact ⟨L.toContinuousLinearMap, rfl⟩
  rw [hface] at hex
  exact hex.isExtreme.mem_extremePoints

/-- Local agreement on an interval contains a direction with no distinct
    root projection collision. Hence a selected root is a strict maximizer
    if every selected projection lies below the indicator. -/
theorem selected_has_strict_direction (roots : Finset ℂ) (h : ℝ → ℝ) (l u : ℝ)
    (hminor : ∀ ν ∈ selected roots h l u, ∀ θ ∈ Ioo l u,
      projection ν θ ≤ h θ) {μ : ℂ} (hμ : μ ∈ selected roots h l u) :
    ∃ θ ∈ Ioo l u, ∀ ν ∈ selected roots h l u, ν ≠ μ →
      projection ν θ < projection μ θ := by
  classical
  obtain ⟨hμroot, a, b, hab, hsub, heq⟩ := Finset.mem_filter.mp hμ
  have hfinite : (CRGIndicatorPartition.collisionDirections roots 1 l u).Finite :=
    CRGIndicatorPartition.collisionDirections_finite roots (by norm_num)
  obtain ⟨θ, hθ, hnot⟩ := ((Ioo_infinite hab).sdiff hfinite).nonempty
  refine ⟨θ, hsub hθ, ?_⟩
  intro ν hν hne
  apply lt_of_le_of_ne
  · rw [← heq θ hθ]
    exact hminor ν hν θ (hsub hθ)
  · intro htie
    exact hnot ⟨⟨(hsub hθ).1.le, (hsub hθ).2.le⟩,
      ν, selected_subset roots h l u hν, μ, hμroot, hne, htie⟩

theorem conjugate_selected_are_exact_vertices
    (roots : Finset ℂ) (h : ℝ → ℝ) (l u : ℝ)
    (hminor : ∀ ν ∈ selected roots h l u, ∀ θ ∈ Ioo l u,
      projection ν θ ≤ h θ) :
    (convexHull ℝ (((selected roots h l u).image star : Finset ℂ) : Set ℂ)).extremePoints ℝ =
      (((selected roots h l u).image star : Finset ℂ) : Set ℂ) := by
  classical
  apply Set.Subset.antisymm (extremePoints_convexHull_subset (𝕜 := ℝ))
  intro x hx
  obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨θ, _, hstrict⟩ := selected_has_strict_direction roots h l u hminor hμ
  apply extreme_of_strict_linear_max _ (Finset.mem_image.mpr ⟨μ, hμ, rfl⟩)
    (normalLinear θ)
  intro y hy hne
  obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hy
  simp only [normal_eq_projection, star_star]
  exact hstrict ν hν (fun h => hne (congrArg star h))

end V10.SelectedVertices
