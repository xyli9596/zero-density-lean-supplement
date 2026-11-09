import ZeroDensity.MainTheorem
import ZeroDensity.SupportingGeometry
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.Convex

/-! Actual supporting faces of finite polygons. The face is proved to be the
convex hull of exactly the maximizing points, including collinear points.
This is geometric; no zero-measure convergence is assumed or established here.
-/
noncomputable section
set_option autoImplicit false
open Set Metric
open scoped BigOperators
namespace ZeroDensity.PolygonFaces

def linearFace (s : Finset ℂ) (L : ℂ →ₗ[ℝ] ℝ) : Set ℂ :=
  {x | x ∈ convexHull ℝ (s : Set ℂ) ∧
    ∀ y ∈ convexHull ℝ (s : Set ℂ), L y ≤ L x}

def maximizingPoints (s : Finset ℂ) (hs : s.Nonempty)
    (L : ℂ →ₗ[ℝ] ℝ) : Finset ℂ :=
  s.filter fun x => L x = s.sup' hs L

theorem linear_le_height (s : Finset ℂ) (hs : s.Nonempty)
    (L : ℂ →ₗ[ℝ] ℝ) {x : ℂ} (hx : x ∈ convexHull ℝ (s : Set ℂ)) :
    L x ≤ s.sup' hs L := by
  obtain ⟨w, hw, hsum, rfl⟩ := Finset.mem_convexHull'.mp hx
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  calc
    ∑ y ∈ s, w y * L y ≤ ∑ y ∈ s, w y * s.sup' hs L :=
      Finset.sum_le_sum fun y hy => mul_le_mul_of_nonneg_left
        (Finset.le_sup' L hy) (hw y hy)
    _ = s.sup' hs L := by rw [← Finset.sum_mul, hsum, one_mul]

theorem mem_linearFace_iff (s : Finset ℂ) (hs : s.Nonempty)
    (L : ℂ →ₗ[ℝ] ℝ) (x : ℂ) :
    x ∈ linearFace s L ↔
      x ∈ convexHull ℝ (s : Set ℂ) ∧ L x = s.sup' hs L := by
  obtain ⟨y, hy, hheight⟩ := Finset.exists_mem_eq_sup' hs L
  constructor
  · rintro ⟨hx, hmax⟩
    exact ⟨hx, le_antisymm (linear_le_height s hs L hx)
      (hheight ▸ hmax y (subset_convexHull ℝ _ hy))⟩
  · rintro ⟨hx, he⟩
    refine ⟨hx, fun y hy => ?_⟩
    rw [he]
    exact linear_le_height s hs L hy

theorem maximizingPoints_nonempty (s : Finset ℂ) (hs : s.Nonempty)
    (L : ℂ →ₗ[ℝ] ℝ) : (maximizingPoints s hs L).Nonempty := by
  obtain ⟨x, hx, he⟩ := Finset.exists_mem_eq_sup' hs L
  exact ⟨x, Finset.mem_filter.mpr ⟨hx, he.symm⟩⟩

/-- The exact finite-hull face formula. Nonmaximizing points receive zero
weight in every convex representation of a supporting point. -/
theorem linearFace_eq_convexHull (s : Finset ℂ) (hs : s.Nonempty)
    (L : ℂ →ₗ[ℝ] ℝ) :
    linearFace s L = convexHull ℝ (maximizingPoints s hs L : Set ℂ) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨hx, hheight⟩ := (mem_linearFace_iff s hs L x).mp hx
    obtain ⟨w, hw, hsum, hrepr⟩ := Finset.mem_convexHull'.mp hx
    have hL : ∑ y ∈ s, w y * L y = L x := by
      rw [← hrepr, map_sum]
      simp only [map_smul, smul_eq_mul]
    have hzero : ∑ y ∈ s, w y * (s.sup' hs L - L y) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum,
        one_mul, hL, hheight, sub_self]
    have hterm : ∀ y ∈ s, w y * (s.sup' hs L - L y) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun y hy =>
        mul_nonneg (hw y hy) (sub_nonneg.mpr (Finset.le_sup' L hy))).mp hzero
    have hwzero : ∀ y ∈ s, y ∉ maximizingPoints s hs L → w y = 0 := by
      intro y hy hnot
      have hne : s.sup' hs L - L y ≠ 0 := by
        intro he
        apply hnot
        exact Finset.mem_filter.mpr ⟨hy, (sub_eq_zero.mp he).symm⟩
      exact (mul_eq_zero.mp (hterm y hy)).resolve_right hne
    apply Finset.mem_convexHull'.mpr
    refine ⟨w, fun y hy => hw y (Finset.mem_filter.mp hy).1, ?_, ?_⟩
    · calc
        ∑ y ∈ maximizingPoints s hs L, w y = ∑ y ∈ s, w y :=
          Finset.sum_subset (Finset.filter_subset _ _) (fun y hy hn => hwzero y hy hn)
        _ = 1 := hsum
    · calc
        ∑ y ∈ maximizingPoints s hs L, w y • y = ∑ y ∈ s, w y • y :=
          Finset.sum_subset (Finset.filter_subset _ _) (fun y hy hn => by rw [hwzero y hy hn, zero_smul])
        _ = x := hrepr
  · intro hx
    have hinc : convexHull ℝ (maximizingPoints s hs L : Set ℂ) ⊆
        convexHull ℝ (s : Set ℂ) := convexHull_mono (Finset.filter_subset _ _)
    apply (mem_linearFace_iff s hs L x).mpr
    refine ⟨hinc hx, ?_⟩
    obtain ⟨w, hw, hsum, rfl⟩ := Finset.mem_convexHull'.mp hx
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    calc
      ∑ y ∈ maximizingPoints s hs L, w y * L y =
          ∑ y ∈ maximizingPoints s hs L, w y * s.sup' hs L := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [(Finset.mem_filter.mp hy).2]
      _ = s.sup' hs L := by rw [← Finset.sum_mul, hsum, one_mul]

theorem linearFace_diameter (s : Finset ℂ) (hs : s.Nonempty)
    (L : ℂ →ₗ[ℝ] ℝ) :
    diam (linearFace s L) = diam (maximizingPoints s hs L : Set ℂ) := by
  rw [linearFace_eq_convexHull, convexHull_diam]

def normalLinear (θ : ℝ) : ℂ →ₗ[ℝ] ℝ :=
  Real.cos θ • Complex.reLm + Real.sin θ • Complex.imLm

theorem normalLinear_eq (θ : ℝ) (z : ℂ) :
    normalLinear θ z = (z * Complex.exp (-((θ : ℂ) * Complex.I))).re := by
  simp [normalLinear, Complex.mul_re, Complex.exp_re, Complex.exp_im]
  ring

/-- This equality uses the precise face definition in the main theorem. -/
theorem actualFace_eq (s : Finset ℂ) (θ : ℝ) :
    MainTheorem.supportingFace (convexHull ℝ (s : Set ℂ)) θ =
      linearFace s (normalLinear θ) := by
  ext x
  simp only [MainTheorem.supportingFace, linearFace, Set.mem_ofPred_eq, normalLinear_eq]

theorem actualFace_diameter (s : Finset ℂ) (hs : s.Nonempty) (θ : ℝ) :
    MainTheorem.faceLength (convexHull ℝ (s : Set ℂ)) θ =
      diam (maximizingPoints s hs (normalLinear θ) : Set ℂ) := by
  rw [MainTheorem.faceLength, actualFace_eq, linearFace_diameter]

def angularTangent (θ : ℝ) (z : ℂ) : ℝ :=
  SupportingGeometry.tangent (star z) θ

theorem normal_eq_projection (θ : ℝ) (z : ℂ) :
    normalLinear θ z = LocalRootSelection.projection (star z) θ := by
  rw [normalLinear_eq]
  simpa only [star_star] using SupportingGeometry.normal_projection (star z) θ

theorem normal_hasDeriv (z : ℂ) (θ : ℝ) :
    HasDerivAt (fun η => normalLinear η z) (angularTangent θ z) θ := by
  convert SupportingGeometry.projection_hasDeriv (star z) θ using 1
  · funext η
    exact normal_eq_projection η z
  · rfl

theorem distance_on_normal_line (θ : ℝ) (x y : ℂ)
    (he : normalLinear θ x = normalLinear θ y) :
    dist x y = |angularTangent θ y - angularTangent θ x| := by
  have hproj : LocalRootSelection.projection (star x) θ =
      LocalRootSelection.projection (star y) θ := by
    rw [← normal_eq_projection, ← normal_eq_projection]
    exact he
  have hd := SupportingGeometry.tangent_difference_length (star x) (star y) θ hproj
  simpa only [angularTangent, ← star_sub, norm_star, dist_eq_norm, norm_sub_rev] using hd.symm

/-- The length is the full tangential range of the actual maximizing face,
not the distance between an arbitrary pair of collinear defining points. -/
theorem actualFace_length_range (s : Finset ℂ) (hs : s.Nonempty) (θ : ℝ) :
    MainTheorem.faceLength (convexHull ℝ (s : Set ℂ)) θ =
      (maximizingPoints s hs (normalLinear θ)).sup'
        (maximizingPoints_nonempty s hs (normalLinear θ)) (angularTangent θ) -
      (maximizingPoints s hs (normalLinear θ)).inf'
        (maximizingPoints_nonempty s hs (normalLinear θ)) (angularTangent θ) := by
  classical
  rw [actualFace_diameter s hs θ]
  let F := maximizingPoints s hs (normalLinear θ)
  have hF : F.Nonempty := maximizingPoints_nonempty s hs (normalLinear θ)
  obtain ⟨p, hp, hmax⟩ := Finset.exists_mem_eq_sup' hF (angularTangent θ)
  obtain ⟨q, hq, hmin⟩ := Finset.exists_mem_eq_inf' hF (angularTangent θ)
  have hpos : 0 ≤ F.sup' hF (angularTangent θ) - F.inf' hF (angularTangent θ) := by
    exact sub_nonneg.mpr ((Finset.inf'_le _ hp).trans (Finset.le_sup' _ hp))
  have he : ∀ x ∈ F, ∀ y ∈ F, normalLinear θ x = normalLinear θ y := by
    intro x hx y hy
    exact (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
  apply le_antisymm
  · apply Metric.diam_le_of_forall_dist_le hpos
    intro x hx y hy
    rw [distance_on_normal_line θ x y (he x hx y hy), abs_le]
    have hxlo := Finset.inf'_le (s := F) (angularTangent θ) hx
    have hxhi := Finset.le_sup' (s := F) (angularTangent θ) hx
    have hylo := Finset.inf'_le (s := F) (angularTangent θ) hy
    have hyhi := Finset.le_sup' (s := F) (angularTangent θ) hy
    constructor <;> linarith
  · have hd := Metric.dist_le_diam_of_mem F.finite_toSet.isBounded hq hp
    rw [distance_on_normal_line θ q p (he q hq p hp), ← hmax, ← hmin,
      abs_of_nonneg hpos] at hd
    exact hd

theorem positive_face_collision (s : Finset ℂ) (hs : s.Nonempty) (θ : ℝ)
    (hpos : 0 < MainTheorem.faceLength (convexHull ℝ (s : Set ℂ)) θ) :
    ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ normalLinear θ x = normalLinear θ y := by
  rw [actualFace_length_range s hs θ] at hpos
  let F := maximizingPoints s hs (normalLinear θ)
  have hF : F.Nonempty := maximizingPoints_nonempty s hs (normalLinear θ)
  obtain ⟨p, hp, hmax⟩ := Finset.exists_mem_eq_sup' hF (angularTangent θ)
  obtain ⟨q, hq, hmin⟩ := Finset.exists_mem_eq_inf' hF (angularTangent θ)
  refine ⟨p, (Finset.mem_filter.mp hp).1, q, (Finset.mem_filter.mp hq).1, ?_,
    (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm⟩
  intro he
  rw [hmax, hmin, he, sub_self] at hpos
  exact lt_irrefl _ hpos

/-- Finiteness of the actual positive face lengths follows from the root
collision geometry, without supplying a finite-support assumption. -/
theorem positive_faces_finite (s : Finset ℂ) (hs : s.Nonempty) (l u : ℝ) :
    {θ | θ ∈ Ioo l u ∧
      0 < MainTheorem.faceLength (convexHull ℝ (s : Set ℂ)) θ}.Finite := by
  classical
  apply (CRGIndicatorPartition.collisionDirections_finite (s.image star) (a := l)
    (b := u) (by norm_num : (0 : ℝ) < 1)).subset
  intro θ hθ
  obtain ⟨x, hx, y, hy, hxy, he⟩ := positive_face_collision s hs θ hθ.2
  refine ⟨⟨hθ.1.1.le, hθ.1.2.le⟩, star x, Finset.mem_image.mpr ⟨x,hx,rfl⟩,
    star y, Finset.mem_image.mpr ⟨y,hy,rfl⟩, ?_, ?_⟩
  · exact fun hh => hxy (star_injective hh)
  · change LocalRootSelection.projection (star x) θ = LocalRootSelection.projection (star y) θ
    rw [← normal_eq_projection, ← normal_eq_projection]
    exact he

#print axioms linearFace_eq_convexHull
#print axioms actualFace_diameter
#print axioms actualFace_length_range
#print axioms positive_faces_finite
end ZeroDensity.PolygonFaces
