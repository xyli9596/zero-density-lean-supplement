import V10.PolygonRayLocalization
import V10.RotatedHingeLaplacian
import V10.SmoothTestLocalization

/-! The actual distributional Laplacian of a finite polygon support function,
away from the origin, is its Euclidean edge-length measure on normal rays.
All local hinge and test-partition identities are derived internally. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace V10.PolygonSupportLaplacian
open ZeroDensity PolygonFaces LocalSupportFace PolygonEdgeNormals
open PolygonRayLocalization RayMeasureGeometry LogLaplacianLocal

theorem pairing_add {H f g : ℂ → ℝ} (hH : Continuous H)
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    (∫ z, Laplacian.laplacian (f + g) z * H z) =
      (∫ z, Laplacian.laplacian f z * H z) +
        (∫ z, Laplacian.laplacian g z * H z) := by
  have hd : ∀ z, Laplacian.laplacian (f + g) z =
      Laplacian.laplacian f z + Laplacian.laplacian g z := by
    intro z
    have hf2 : ContDiff ℝ 2 f := hf.of_le (by decide)
    have hg2 : ContDiff ℝ 2 g := hg.of_le (by decide)
    exact hf2.contDiffAt.laplacian_add hg2.contDiffAt
  simp_rw [hd, add_mul]
  exact integral_add
    (((continuous_laplacian hf hfc).mul hH).integrable_of_hasCompactSupport
      (hasCompactSupport_laplacian hfc).mul_right)
    (((continuous_laplacian hg hgc).mul hH).integrable_of_hasCompactSupport
      (hasCompactSupport_laplacian hgc).mul_right)

/-- The genuine weak Laplacian formula with actual supporting-face lengths.
Tests are allowed to cross any number of normal rays and to have disconnected
compact support. Only the origin is excluded from their support. -/
theorem polygon_support_laplacian (s : Finset ℂ) (hs : s.Nonempty)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφ0 : (0 : ℂ) ∉ tsupport φ) :
    (∫ z, Laplacian.laplacian φ z * LocalSupportFace.support s hs z) =
      ∫ z, φ z ∂polygonMeasure s hs := by
  let P : (ℂ → ℝ) → Prop := fun ψ =>
    (∫ z, Laplacian.laplacian ψ z * LocalSupportFace.support s hs z) =
      ∫ z, ψ z ∂polygonMeasure s hs
  change P φ
  refine SmoothTestLocalization.of_local (P := P) ?_ ?_ hφ hφc ?_
  · change (∫ z, Laplacian.laplacian (fun _ : ℂ => (0 : ℝ)) z *
      LocalSupportFace.support s hs z) = ∫ z, (0 : ℝ) ∂polygonMeasure s hs
    simp
  · intro f g hf hfc hg hgc hPf hPg
    dsimp [P] at *
    rw [pairing_add (support_continuous s hs) hf hfc hg hgc, hPf, hPg]
    exact (integral_add (hf.continuous.integrable_of_hasCompactSupport hfc)
      (hg.continuous.integrable_of_hasCompactSupport hgc)).symm
  · intro x hx
    have hx0 : x ≠ 0 := fun he => hφ0 (he ▸ hx)
    obtain ⟨p, _, hh⟩ := support_local_hinge s hs hx0
    obtain ⟨W, hW, hWo, hxW⟩ := mem_nhds_iff.mp hh
    obtain ⟨V, hVo, hxV, hVpair⟩ := exists_local_pairing s hs hx0
    have hc : Continuous (fun z : ℂ => normalLinear x.arg z) := by
      change Continuous (fun z : ℂ => Real.cos x.arg * z.re + Real.sin x.arg * z.im)
      fun_prop
    have hxpos : 0 < normalLinear x.arg x := by
      have he := normal_ray_self ‖x‖ x.arg
      rw [Complex.norm_mul_exp_arg_mul_I] at he
      rw [he]
      exact norm_pos_iff.mpr hx0
    refine ⟨W ∩ V ∩ {z : ℂ | 0 < normalLinear x.arg z},
      (hWo.inter hVo).inter (isOpen_lt continuous_const hc), ⟨⟨hxW, hxV⟩, hxpos⟩, ?_⟩
    intro ψ hψ hψc hψsub
    have hhalf : tsupport ψ ⊆ {z : ℂ | 0 < normalLinear x.arg z} :=
      hψsub.trans inter_subset_right
    have hμ := hVpair ψ hψ.continuous hψc
      (hψsub.trans (inter_subset_left.trans inter_subset_right))
    rw [← integral_rayLengthMeasure hψ.continuous] at hμ
    dsimp [P]
    rw [hμ]
    calc
      _ = ∫ z, Laplacian.laplacian ψ z *
          (LocalSupportFace.projection p z + weight s x.arg *
            max 0 (angularTangent x.arg z)) := by
        apply integral_congr_ae
        apply ae_of_all
        intro z
        dsimp only
        by_cases hz : z ∈ tsupport ψ
        · rw [hW (hψsub hz).1.1]
        · simp [laplacian_eq_zero_of_notMem_tsupport hz]
      _ = _ := RotatedHingeLaplacian.linear_add_hinge_laplacian_ray p
        (weight s x.arg) x.arg hψ hψc hhalf

/-- The explicit finite sum version used in the manuscript. -/
theorem polygon_support_laplacian_sum (s : Finset ℂ) (hs : s.Nonempty)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφ0 : (0 : ℂ) ∉ tsupport φ) :
    (∫ z, Laplacian.laplacian φ z * LocalSupportFace.support s hs z) =
      ∑ θ ∈ normals s hs, weight s θ *
        ∫ r in Ioi (0 : ℝ), φ (RadialCutoffGeometry.rayPoint r θ) := by
  rw [polygon_support_laplacian s hs hφ hφc hφ0]
  exact integral_edgeMeasure hφ.continuous hφc _ _ (fun θ _ => weight_nonneg s θ)

#print axioms polygon_support_laplacian
#print axioms polygon_support_laplacian_sum
end V10.PolygonSupportLaplacian
