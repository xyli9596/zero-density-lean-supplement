import V10.PolygonEdgeNormals
import V10.RayMeasureGeometry

/-! Local isolation of actual edge rays. At a nonzero point, the finite
polygon edge measure agrees locally with the single ray having that argument,
with zero coefficient when the supporting face is a singleton. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology
namespace V10.PolygonRayLocalization
open ZeroDensity ZeroDensity.SectorDivisorCount RayMeasureGeometry PolygonEdgeNormals
open RadialCutoffGeometry

def polygonMeasure (s : Finset ℂ) (hs : s.Nonempty) : Measure ℂ :=
  edgeMeasure (normals s hs) (weight s)

instance polygonMeasure_finiteOnCompacts (s : Finset ℂ) (hs : s.Nonempty) :
    IsFiniteMeasureOnCompacts (polygonMeasure s hs) :=
  inferInstanceAs (IsFiniteMeasureOnCompacts (edgeMeasure (normals s hs) (weight s)))

theorem mem_raySupport_iff_arg {z : ℂ} (hz : z ≠ 0) {θ : ℝ}
    (hθ : θ ∈ Ioc (-Real.pi) Real.pi) :
    z ∈ raySupport θ ↔ z.arg = θ := by
  constructor
  · intro he
    change z = (‖z‖ : ℂ) * unitPoint θ at he
    have ha := congrArg Complex.arg he
    rw [Complex.arg_real_mul _ (norm_pos_iff.mpr hz)] at ha
    exact ha.trans (arg_unitPoint hθ)
  · intro he
    change z = (‖z‖ : ℂ) * unitPoint θ
    rw [← he]
    exact (Complex.norm_mul_exp_arg_mul_I z).symm

theorem integral_ray_eq_zero_of_disjoint {φ : ℂ → ℝ} (_hφ : Continuous φ)
    {θ : ℝ} (hs : Disjoint (tsupport φ) (raySupport θ)) :
    (∫ r in Ioi (0 : ℝ), φ (rayPoint r θ)) = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  apply image_eq_zero_of_notMem_tsupport
  intro hp
  exact Set.disjoint_left.mp hs hp ((rayPoint_mem_raySupport hr).mpr rfl)

/-- The local weak action of the explicit positive edge measure. -/
theorem exists_local_pairing (s : Finset ℂ) (hs : s.Nonempty)
    {z₀ : ℂ} (hz₀ : z₀ ≠ 0) :
    ∃ V : Set ℂ, IsOpen V ∧ z₀ ∈ V ∧
      ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ V →
        (∫ z, φ z ∂polygonMeasure s hs) =
          weight s z₀.arg * ∫ r in Ioi (0 : ℝ), φ (rayPoint r z₀.arg) := by
  classical
  let T := normals s hs
  let V : Set ℂ := (⋃ θ ∈ T.erase z₀.arg, raySupport θ)ᶜ
  have hVo : IsOpen V :=
    (isClosed_biUnion_finset fun θ (_ : θ ∈ T.erase z₀.arg) => raySupport_isClosed θ).isOpen_compl
  have hzV : z₀ ∈ V := by
    intro hzbad
    obtain ⟨θ, hθT, hzθ⟩ := mem_iUnion₂.mp hzbad
    have hθe := Finset.mem_erase.mp hθT
    have hθcan := (mem_normals.mp hθe.2).1
    exact hθe.1 ((mem_raySupport_iff_arg hz₀ hθcan).mp hzθ).symm
  refine ⟨V, hVo, hzV, ?_⟩
  intro φ hφ hφc hφV
  have hzero (θ : ℝ) (hθ : θ ∈ T) (hne : θ ≠ z₀.arg) :
      (∫ r in Ioi (0 : ℝ), φ (rayPoint r θ)) = 0 := by
    apply integral_ray_eq_zero_of_disjoint hφ
    apply Set.disjoint_left.mpr
    intro z hz hzray
    have hzV' := hφV hz
    exact hzV' (mem_iUnion₂.mpr ⟨θ, Finset.mem_erase.mpr ⟨hne, hθ⟩, hzray⟩)
  rw [polygonMeasure, integral_edgeMeasure hφ hφc _ _ (fun θ _ => weight_nonneg s θ)]
  by_cases hmem : z₀.arg ∈ T
  · exact Finset.sum_eq_single z₀.arg
      (fun θ hθ hne => by rw [hzero θ hθ hne, mul_zero])
      (fun hn => (hn hmem).elim)
  · have hd : weight s z₀.arg = 0 := weight_eq_zero_of_notMem z₀.arg_mem_Ioc hmem
    rw [hd, zero_mul]
    apply Finset.sum_eq_zero
    intro θ hθ
    rw [hzero θ hθ (fun he => hmem (he ▸ hθ)), mul_zero]

#print axioms exists_local_pairing
end V10.PolygonRayLocalization
