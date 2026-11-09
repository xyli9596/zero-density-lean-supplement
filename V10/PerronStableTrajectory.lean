import V10.PerronStableDimension
import V10.PerronStableFlowUniqueness

/-!
# Stable initial values characterize bounded actual trajectories

This connects the constructed finite-dimensional initial subspace to any
given continuous trajectory of the actual ODE. Only derivatives strictly
inside the half-line are required. The forward direction uses actual ODE
uniqueness, so membership is not merely membership in an unrelated graph.
-/
noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace V10.PerronStableSubspace
open V10.PerronStableFlowODE

variable {ι : Type*} [Fintype ι]

/-- The actual diagonal operator, with no basis or matrix instance assumptions. -/
def diagonalCoefficient (lam : ι → ℂ) : (ι → ℂ) →L[ℂ] (ι → ℂ) :=
  ContinuousLinearMap.pi fun i => (lam i) • ContinuousLinearMap.proj i

omit [Fintype ι] in
@[simp] theorem diagonalCoefficient_apply (lam v : ι → ℂ) (i : ι) :
    diagonalCoefficient lam v i = lam i * v i := rfl

variable (T δ η : ℝ) (hδ : 0 < δ) (hη : 0 ≤ η)
variable (mode : ι → Bool) (lam : ι → ℂ)
variable (hgap : ∀ i, if mode i then (lam i).re ≤ -δ else δ ≤ (lam i).re)
variable (R : Ici T → (ι → ℂ) →L[ℂ] (ι → ℂ)) (hR : Continuous R)
variable (hsmallR : ∀ s, ‖R s‖ ≤ η) (hsmall : decayMass δ * η < 1)

/-- An arbitrary actual trajectory is bounded on the half-line exactly when
its initial value lies in the constructed bounded-ODE initial subspace. -/
theorem initial_mem_iff_bounded {z : ℝ → (ι → ℂ)}
    (hz : ContinuousOn z (Ici T))
    (hzode : ∀ r > T, HasDerivAt z
      (fun i => lam i * z r i + R (clamp T r) (z r) i) r) :
    z T ∈ boundedODEInitialStates T δ η hδ hη mode lam hgap R hR hsmallR hsmall ↔
      ∃ C : ℝ, ∀ t ≥ T, ‖z t‖ ≤ C := by
  constructor
  · rintro ⟨u, huT, huode⟩
    let A : ℝ → (ι → ℂ) →L[ℂ] (ι → ℂ) :=
      fun t => diagonalCoefficient lam + R (clamp T t)
    have hAc : ContinuousOn A (Ici T) :=
      (continuous_const.add (hR.comp (continuous_clamp T))).continuousOn
    have huc : ContinuousOn (extend u) (Ici T) :=
      (u.continuous.comp (continuous_clamp T)).continuousOn
    have hdz : ∀ r > T, HasDerivAt z (A r (z r)) r := hzode
    have hdu : ∀ r > T, HasDerivAt (extend u) (A r (extend u r)) r := huode
    have heq : EqOn z (extend u) (Ici T) :=
      V10.PerronStableFlow.solution_eqOn_halfline A hAc hz huc hdz hdu (by
        rw [extend_of_mem u (le_refl T)]
        exact huT.symm)
    refine ⟨‖u‖, fun t ht => ?_⟩
    rw [heq ht, extend_of_mem u ht]
    exact u.norm_coe_le_norm _
  · rintro ⟨C, hC⟩
    let u : Ici T →ᵇ (ι → ℂ) :=
      BoundedContinuousFunction.ofNormedAddCommGroup (fun t : Ici T => z t)
        (continuousOn_iff_continuous_domRestrict.mp hz) C (fun t => hC t t.property)
    refine ⟨u, rfl, ?_⟩
    intro r hr
    have heq : ∀ᶠ t in 𝓝 r, extend u t = z t := by
      filter_upwards [Ioi_mem_nhds hr] with t ht
      rw [extend_of_mem u ht.le]
      rfl
    have heqr : extend u r = z r := by
      rw [extend_of_mem u hr.le]
      rfl
    rw [heqr]
    exact (hzode r hr).congr_of_eventuallyEq heq

/-- The equivalent graph formulation, convenient before packaging the
actual initial-value submodule. -/
theorem initialGraph_mem_iff_bounded {z : ℝ → (ι → ℂ)}
    (hz : ContinuousOn z (Ici T))
    (hzode : ∀ r > T, HasDerivAt z
      (fun i => lam i * z r i + R (clamp T r) (z r) i) r) :
    z T ∈ initialGraph T δ η hδ hη mode lam hgap R hR hsmallR hsmall ↔
      ∃ C : ℝ, ∀ t ≥ T, ‖z t‖ ≤ C := by
  rw [← boundedODEInitialStates_eq_initialGraph]
  exact initial_mem_iff_bounded T δ η hδ hη mode lam hgap R hR hsmallR hsmall hz hzode

#print axioms initial_mem_iff_bounded
#print axioms initialGraph_mem_iff_bounded
end V10.PerronStableSubspace
