import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Tactic

/-! Integration of actual finite positive atomic counts. Each atom in E is
seen from a unit disk of centers of area π, entirely contained in the closed
unit thickening of E. Finite-sum integration supplies the exact counting bound. -/
noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Metric
open scoped Topology
namespace V10.AtomicCountIntegral
attribute [local instance] Classical.propDecidable

def atomCount (Z : Finset ℂ) (w : ℂ → ℝ) (E : Set ℂ) : ℝ :=
  ∑ u ∈ Z, if u ∈ E then w u else 0

theorem integrable_ball_indicator (u : ℂ) (a : ℝ) :
    Integrable ((closedBall u 1).indicator (fun _ : ℂ => a)) := by
  exact (integrableOn_const (isCompact_closedBall u (1 : ℝ)).measure_ne_top).integrable_indicator
    measurableSet_closedBall

theorem integral_ball_indicator (u : ℂ) (a : ℝ) :
    (∫ z, (closedBall u 1).indicator (fun _ : ℂ => a) z) = Real.pi * a := by
  rw [integral_indicator_const a measurableSet_closedBall]
  simp [Measure.real, Complex.volume_closedBall]

theorem atom_integral_over_thickening {E : Set ℂ} {u : ℂ} (hu : u ∈ E) (a : ℝ) :
    (∫ z in cthickening 1 E, (closedBall u 1).indicator (fun _ : ℂ => a) z) =
      Real.pi * a := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero, integral_ball_indicator]
  intro z hz
  apply Set.indicator_of_notMem
  intro hzu
  exact hz ((closedBall_subset_cthickening hu 1) hzu)

/-- A local unit-disk count bound integrates to the enlarged-set bound.
There are no assumptions on the distribution of atoms beyond positivity. -/
theorem atomCount_le_integral {Z : Finset ℂ} {w W : ℂ → ℝ} {E : Set ℂ} {C : ℝ}
    (hw : ∀ u ∈ Z, 0 ≤ w u) (hW : IntegrableOn W (cthickening 1 E))
    (hlocal : ∀ z ∈ cthickening 1 E, atomCount Z w (closedBall z 1) ≤ C * W z) :
    atomCount Z w E ≤ C / Real.pi * ∫ z in cthickening 1 E, W z := by
  classical
  let T := Z.filter (fun u => u ∈ E)
  let g : ℂ → ℝ := fun z => ∑ u ∈ T,
    (closedBall u 1).indicator (fun _ : ℂ => w u) z
  have hg : Integrable g := integrable_finsetSum T (fun u _ => integrable_ball_indicator u (w u))
  have he : (∫ z in cthickening 1 E, g z) = Real.pi * atomCount Z w E := by
    rw [show (∫ z in cthickening 1 E, g z) =
        ∑ u ∈ T, ∫ z in cthickening 1 E,
          (closedBall u 1).indicator (fun _ : ℂ => w u) z from
      integral_finsetSum _ (fun u _ => (integrable_ball_indicator u (w u)).integrableOn)]
    calc
      _ = ∑ u ∈ T, Real.pi * w u := by
        apply Finset.sum_congr rfl
        intro u hu
        exact atom_integral_over_thickening (Finset.mem_filter.mp hu).2 (w u)
      _ = Real.pi * atomCount Z w E := by
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_filter _ _
  have hle : ∀ z, g z ≤ atomCount Z w (closedBall z 1) := by
    intro z
    have hex : g z = ∑ u ∈ T, if u ∈ closedBall z 1 then w u else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      simp only [Set.indicator_apply, mem_closedBall, dist_comm z u]
    rw [hex]
    unfold atomCount
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro u hu _
    split_ifs
    · exact hw u hu
    · exact le_rfl
  have hbound : Real.pi * atomCount Z w E ≤ C * ∫ z in cthickening 1 E, W z := by
    rw [← he, ← integral_const_mul]
    exact setIntegral_mono_on hg.integrableOn (hW.const_mul C)
      isClosed_cthickening.measurableSet (fun z hz => (hle z).trans (hlocal z hz))
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ Real.pi_pos).mpr
  nlinarith [hbound]

#print axioms atomCount_le_integral
end V10.AtomicCountIntegral
