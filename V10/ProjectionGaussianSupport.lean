import V10.ProjectionGaussianLoss
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic

/-! Full support of the actual Gaussian used in the projection argument.
It follows from real Gaussian absolute continuity, finite products, and
surjective continuous linear maps; no density formula is assumed. -/

noncomputable section
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Metric
open scoped Topology NNReal
namespace V10.ProjectionGaussianSupport
open ProjectionGaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem stdGaussian_isOpenPos : IsOpenPosMeasure (stdGaussian E) := by
  let : IsOpenPosMeasure (gaussianReal 0 1) :=
    (gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : ℝ≥0) ≠ 0)).isOpenPosMeasure
  unfold stdGaussian
  apply Continuous.isOpenPosMeasure_map (by fun_prop)
  intro x
  exact ⟨fun i => (stdOrthonormalBasis ℝ E).repr x i,
    (stdOrthonormalBasis ℝ E).sum_repr x⟩

instance complexGaussian_isOpenPos : IsOpenPosMeasure (complexGaussian E) := by
  let := stdGaussian_isOpenPos (E := E)
  unfold complexGaussian
  apply Continuous.isOpenPosMeasure_map (by fun_prop)
  intro x
  refine ⟨(Real.sqrt (1 / 2 : ℝ))⁻¹ • x, ?_⟩
  exact smul_inv_smul₀ (by positivity : Real.sqrt (1 / 2 : ℝ) ≠ 0) x

theorem complexGaussian_ball_pos (c : E) {r : ℝ} (hr : 0 < r) :
    0 < complexGaussian E (ball c r) :=
  isOpen_ball.measure_pos _ (nonempty_ball.mpr hr)

/-- Every open ball meets any Gaussian-almost-everywhere good set. In
particular, a Gaussian-a.e. finite projection series cannot be identically
minus infinity on a ball. -/
theorem exists_good_in_ball {P : E → Prop} (hP : ∀ᵐ x ∂complexGaussian E, P x)
    (c : E) {r : ℝ} (hr : 0 < r) : ∃ x ∈ ball c r, P x := by
  by_contra! h
  have hzero : complexGaussian E (ball c r) = 0 := by
    apply measure_mono_null (show ball c r ⊆ {x | ¬P x} from h)
    exact ae_iff.mp hP
  exact (complexGaussian_ball_pos c hr).ne' hzero

#print axioms stdGaussian_isOpenPos
#print axioms complexGaussian_ball_pos
#print axioms exists_good_in_ball
end V10.ProjectionGaussianSupport
