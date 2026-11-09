import ZeroDensity.CharacteristicEquation
import ZeroDensity.InverseGeometry
import ZeroDensity.ScaledEquation
import ZeroDensity.CandidateFamily
import ZeroDensity.CountingTransfer
import Mathlib.Topology.Instances.EReal.Lemmas

/-! The complete target for manuscript Theorem 3.1, with its actual phase
map, fixed inverse branch, solution-defined root selection and polygon.

`Theorem31Target` is a proposition WITHOUT a proof. In particular, compiling
this file does not certify the main counting theorem. No missing analytic
statement is declared as an axiom or as an admissibility field.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Metric
open scoped Topology BigOperators
namespace ZeroDensity.MainTheorem
open Statement MaximalCoefficientData CountGeometry

def rightHalfPlane : Set ℂ := {t | 0 < t.re}

def phaseDerivative (β : ℝ) (t : ℂ) : ℂ :=
  Complex.exp ((β : ℂ) * Complex.log t + t)

/-- This is the primitive in equation (2.5), including its arbitrary constant. -/
def IsPhasePrimitive (Φ : ℂ → ℂ) (β : ℝ) (C : ℂ) : Prop :=
  Φ 1 = C ∧ ∀ t ∈ rightHalfPlane, HasDerivAt Φ (phaseDerivative β t) t

/-- An inverse branch is an actual analytic right inverse with image in the
right half-plane. Its asymptotic expansion is NOT an input field. -/
structure InverseBranch (Φ : ℂ → ℂ) where
  left : ℝ
  right : ℝ
  S₀ : ℝ
  left_lt_right : left < right
  opening_lt_two_pi : right - left < 2 * Real.pi
  radius_pos : 0 < S₀
  ψ : ℂ → ℂ
  analytic : AnalyticOnNhd ℂ ψ (angularSector S₀ left right)
  image_right : MapsTo ψ (angularSector S₀ left right) rightHalfPlane
  right_inverse : ∀ s ∈ angularSector S₀ left right, Φ (ψ s) = s

def inverseMap {n : ℕ} {E : EquationData n} (S : Selection E)
    {Φ : ℂ → ℂ} (B : InverseBranch Φ) (s : ℂ) : ℂ := S.ω⁻¹ * B.ψ s

/-- At a zero, log modulus is minus infinity, as required for the indicator.
Using the real totalized value log 0 = 0 here would change negative indicators. -/
def logModulus (z : ℂ) : EReal :=
  if z = 0 then ⊥ else (Real.log ‖z‖ : EReal)

def phaseIndicator {n : ℕ} {E : EquationData n} (S : Selection E)
    {Φ : ℂ → ℂ} (B : InverseBranch Φ) (f : ℂ → ℂ) (θ : ℝ) : EReal :=
  limsup (fun R : ℝ => ((R⁻¹ : ℝ) : EReal) *
    logModulus (f (inverseMap S B ((R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))))) atTop

/-- Once finiteness has been proved, the real indicator determines the
same explicit local selection as in the manuscript. -/
def selectedRoots {n : ℕ} {E : EquationData n} (S : Selection E)
    {Φ : ℂ → ℂ} (B : InverseBranch Φ) (f : ℂ → ℂ) (l u : ℝ) : Finset ℂ :=
  LocalRootSelection.selected (CharacteristicEquation.roots E S)
    (fun θ => (phaseIndicator S B f θ).toReal) l u

def polygon {n : ℕ} {E : EquationData n} (S : Selection E)
    {Φ : ℂ → ℂ} (B : InverseBranch Φ) (f : ℂ → ℂ) (l u : ℝ) : Set ℂ :=
  CandidateFamily.rootPolygon (selectedRoots S B f l u)

/-- The actual supporting face, in the conjugate-root convention. -/
def supportingFace (K : Set ℂ) (θ : ℝ) : Set ℂ :=
  {ν | ν ∈ K ∧ ∀ κ ∈ K,
    (κ * Complex.exp (-((θ : ℂ) * Complex.I))).re ≤
      (ν * Complex.exp (-((θ : ℂ) * Complex.I))).re}

/-- A polygonal supporting face is a point or a segment. Its diameter is
therefore exactly its Euclidean length, rather than a perimeter. -/
def faceLength (K : Set ℂ) (θ : ℝ) : ℝ := Metric.diam (supportingFace K θ)

def angularFaceSum (K : Set ℂ) (α₁ α₂ : ℝ) : ℝ :=
  ∑ᶠ θ : ℝ, if θ ∈ Ioo α₁ α₂ then faceLength K θ else 0

def CountingConclusion31 {n : ℕ} {E : EquationData n} (S : Selection E)
    {Φ : ℂ → ℂ} (B : InverseBranch Φ) (l u S₀ : ℝ) (f : ℂ → ℂ) : Prop :=
  ∀ α₁ α₂ : ℝ, l < α₁ → α₁ < α₂ → α₂ < u →
    faceLength (polygon S B f l u) α₁ = 0 →
    faceLength (polygon S B f l u) α₂ = 0 →
    (fun r => count f (pullback (inverseMap S B) S₀ α₁ α₂) r -
      RadiusComparison.Q ‖S.ω‖ (beta E S : ℝ) r / (2 * Real.pi) *
        angularFaceSum (polygon S B f l u) α₁ α₂) =o[atTop]
      CountingTransfer.mainScale ‖S.ω‖ (beta E S : ℝ)

/-- Full target. The interval, inner radius and admissible pair are chosen
before the solution. The same explicitly selected roots are used for all
allowed angular subintervals. NO proof of this target is present yet. -/
def Theorem31Target : Prop :=
  ∀ (n : ℕ) (E : EquationData n) (S : Selection E) (C : ℂ) (Φ : ℂ → ℂ),
    IsPhasePrimitive Φ (beta E S : ℝ) C →
    ∀ B : InverseBranch Φ, ∀ θ ∈ Ioo B.left B.right,
      ∃ (l u S₀ : ℝ), B.left < l ∧ θ ∈ Ioo l u ∧ u < B.right ∧
        u - l < Real.pi ∧ B.S₀ < S₀ ∧
        ∃ P : AdmissiblePair E,
          P.left = l ∧ P.right = u ∧ P.S₀ = S₀ ∧
          P.a = ‖S.ω‖ ∧ P.β = (beta E S : ℝ) ∧
          P.phase_limits = characteristicCoefficient E S ∧
          P.domain = inverseMap S B '' angularSector S₀ l u ∧
          P.forward = (fun z => Φ (S.ω * z)) ∧ P.inverse = inverseMap S B ∧
          ∀ f : ℂ → ℂ, IsSolution E f → f ≠ 0 →
            (∀ η ∈ Ioo l u, ∃ h : ℝ, phaseIndicator S B f η = (h : EReal)) ∧
            (selectedRoots S B f l u).Nonempty ∧
            {η | η ∈ Ioo l u ∧ 0 < faceLength (polygon S B f l u) η}.Finite ∧
            CountingConclusion31 S B l u S₀ f

theorem selectedRoots_subset {n : ℕ} {E : EquationData n} (S : Selection E)
    {Φ : ℂ → ℂ} (B : InverseBranch Φ) (f : ℂ → ℂ) (l u : ℝ) :
    selectedRoots S B f l u ⊆ CharacteristicEquation.roots E S :=
  LocalRootSelection.selected_subset _ _ _ _

/-- Continuous finite alternatives supply the natural, explicit root subset.
The ODE-to-indicator implication is an outstanding analytic obligation. -/
theorem selectedRoots_nonempty {n : ℕ} {E : EquationData n} (S : Selection E)
    {Φ : ℂ → ℂ} (B : InverseBranch Φ) {f : ℂ → ℂ} {l u : ℝ}
    (hlu : l < u)
    (hc : ContinuousOn (fun θ => (phaseIndicator S B f θ).toReal) (Ioo l u))
    (halt : ∀ θ ∈ Ioo l u, ∃ μ ∈ CharacteristicEquation.roots E S,
      (phaseIndicator S B f θ).toReal = LocalRootSelection.projection μ θ) :
    (selectedRoots S B f l u).Nonempty :=
  LocalRootSelection.selected_nonempty _ hlu hc halt

#check Theorem31Target
#print axioms selectedRoots_subset
#print axioms selectedRoots_nonempty
end ZeroDensity.MainTheorem
