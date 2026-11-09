import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Image
import Mathlib.Tactic

/-! Finite root-subset candidates. This is a combinatorial assembly result:
it derives a finite family from a fixed finite root set, without assuming a
finite output family. It does not assert that analytic subsequential limits
select these candidates, or identify polygon edge jumps. -/
noncomputable section
set_option autoImplicit false
open Set
open scoped BigOperators
namespace ZeroDensity.CandidateFamily

/-- All possible outputs of a deterministic construction on root subsets. -/
def candidates {α β : Type*} [DecidableEq α] [DecidableEq β]
    (roots : Finset α) (build : Finset α → β) : Finset β :=
  roots.powerset.image build

theorem selected_mem {α β : Type*} [DecidableEq α] [DecidableEq β]
    (roots : Finset α) (build : Finset α → β) {s : Finset α}
    (hs : s ⊆ roots) : build s ∈ candidates roots build := by
  exact Finset.mem_image.mpr ⟨s, Finset.mem_powerset.mpr hs, rfl⟩

theorem candidate_card_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (roots : Finset α) (build : Finset α → β) :
    (candidates roots build).card ≤ 2 ^ roots.card := by
  exact (Finset.card_image_le).trans_eq (Finset.card_powerset roots)

/-- A parameter-dependent choice of root subsets has a finite output range.
The only selection hypothesis is inclusion in the fixed finite root set. -/
theorem selected_range_finite {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    (roots : Finset α) (build : Finset α → β) (select : γ → Finset α)
    (hs : ∀ t, select t ⊆ roots) : Set.Finite (Set.range (fun t => build (select t))) := by
  apply (candidates roots build).finite_toSet.subset
  rintro _ ⟨t,rfl⟩
  exact selected_mem roots build (hs t)

/-- Polygon associated with the conjugate roots in a selected subset. -/
def rootPolygon (s : Finset ℂ) : Set ℂ :=
  convexHull ℝ ((star : ℂ → ℂ) '' (s : Set ℂ))

theorem selected_polygons_finite {γ : Type*} (roots : Finset ℂ)
    (select : γ → Finset ℂ) (hs : ∀ t, select t ⊆ roots) :
    Set.Finite (Set.range (fun t => rootPolygon (select t))) := by
  classical
  exact selected_range_finite roots rootPolygon select hs

/-- Concrete finite step-function assembly from selected root subsets.
`jumps` and `weight` may subsequently be instantiated by proved polygon-edge
constructions; no geometric identification is assumed here. -/
def stepCandidate (jumps : Finset ℂ → Finset ℝ)
    (weight : Finset ℂ → ℝ → ℝ) (s : Finset ℂ) (θ : ℝ) : ℝ :=
  ∑ η ∈ jumps s, if η ≤ θ then weight s η else 0

theorem selected_step_functions_finite {γ : Type*} (roots : Finset ℂ)
    (jumps : Finset ℂ → Finset ℝ) (weight : Finset ℂ → ℝ → ℝ)
    (select : γ → Finset ℂ) (hs : ∀ t, select t ⊆ roots) :
    Set.Finite (Set.range (fun t => stepCandidate jumps weight (select t))) := by
  classical
  exact selected_range_finite roots (stepCandidate jumps weight) select hs

/-- Polygons and their assembled step functions have a common finite index
set, rather than two independently postulated finite families. -/
theorem paired_candidates_finite {γ : Type*} (roots : Finset ℂ)
    (jumps : Finset ℂ → Finset ℝ) (weight : Finset ℂ → ℝ → ℝ)
    (select : γ → Finset ℂ) (hs : ∀ t, select t ⊆ roots) :
    Set.Finite (Set.range (fun t =>
      (rootPolygon (select t), stepCandidate jumps weight (select t)))) := by
  classical
  exact selected_range_finite roots
    (fun s => (rootPolygon s, stepCandidate jumps weight s)) select hs

#print axioms selected_polygons_finite
#print axioms selected_step_functions_finite
#print axioms paired_candidates_finite
end ZeroDensity.CandidateFamily
