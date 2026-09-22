import AKT5SamePuncturedPhysicalHilbertField

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set Filter
open scoped Topology
namespace Grad.ActualPuncturedFamily
open Grad.SourceCollarCoefficients Grad.ClosedJets Grad.CartesianState Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularHighGenerators Grad.AnnularRestriction
open Grad.AnnularWeightedSmoothCore Grad.AnnularSmoothCore Grad.AnnularIncomingIntegrability Grad.PhaseAlgebra

variable (parameters : PhaseParameters) (length : ℝ) (lengthPositive : 0 < length)
    (lower : ℕ → ℝ) (positive : ∀ index, 0 < lower index) (bounded : ∀ index, lower index < 1)
    (decreasing : Antitone lower) (cofinal : Tendsto lower atTop (𝓝 0))
    (fields : ∀ index, CoupledSpace (lower index) length (positive index) lengthPositive)
    (allGrades : ∀ index grade, ∃ weighted : CoupledSpace (lower index) length (positive index) lengthPositive,
      CoupledInsertedGrade (lower index) length (positive index) lengthPositive grade (fields index) weighted)
    (compatible : ActualRetainedFamilyCompatible length lengthPositive lower positive bounded decreasing fields)

private abbrev physical := puncturedPhysicalPair parameters length lengthPositive lower positive bounded cofinal fields allGrades
private abbrev weighted := puncturedWeightedPair parameters length lengthPositive lower positive bounded cofinal fields allGrades

include compatible

/-- Every glued grade is the literal full Fourier insertion of the SAME
physical field, rather than a separately chosen solution. -/
theorem puncturedPhysicalPair_grade (grade : ℕ) (radius : ℝ) (inside : radius ∈ Ioc (0 : ℝ) 1) (mode : ℤ × ℤ) :
    ((physical parameters length lengthPositive lower positive bounded cofinal fields allGrades grade radius).1 mode,
      (physical parameters length lengthPositive lower positive bounded cofinal fields allGrades grade radius).2 mode) =
    ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
      ((physical parameters length lengthPositive lower positive bounded cofinal fields allGrades 0 radius).1 mode,
        (physical parameters length lengthPositive lower positive bounded cofinal fields allGrades 0 radius).2 mode) := by
  let index := selectedInnerCollar lower cofinal radius inside.1
  have localInside : radius ∈ Icc (lower index) 1 := ⟨(selectedInnerCollar_lt lower cofinal radius inside.1).le,inside.2⟩
  rw [puncturedPhysicalPair_physical parameters length lengthPositive lower positive bounded decreasing cofinal fields allGrades compatible grade index radius localInside,
    puncturedPhysicalPair_physical parameters length lengthPositive lower positive bounded decreasing cofinal fields allGrades compatible 0 index radius localInside,
    sameCoupledXCoefficient_grade parameters (lower index) length (positive index) (bounded index) lengthPositive (fields index) grade,
    sameCoupledXiCoefficient_grade parameters (lower index) length (positive index) (bounded index) lengthPositive (fields index) grade]
  rfl

/-- Original analytic width and phase relate the two actual global fields
pointwise at every positive radius and every full Fourier mode. -/
theorem puncturedWeightedPair_exactPhase (grade : ℕ) (radius : ℝ) (inside : radius ∈ Ioc (0 : ℝ) 1) (mode : ℤ × ℤ) :
    ((weighted parameters length lengthPositive lower positive bounded cofinal fields allGrades grade radius).1 mode,
      (weighted parameters length lengthPositive lower positive bounded cofinal fields allGrades grade radius).2 mode) =
    Real.exp (radialPhase parameters radius mode.2) •
      ((physical parameters length lengthPositive lower positive bounded cofinal fields allGrades grade radius).1 mode,
        (physical parameters length lengthPositive lower positive bounded cofinal fields allGrades grade radius).2 mode) := by
  let index := selectedInnerCollar lower cofinal radius inside.1
  have localInside : radius ∈ Icc (lower index) 1 := ⟨(selectedInnerCollar_lt lower cofinal radius inside.1).le,inside.2⟩
  rw [puncturedWeightedPair_physical parameters length lengthPositive lower positive bounded decreasing cofinal fields allGrades compatible grade index radius localInside,
    puncturedPhysicalPair_physical parameters length lengthPositive lower positive bounded decreasing cofinal fields allGrades compatible grade index radius localInside]
  rfl

theorem puncturedPhysicalPair_meanFree (grade : ℕ) (radius : ℝ) (inside : radius ∈ Ioc (0 : ℝ) 1) (cell : ℤ) :
    (physical parameters length lengthPositive lower positive bounded cofinal fields allGrades grade radius).1 (0,cell) = 0 ∧
      (physical parameters length lengthPositive lower positive bounded cofinal fields allGrades grade radius).2 (0,cell) = 0 := by
  let index := selectedInnerCollar lower cofinal radius inside.1
  have localInside : radius ∈ Icc (lower index) 1 := ⟨(selectedInnerCollar_lt lower cofinal radius inside.1).le,inside.2⟩
  have same := puncturedPhysicalPair_physical parameters length lengthPositive lower positive bounded decreasing cofinal fields allGrades compatible grade index radius localInside (0,cell)
  exact ⟨(congrArg Prod.fst same).trans (sameCoupledXCoefficient_meanZero parameters (lower index) length (positive index) (bounded index) lengthPositive (fields index) grade ⟨radius,localInside⟩ cell),
    (congrArg Prod.snd same).trans (sameCoupledXiCoefficient_meanZero parameters (lower index) length (positive index) (bounded index) lengthPositive (fields index) grade ⟨radius,localInside⟩ cell)⟩

end Grad.ActualPuncturedFamily
