import AKBD26SameCartesianSignedCofactorFlux

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualDeterminantEquations
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualBoundaryPrimitives Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.SourceCollar Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation Grad.ActualPolarFlux Grad.ActualCartesianEquations
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularSourceGraph
open Grad.AnnularGeneralSourceRegularity Grad.AnnularHighGenerators

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (solution : CoupledSpace lower length positive lengthPositive)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade solution weighted)
    (smooth : ∀ grade, ContDiffOn ℝ ∞
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive solution grade) (Icc lower 1))
    (curves : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution))
    (force : SmoothLowPhysicalRow parameters lower positive (strongKnownBulk parameters lower positive bounded.le data 3))


open Grad.ActualCartesianDescent Grad.PhysicalFamily

/-- The actual signed cofactor flux has precisely L times the original
polar determinant divergence, with genuine Cartesian derivatives. -/
theorem sameCartesianCofactorFlux_divergence (radius : ℝ) (inside : radius ∈ Ioo lower 1) (polar axial : ℝ) :
    cartesianDeterminantDivergence length
      ((samePolarCofactorVector parameters length compact lower positive bounded state curves).cartesianCovariant.cartesianField bounded)
      (polarPlane (radius,polar),axial) =
      (length : ℂ)*polarDeterminantDivergence parameters length compact lower positive bounded state lengthPositive data solution curves radius (polar,axial) := by
  have actual := sameCartesianRotation_divergence
    (samePolarCofactorVector parameters length compact lower positive bounded state curves) bounded
    length (ne_of_gt lengthPositive) radius inside polar axial
  rw [samePolarCofactorVector_directional parameters length compact lower positive bounded state curves 0 (1,0,0) radius inside,
    samePolarCofactorVector_directional parameters length compact lower positive bounded state curves 1 (0,1,0) radius inside,
    samePolarCofactorVector_directional parameters length compact lower positive bounded state curves 2 (0,0,1) radius inside,
    samePolarCofactorVector_component parameters length compact lower positive bounded state curves 0 radius ⟨inside.1.le,inside.2.le⟩] at actual
  exact actual

end Grad.ActualDeterminantEquations
