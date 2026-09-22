import AKBD12SameGenuineAngularAxialCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
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

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (solution : CoupledSpace lower length positive lengthPositive)
    (curves : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution))

/-- The first accepted physical force equation gives the exact second angular
component, retaining the circular minus-two contribution in r0. -/
theorem sameCovariant_secondAngularForce (radius : ℝ) (inside : radius ∈ Ioo lower 1) (polar axial : ℝ) :
    let covariant := curves.covariant parameters length compact lower positive bounded state.val
    scalarDirectionalField covariant bounded 1 (0,1,0) (radius,polar,axial) =
      scalarDirectionalField curves bounded 3 (0,1,0) (radius,polar,axial) +
      (covariant.forceZero parameters length compact lower positive bounded state).fullField bounded (radius,polar,axial) 0 -
      curves.fullField bounded (radius,polar,axial) 4 := by
  dsimp only
  rw [sameCovariant_scalarPolar parameters length compact lower positive bounded state lengthPositive data solution curves _ radius inside polar axial,
      sameSeven_scalarPolar parameters length lower positive bounded lengthPositive data solution curves radius inside polar axial]
  rw [fullField_originalForceZero parameters length compact lower positive bounded state _ radius ⟨inside.1.le,inside.2.le⟩]
  have law := congrArg (fun value : ComplexEuclidean 1 => value 0)
    (sharedFull_firstForce_pointwise parameters length compact lower positive bounded lengthPositive state.val data solution curves
      radius ⟨inside.1.le,inside.2.le⟩ (polar,axial))
  dsimp only at law
  simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul] at law
  simp_rw [fullField_bulkUnit_zero_scalar _ bounded _ radius ⟨inside.1.le,inside.2.le⟩] at law
  linear_combination -law

/-- The third accepted force equation gives the exact third angular component;
the projection remains inside the variable cofactor multiplication. -/
theorem sameCovariant_thirdAngularForce (radius : ℝ) (inside : radius ∈ Ioo lower 1) (polar axial : ℝ) :
    let covariant := curves.covariant parameters length compact lower positive bounded state.val
    let force := physicalForceCurves parameters length compact lower positive bounded state.val 1 covariant
    scalarDirectionalField covariant bounded 2 (0,1,0) (radius,polar,axial) =
      (radius : ℂ) / (length : ℂ) * scalarDirectionalField curves bounded 3 (0,0,1) (radius,polar,axial) -
      removePolarMean (fun angles => force.fullField bounded (radius,angles) 0) (polar,axial) +
      curves.fullField bounded (radius,polar,axial) 6 := by
  dsimp only
  rw [sameCovariant_scalarPolar parameters length compact lower positive bounded state lengthPositive data solution curves _ radius inside polar axial,
    sameSeven_scalarAxial parameters length lower positive bounded lengthPositive data solution curves radius inside polar axial]
  have law := congrArg (fun value : ComplexEuclidean 1 => value 0)
    (sharedFull_thirdForce_pointwise parameters length compact lower positive bounded lengthPositive state.val data solution curves
      radius ⟨inside.1.le,inside.2.le⟩ (polar,axial))
  dsimp only at law
  simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul] at law
  simp_rw [fullField_bulkUnit_zero_scalar _ bounded _ radius ⟨inside.1.le,inside.2.le⟩] at law
  rw [removePolarMean_coordinate _
    ((physicalForceCurves parameters length compact lower positive bounded state.val 1
      (curves.covariant parameters length compact lower positive bounded state.val)).fullField_continuous_angles bounded radius ⟨inside.1.le,inside.2.le⟩) (polar,axial)] at law
  have nonzero : (radius : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (positive.trans inside.1))
  have cancellation : (radius : ℂ) / (length : ℂ) * ((radius : ℂ)⁻¹ * curves.fullField bounded (radius,polar,axial) 2) =
      (length : ℂ)⁻¹ * curves.fullField bounded (radius,polar,axial) 2 := by field_simp [nonzero]
  rw [cancellation]
  linear_combination law

end Grad.ActualDeterminantEquations
