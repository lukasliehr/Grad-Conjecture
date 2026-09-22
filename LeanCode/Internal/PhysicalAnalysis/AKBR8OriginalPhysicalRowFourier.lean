import AKBR7OriginalPhysicalSeedInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalKernelOuterUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.NonlinearRange Grad.NonlinearQuotientBounds Grad.SourceCollar Grad.Cor18
open Grad.SourceCollarCoefficients Grad.SourceCollarDivision Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.BoundaryTrace
open Grad.GaugeCoefficients.Physical.Ledger Grad.BoundaryLift
open Grad.OriginalKernelRetainedDecay Grad.AnnularReconstruction Grad.PhysicalCoordinates

def originalBoundaryRadialOperator (angle : ℝ) : ComplexEuclidean 2→L[ℂ]ComplexEuclidean 1 :=
  (Real.cos angle : ℂ) • matrixUnit 0 0+(Real.sin angle : ℂ) • matrixUnit 0 1

def originalBoundaryRowSeries (parameters : PhaseParameters) (field : ACore parameters 2) (angles : ℝ×ℝ) : ComplexEuclidean 1 :=
  originalBoundaryRadialOperator angles.1 (originalCoreCircle parameters field ⟨1,zero_le_one,le_rfl⟩ angles)

theorem originalBoundaryRowSeries_continuous (parameters : PhaseParameters) (field : ACore parameters 2) :
    Continuous (originalBoundaryRowSeries parameters field) := by
  unfold originalBoundaryRowSeries originalBoundaryRadialOperator
  apply Continuous.add
  · exact (Complex.continuous_ofReal.comp (Real.continuous_cos.comp continuous_fst)).smul
      ((matrixUnit (0 : Fin 1) (0 : Fin 2)).continuous.comp (originalCoreCircle_continuous parameters field _))
  · exact (Complex.continuous_ofReal.comp (Real.continuous_sin.comp continuous_fst)).smul
      ((matrixUnit (0 : Fin 1) (1 : Fin 2)).continuous.comp (originalCoreCircle_continuous parameters field _))

theorem originalBoundaryPolarPoint (angle : ℝ) :
    Grad.SourceCollarDivision.polarClosedPoint 1 angle zero_le_one le_rfl=boundaryDiskPoint (angle : CellCircle) := by
  apply Subtype.ext
  change polarPlane (1,angle)=boundaryCirclePoint (angle : CellCircle)
  rw [boundaryCirclePoint_coe,polarPlane_eq]
  simp [radialDirection,collarPlane]

/-- The full two-angle physical boundary Fourier coefficient is the SAME
original CP7 row coefficient, before its high-angular projection. -/
theorem originalBoundaryRowSeries_coefficient (parameters : PhaseParameters) (field : ACore parameters 2) (mode : ℤ×ℤ) :
    doubleCoefficient (originalBoundaryRowSeries parameters field) mode=
      EuclideanSpace.single 0 (fourierCoeff (rowFunction parameters field mode.2) mode.1) := by
  have inner (polar : ℝ) :
      angularCoefficient (fun axial => originalBoundaryRowSeries parameters field (polar,axial)) mode.2=
        originalBoundaryRadialOperator polar ((field.val mode.2).value
          (Grad.SourceCollarDivision.polarClosedPoint 1 polar zero_le_one le_rfl)) := by
    exact (angularCoefficient_valueMap (originalBoundaryRadialOperator polar)
      (fun axial => originalCoreCircle parameters field ⟨1,zero_le_one,le_rfl⟩ (polar,axial))
      ((originalCoreCircle_continuous parameters field _).comp (continuous_const.prodMk continuous_id)) mode.2).trans
        (congrArg (originalBoundaryRadialOperator polar) (originalCoreCircle_axialCoefficient parameters field _ polar mode.2))
  unfold doubleCoefficient
  simp_rw [inner]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  have continuousRow : Continuous (fun angle => originalBoundaryRadialOperator angle ((field.val mode.2).value
      (Grad.SourceCollarDivision.polarClosedPoint 1 angle zero_le_one le_rfl))) := by
    unfold originalBoundaryRadialOperator
    have point : Continuous (fun angle => Grad.SourceCollarDivision.polarClosedPoint 1 angle zero_le_one le_rfl) :=
      (polarPlane_smooth.continuous.comp (continuous_const.prodMk continuous_id)).subtype_mk _
    have value := (field.val mode.2).value.continuous.comp point
    exact ((Complex.continuous_ofReal.comp Real.continuous_cos).smul ((matrixUnit (0 : Fin 1) (0 : Fin 2)).continuous.comp value)).add
      ((Complex.continuous_ofReal.comp Real.continuous_sin).smul ((matrixUnit (0 : Fin 1) (1 : Fin 2)).continuous.comp value))
  rw [angularCoefficient_component _ continuousRow]
  simp only [PiLp.single_apply]
  have literal (angle : ℝ) :
      (originalBoundaryRadialOperator angle ((field.val mode.2).value
        (Grad.SourceCollarDivision.polarClosedPoint 1 angle zero_le_one le_rfl))) 0=
          rowFunction parameters field mode.2 (angle : CellCircle) := by
    rw [originalBoundaryPolarPoint]
    simp [originalBoundaryRadialOperator,matrixUnit_apply,operatorBasis,rowFunction,boundaryCirclePoint_coe,collarPlane]
  exact (congrArg (fun source : ℝ→ℂ => angularCoefficient source mode.1) (funext literal)).trans
    (angularCoefficient_circle _ _)

/-- The actual original smooth domain kills precisely the high part of
the SAME physical boundary series; no boundary condition is added. -/
theorem originalDomain_boundaryRowCoefficient_zero (parameters : PhaseParameters) (seed : Seed.Parameters)
    (inside : seed∈Seed.parameterDomain) (vector : ACore parameters 3)
    (constrained : VectorConstraints parameters seed inside (toPhysicalCore parameters vector))
    (mode : ℤ×ℤ) (high : 2 < |mode.1|) :
    doubleCoefficient (originalBoundaryRowSeries parameters
      (rowField parameters seed inside (toPhysicalCore parameters vector))) mode=0 := by
  rw [originalBoundaryRowSeries_coefficient]
  have row := congrArg (fun boundary : BoundaryCore parameters 1 => boundary.val mode) constrained.2.2.2
  change physicalRowFamily parameters seed inside (toPhysicalCore parameters vector) mode=0 at row
  simpa only [physicalRowFamily,if_neg (not_le.mpr high)] using row

end Grad.OriginalKernelOuterUniqueness
