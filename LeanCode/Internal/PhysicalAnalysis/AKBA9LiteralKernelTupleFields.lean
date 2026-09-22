import AKBA8SameOriginalKernelTuple

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
open scoped ContDiff
namespace Grad.OriginalKernelGraphRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.AnnularCurrentEnergy
open Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction Grad.ActualSmoothPhysicalField
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.OriginalKernelRetainedDecay Grad.SourceCollarAngular Grad.AnnularOriginalSmoothCore Grad.SourceCollarFullSource

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 8 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (total vector : ACore parameters 3) (scalar : ACore parameters 1)

theorem originalKernelPField_literal (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    originalKernelPField parameters length rho epsilon base small lower positive bounded total vector scalar (radius,angles) =
      removePolarMean (originalPhysicalRawFlux parameters length epsilon base ⟨radius,positive.le.trans inside.1,inside.2⟩
        (originalCoreCircle parameters vector ⟨radius,positive.le.trans inside.1,inside.2⟩)
        (originalCoreCircle parameters (originalKernelXi total vector scalar) ⟨radius,positive.le.trans inside.1,inside.2⟩)) angles := by
  unfold originalKernelPField
  rw [SmoothLowPhysicalRow.fullField_meanFree _ bounded radius inside angles]
  apply congrArg (fun field => removePolarMean field angles)
  funext query
  rw [originalRawFluxCurves_fullField parameters length rho epsilon base small lower positive bounded _ _ radius inside query]
  have vectorSame := funext (originalVectorLowCurves_fullField parameters lower positive bounded vector radius inside)
  have scalarSame := funext (originalCoreLowCurves_fullField parameters lower positive bounded (originalKernelXi total vector scalar) radius inside)
  rw [vectorSame,scalarSame]

theorem originalKernelXiField_literal (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    originalKernelXiField parameters lower positive bounded total vector scalar (radius,angles) =
      originalCoreCircle parameters (originalKernelXi total vector scalar) ⟨radius,positive.le.trans inside.1,inside.2⟩ angles :=
  originalCoreLowCurves_fullField parameters lower positive bounded _ radius inside angles

theorem originalKernelSmoothTuple_p (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (originalKernelSmoothTuple parameters length rho epsilon base small lower positive bounded total vector scalar).val 0 (radius,angles) =
      removePolarMean (originalPhysicalRawFlux parameters length epsilon base ⟨radius,positive.le.trans inside.1,inside.2⟩
        (originalCoreCircle parameters vector ⟨radius,positive.le.trans inside.1,inside.2⟩)
        (originalCoreCircle parameters (originalKernelXi total vector scalar) ⟨radius,positive.le.trans inside.1,inside.2⟩)) angles :=
  originalKernelPField_literal parameters length rho epsilon base small lower positive bounded total vector scalar radius inside angles

theorem originalKernelSmoothTuple_xi (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (originalKernelSmoothTuple parameters length rho epsilon base small lower positive bounded total vector scalar).val 1 (radius,angles) =
      originalCoreCircle parameters (originalKernelXi total vector scalar) ⟨radius,positive.le.trans inside.1,inside.2⟩ angles :=
  originalKernelXiField_literal parameters lower positive bounded total vector scalar radius inside angles

theorem originalKernelSmoothTuple_sources :
    (originalKernelSmoothTuple parameters length rho epsilon base small lower positive bounded total vector scalar).val 2=0 ∧
    (originalKernelSmoothTuple parameters length rho epsilon base small lower positive bounded total vector scalar).val 3=0 := ⟨rfl,rfl⟩

end Grad.OriginalKernelGraphRestriction
