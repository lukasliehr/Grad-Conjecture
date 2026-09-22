import AKBA10ActualOriginalGraphEntry

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
namespace Grad.OriginalKernelGraphRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.SourceCollarFullSource
open Grad.AnnularReconstruction Grad.AnnularOriginalSmoothCore Grad.AnnularOriginalCoreRealization
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularFullGraph Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.OriginalKernelRetainedDecay Grad.BoundaryTrace

theorem originalPhysicalCoefficient_eq_double {lower : ℝ} (field : OriginalPhysicalField)
    (smooth : OriginalPhysicalClosedSmooth lower field) (radius : ℝ) (inside : radius ∈ Icc lower 1)
    (mode : ℤ × ℤ) : originalPhysicalCoefficient field radius mode =
      doubleCoefficient (fun angles => field (radius,angles)) mode := by
  exact (doubleCoefficient_swap (fun angles => field (radius,angles)) (smooth.slice radius inside) mode.1 mode.2).symm

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 8 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (total vector : ACore parameters 3) (scalar : ACore parameters 1)

theorem originalKernelSmoothTuple_pressureCoefficient (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    originalPhysicalCoefficient
      ((originalKernelSmoothTuple parameters length rho epsilon base small lower positive bounded total vector scalar).val 0) radius mode =
      lambdaCircleCoefficient parameters radius
        (originalKernelPhysicalP parameters length rho epsilon base small ⟨radius,positive.le.trans inside.1,inside.2⟩ total vector scalar) mode := by
  let tuple := originalKernelSmoothTuple parameters length rho epsilon base small lower positive bounded total vector scalar
  rw [originalPhysicalCoefficient_eq_double _ (tuple.property.1 0).1 radius inside mode]
  have same := funext (originalKernelSmoothTuple_p parameters length rho epsilon base small lower positive bounded total vector scalar radius inside)
  rw [same]
  exact (originalKernelPhysicalP_represents parameters length rho epsilon base small _ total vector scalar mode).symm

theorem originalKernelSmoothTuple_scalarCoefficient (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    originalPhysicalCoefficient
      ((originalKernelSmoothTuple parameters length rho epsilon base small lower positive bounded total vector scalar).val 1) radius mode =
      lambdaCircleCoefficient parameters radius
        (originalCoreCircleTrace parameters (originalKernelXi total vector scalar) ⟨radius,positive.le.trans inside.1,inside.2⟩) mode := by
  let tuple := originalKernelSmoothTuple parameters length rho epsilon base small lower positive bounded total vector scalar
  rw [originalPhysicalCoefficient_eq_double _ (tuple.property.1 1).1 radius inside mode]
  have same := funext (originalKernelSmoothTuple_xi parameters length rho epsilon base small lower positive bounded total vector scalar radius inside)
  rw [same]
  exact (originalCoreCircleTrace_represents parameters (originalKernelXi total vector scalar) _ mode).symm

end Grad.OriginalKernelGraphRestriction
