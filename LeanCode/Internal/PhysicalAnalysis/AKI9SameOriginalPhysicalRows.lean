import AKI8SameOriginalFullPacket

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
namespace Grad.AnnularOriginalSmoothCore
open Grad.AnnularKernelContinuity Grad.AnnularKernelL2
open Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularSmoothCore
open Grad.AnnularCurrentLow Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.AnnularStrongOrbit Grad.AnnularWeightedSmoothCore Grad.AnnularSmoothSources
open Grad.GaugeCoefficients.Physical.Allocation
open scoped ContDiff

/-- Original physical action at the same radius is uniquely determined by
its full seven input coefficients. The statement retains the actual kernel. -/
theorem tuplePhysicalRows_of_packet (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (state : RetainedInverseState parameters length compact)
    (tuple : OriginalSmoothTuple parameters lower) (field : DivisionRow 7 lower)
    (packet : ∀ᵐ location ∂volume.restrict (Icc lower 1), ∀ inside : location ∈ Icc lower 1, ∀ mode,
      originalTupleNormalizedCoefficient parameters lower tuple ⟨location, inside⟩ mode =
        lowRhoPhysicalCoefficient parameters lower positive field location mode)
    (row : Fin 3) :
    ∀ᵐ location ∂volume.restrict (Icc lower 1), ∀ inside : location ∈ Icc lower 1, ∀ mode,
      negativeTraceCoefficient (radialKernelParameters parameters (tupleRadius lower positive ⟨location, inside⟩)) 0 0
        (tuplePhysicalRowTrace parameters length compact lower positive state tuple ⟨location, inside⟩ row) mode =
      lowRhoPhysicalCoefficient parameters lower positive
        (lowPhysicalRowAction parameters length compact lower positive bounded state row field) location mode := by
  filter_upwards [packet, lowRegularAction_physical parameters lower positive bounded
    (lowPhysicalRowKernel parameters length compact state row)
    (lowPhysicalRowKernel_regular parameters length compact state row) field] with location packet actual
  intro inside mode
  have radiusSame : collarRadius lower positive bounded location = tupleRadius lower positive ⟨location, inside⟩ := by
    apply Subtype.ext
    exact collarRadius_literal lower positive bounded location inside
  have original := fullNegativeKernelAction_coefficient_hasSum
    (radialKernelParameters parameters (tupleRadius lower positive ⟨location, inside⟩)) 0 0
    (lowPhysicalRowKernel parameters length compact state row (tupleRadius lower positive ⟨location, inside⟩))
    (sevenSlotFlatten _ 0 0 (tupleNormalizedInput parameters lower positive tuple ⟨location, inside⟩)) mode
  have actual := actual mode
  rw [radiusSame] at actual
  apply original.unique
  apply actual.congr_fun
  intro shift
  rw [tupleNormalizedInput_coefficient, packet inside]

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)
    (weightedSmooth : ∀ grade, ContDiffOn ℝ ∞
      (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core grade) (Icc lower 1))

theorem sameResponseOriginalTuple_rows (row : Fin 3) :
    ∀ᵐ location ∂volume.restrict (Icc lower 1), ∀ inside : location ∈ Icc lower 1, ∀ mode,
      negativeTraceCoefficient (radialKernelParameters parameters (tupleRadius lower positive ⟨location, inside⟩)) 0 0
        (tuplePhysicalRowTrace parameters length compact lower positive state
          (sameResponseOriginalTuple parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core weightedSmooth)
          ⟨location, inside⟩ row) mode =
      lowRhoPhysicalCoefficient parameters lower positive
        (lowPhysicalRowAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state row
          (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num))
            ((strongSmoothDenseMap parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive).mapping core)
            (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core))) location mode :=
  tuplePhysicalRows_of_packet parameters length compact lower positive (lowerHalf.trans (by norm_num)) state _ _
    (sameResponseOriginalTuple_packet parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core weightedSmooth) row

end Grad.AnnularOriginalSmoothCore
