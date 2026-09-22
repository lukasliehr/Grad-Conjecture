import AKBB7ActualPrimitiveDeterminantFields

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarFlux
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularCoupledInverse Grad.AnnularKnownLow
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularHighGenerators
open Grad.SourceCollarFullSource Grad.BoundaryTrace Grad.ActualPolarEquations

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (field : CoupledSpace lower length positive lengthPositive)
    (seven : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data field))
    (third : SmoothLowPhysicalRow parameters lower positive
      (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2)

private theorem primitiveP_coefficient (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    actualPrimitiveDeterminantCoefficientCurves parameters length compact lower positive lowerHalf lengthPositive state data field seven third 0 radius 0 mode =
      Grad.BoundaryKernelAction.angularInverseMultiplier mode • actualDeterminantCoefficientCurves parameters length compact lower positive lowerHalf lengthPositive state data field seven third 0 radius 0 mode :=
  sharedCorrectedP_physicalCurve parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state
    lengthPositive data field seven radius inside mode

private theorem primitiveC_coefficient (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    actualDeterminantCoefficientCurves parameters length compact lower positive lowerHalf lengthPositive state data field seven third 0 radius 1 mode =
      (Complex.I * (mode.1 : ℂ)) • actualPrimitiveDeterminantCoefficientCurves parameters length compact lower positive lowerHalf lengthPositive state data field seven third 0 radius 1 mode :=
  samePhysical_modeMultiplier
    (SmoothLowPhysicalRow.originalPhysicalRow parameters length compact lower positive lowerHalf state seven 1)
    (seven.bThree parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state)
    (lowerHalf.trans_lt (by norm_num)) (fun mode => Complex.I * (mode.1 : ℂ))
    (sharedBThree_angularCoefficients parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state
      lengthPositive data field) radius inside mode


private theorem primitiveV_coefficient (radius : ℝ) (mode : ℤ × ℤ) :
    actualDeterminantCoefficientCurves parameters length compact lower positive lowerHalf lengthPositive state data field seven third 0 radius 2 mode =
      actualPrimitiveDeterminantCoefficientCurves parameters length compact lower positive lowerHalf lengthPositive state data field seven third 0 radius 2 mode := by
  have same : actualDeterminantCoefficientCurves parameters length compact lower positive lowerHalf lengthPositive state data field seven third 0 radius 2 =
      actualPrimitiveDeterminantCoefficientCurves parameters length compact lower positive lowerHalf lengthPositive state data field seven third 0 radius 2 := by
    simp only [actualDeterminantCoefficientCurves,actualPrimitiveDeterminantCoefficientCurves,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  exact congrArg (fun value : CellL2 1 => value mode) same

private theorem primitiveG_coefficient (radius : ℝ) (mode : ℤ × ℤ) :
    actualDeterminantCoefficientCurves parameters length compact lower positive lowerHalf lengthPositive state data field seven third 0 radius 3 mode =
      actualPrimitiveDeterminantCoefficientCurves parameters length compact lower positive lowerHalf lengthPositive state data field seven third 0 radius 3 mode := by
  have same : actualDeterminantCoefficientCurves parameters length compact lower positive lowerHalf lengthPositive state data field seven third 0 radius 3 =
      actualPrimitiveDeterminantCoefficientCurves parameters length compact lower positive lowerHalf lengthPositive state data field seven third 0 radius 3 := by
    simp only [actualDeterminantCoefficientCurves,actualPrimitiveDeterminantCoefficientCurves,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  exact congrArg (fun value : CellL2 1 => value mode) same

/-- The exact physical p and b3 coefficients convert the original x equation
symbol into the primitive determinant equation on the SAME fields. -/
theorem actualPrimitiveDeterminantSymbol_same (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    primitiveDeterminantModeRHS length radius mode
      (fun index => actualPrimitiveDeterminantCoefficientCurves parameters length compact lower positive lowerHalf lengthPositive
        state data field seven third 0 radius index mode) =
      Grad.BoundaryKernelAction.angularInverseMultiplier mode • determinantModeRHS length radius mode
        (fun index => actualDeterminantCoefficientCurves parameters length compact lower positive lowerHalf lengthPositive
          state data field seven third 0 radius index mode) := by
  exact (primitiveDeterminantModeRHS_eq length radius mode
    (fun index => actualDeterminantCoefficientCurves parameters length compact lower positive lowerHalf lengthPositive state data field seven third 0 radius index mode)
    (fun index => actualPrimitiveDeterminantCoefficientCurves parameters length compact lower positive lowerHalf lengthPositive state data field seven third 0 radius index mode)
    (primitiveP_coefficient parameters length compact lower positive lowerHalf lengthPositive state data field seven third radius inside mode)
    (primitiveC_coefficient parameters length compact lower positive lowerHalf lengthPositive state data field seven third radius inside mode)
    (primitiveV_coefficient parameters length compact lower positive lowerHalf lengthPositive state data field seven third radius mode)
    (primitiveG_coefficient parameters length compact lower positive lowerHalf lengthPositive state data field seven third radius mode)).symm

variable (curves : ActualSourceRadialCurves parameters lower positive (lowerHalf.trans_lt (by norm_num)) data)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)

/-- The genuine original coefficient slope is exactly the literal p RHS. -/
theorem actualPrimitiveDeterminantSlope (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    Grad.BoundaryKernelAction.angularInverseMultiplier mode •
      (generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data field curves allGrades mode radius).1 =
      primitiveDeterminantModeRHS length radius mode
        (fun index => actualPrimitiveDeterminantCoefficientCurves parameters length compact lower positive lowerHalf lengthPositive
          state data field seven third 0 radius index mode) := by
  rw [actualDeterminantSlope_pointwise parameters length compact lower positive lowerHalf lengthPositive state data field seven third
    curves allGrades radius inside mode]
  exact (actualPrimitiveDeterminantSymbol_same parameters length compact lower positive lowerHalf lengthPositive state data field seven third
    radius inside mode).symm

end Grad.ActualPolarFlux
