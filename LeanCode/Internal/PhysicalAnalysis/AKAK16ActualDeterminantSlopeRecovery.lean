import AKAK15ActualDeterminantCoefficients

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularCoupledInverse Grad.AnnularKnownLow
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularHighGenerators
open Grad.SourceCollarFullSource Grad.BoundaryTrace

/-- Exact scalar Fourier symbol of the projected original determinant RHS. -/
def determinantModeRHS (length radius : ℝ) (mode : ℤ × ℤ) (values : Fin 4 → ComplexEuclidean 1) : ComplexEuclidean 1 :=
  (if mode.1 = 0 then (0 : ℂ) else 1) •
    ((-((radius : ℂ)⁻¹)) • values 0 -
      (length : ℂ)⁻¹ • (frequencyNumerator (some true) mode • values 1) -
      (radius : ℂ)⁻¹ • (frequencyNumerator (some false) mode • values 2) +
      frequencyNumerator (some false) mode • values 3)

private theorem projectedOriginalFirst (length radius : ℝ) (mode : ℤ × ℤ)
    (physical original : ComplexEuclidean 1 × ComplexEuclidean 1) (x c v g : ComplexEuclidean 1)
    (values : Fin 4 → ComplexEuclidean 1)
    (physicalLaw : physical = (if mode.1 = 0 then (0 : ℂ) else 1) • original)
    (originalLaw : original.1 = (-((radius : ℂ)⁻¹)) • x -
      (length : ℂ)⁻¹ • (frequencyNumerator (some true) mode • c) -
      (radius : ℂ)⁻¹ • (frequencyNumerator (some false) mode • v) + frequencyNumerator (some false) mode • g)
    (valuesLaw : values = ![x,c,v,g]) : physical.1 = determinantModeRHS length radius mode values := by
  rw [physicalLaw,valuesLaw]
  change (if mode.1 = 0 then (0 : ℂ) else 1) • original.1 = _
  rw [originalLaw]
  rfl

theorem determinantModeRHS_continuousOn (lower length : ℝ) (positive : 0 < lower)
    (mode : ℤ × ℤ) (values : ℝ → Fin 4 → ComplexEuclidean 1)
    (continuousValues : ∀ index, ContinuousOn (fun radius => values radius index) (Icc lower 1)) :
    ContinuousOn (fun radius => determinantModeRHS length radius mode (values radius)) (Icc lower 1) :=
  (((((reciprocalRadius_smooth lower positive).continuousOn.neg.smul (continuousValues 0)).sub
    (((continuousValues 1).const_smul (frequencyNumerator (some true) mode)).const_smul ((length : ℂ)⁻¹))).sub
      ((reciprocalRadius_smooth lower positive).continuousOn.smul
        ((continuousValues 2).const_smul (frequencyNumerator (some false) mode)))).add
      ((continuousValues 3).const_smul (frequencyNumerator (some false) mode))).const_smul
      (if mode.1 = 0 then (0 : ℂ) else 1)

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (field : CoupledSpace lower length positive lengthPositive)
    (seven : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data field))
    (third : SmoothLowPhysicalRow parameters lower positive
      (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2)

variable (curves : ActualSourceRadialCurves parameters lower positive (lowerHalf.trans_lt (by norm_num)) data)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)

/-- The genuine full original radial PDE gives the exact determinant RHS
on the SAME coefficients of x,c,rV,g. -/
theorem actualDeterminantSlope_ae (mode : ℤ × ℤ) :
    (fun radius => (generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data field curves allGrades mode radius).1)
      =ᵐ[volume.restrict (Icc lower 1)] fun radius => determinantModeRHS length radius mode
        (fun index => actualDeterminantCoefficientCurves parameters length compact lower positive lowerHalf lengthPositive state data field seven third 0 radius index mode) := by
  filter_upwards [generalPhysicalRHSCurve_actual parameters length compact lower positive lowerHalf lengthPositive state data field curves allGrades mode,
    generalOriginalFullRHS_literal parameters length compact lower positive lowerHalf lengthPositive state data field,
    actualDeterminantCoefficientCurves_actual parameters length compact lower positive lowerHalf lengthPositive state data field seven third]
      with radius physical original actual
  exact projectedOriginalFirst length radius mode
    (generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data field curves allGrades mode radius)
    (generalOriginalFullRHS parameters length compact lower positive lowerHalf lengthPositive state data field radius mode)
    (sameCoupledXCoefficient parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive field 0
      (radialClamp lower (lowerHalf.trans (by norm_num)) radius) mode)
    (lowRhoPhysicalCoefficient parameters lower positive
      (lowPhysicalRowAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state 1
        (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data field)) radius mode)
    (lowRhoPhysicalCoefficient parameters lower positive
      (lowPhysicalRowAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state 2
        (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data field)) radius mode)
    (lowRhoPhysicalCoefficient parameters lower positive (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2 radius mode)
    (fun index => actualDeterminantCoefficientCurves parameters length compact lower positive lowerHalf lengthPositive state data field seven third 0 radius index mode)
    physical (congrArg Prod.fst (original mode)) (actual mode)

/-- Continuous representative recovery upgrades the actual AE equation at
every radius of the original closed collar. -/
theorem actualDeterminantSlope_pointwise (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    (generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data field curves allGrades mode radius).1 =
      determinantModeRHS length radius mode
        (fun index => actualDeterminantCoefficientCurves parameters length compact lower positive lowerHalf lengthPositive state data field seven third 0 radius index mode) := by
  apply collarCurve_eq_of_ae lower (lowerHalf.trans_lt (by norm_num))
    (fun location => (generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data field curves allGrades mode location).1)
    (fun location => determinantModeRHS length location mode
      (fun index => actualDeterminantCoefficientCurves parameters length compact lower positive lowerHalf lengthPositive state data field seven third 0 location index mode))
    (continuous_fst.comp (generalPhysicalRHSCurve parameters length compact lower positive lowerHalf lengthPositive state data field curves allGrades mode).continuous).continuousOn
    (determinantModeRHS_continuousOn lower length positive mode _ (fun index =>
      (lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 mode).continuous.comp_continuousOn
        (actualDeterminantCoefficientCurves_smooth parameters length compact lower positive lowerHalf lengthPositive state data field seven third 0 index).continuousOn))
    (actualDeterminantSlope_ae parameters length compact lower positive lowerHalf lengthPositive state data field seven third curves allGrades mode) inside

end Grad.ActualPolarEquations
