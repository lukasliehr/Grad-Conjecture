import AKBB2SamePrimitivePhysicalCurves
import AKAK17SamePhysicalDeterminantRadialPDE

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarFlux
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularCoupledInverse Grad.AnnularKnownLow
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularHighGenerators
open Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (field : CoupledSpace lower length positive lengthPositive)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
    (smooth : ∀ grade, ContDiffOn ℝ ∞
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade) (Icc lower 1))
    (seven : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data field))

include allGrades smooth

theorem sameSeven_originalXCurve (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    (seven.bulkUnit (0 : Fin 1) (0 : Fin 7)).physicalCurve 0 radius mode =
      originalPhysicalComponentCurve parameters lower length positive bounded lengthPositive field 0 0 radius mode := by
  apply collarCurve_eq_of_ae lower bounded _ _
    ((lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 mode).continuous.comp_continuousOn
      ((seven.bulkUnit (0 : Fin 1) (0 : Fin 7)).physicalCurve_smooth bounded 0).continuousOn)
    ((lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 mode).continuous.comp_continuousOn
      (originalPhysicalComponentCurve_smooth parameters lower length positive bounded lengthPositive field allGrades smooth 0 0).continuousOn) _ inside
  filter_upwards [(seven.bulkUnit (0 : Fin 1) (0 : Fin 7)).physicalCurve_actual bounded 0,
    fullStrongSevenInput_firstFour_physical parameters lower length positive bounded lengthPositive data field,
    lowRhoPhysicalCoefficient_bulkUnit parameters lower positive (0 : Fin 1) (0 : Fin 7)
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data field)] with location actual same selected
  change (seven.bulkUnit (0 : Fin 1) (0 : Fin 7)).physicalCurve 0 location mode =
    originalPhysicalComponentCurve parameters lower length positive bounded lengthPositive field 0 0 location mode
  rw [actual mode,pow_zero,one_smul,selected mode]
  have exactSlot := same mode 0
  simp only [ite_true] at exactSlot
  change _ = (sameCoupledPhysicalXSection parameters lower length positive bounded lengthPositive 0 field (radialClamp lower bounded.le location)) mode
  rw [sameCoupledPhysicalXSection_coefficient parameters lower length positive bounded lengthPositive field allGrades]
  exact exactSlot

theorem sharedCorrectedP_originalXCurve (compact : ℝ) (state : RetainedInverseState parameters length compact)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    (seven.correctedP parameters length compact lower positive bounded state).physicalCurve 0 radius mode =
      angularInverseMultiplier mode •
        originalPhysicalComponentCurve parameters lower length positive bounded lengthPositive field 0 0 radius mode := by
  rw [sharedCorrectedP_physicalCurve parameters length compact lower positive bounded state lengthPositive data field seven radius inside mode,
    sameSeven_originalXCurve parameters lower length positive bounded lengthPositive data field allGrades smooth seven radius inside mode]

end Grad.ActualPolarFlux
