import AKAO22SameDiagonalCofactor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualPolarFlux
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.AnnularPhysicalReconstruction Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualBoundaryPrimitives Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.SourceCollar Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    {row : DivisionRow 1 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

theorem fullField_action_meanFree (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.action parameters lower positive bounded
      (fun r => angularMeanFreeKernel (radialKernelParameters parameters r) 1)
      (scalarModeRadialKernel_regular parameters _ _ _ _)
      (smoothConjugatedFamily_fixed parameters lower positive bounded
        (fun p => angularMeanFreeKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _))).fullField bounded (radius,angles) =
      removePolarMean (fun query => curves.fullField bounded (radius,query)) angles := by
  let kernel := fun r : RadialPoint => angularMeanFreeKernel (radialKernelParameters parameters r) 1
  have regular : RegularKernelFamily kernel := scalarModeRadialKernel_regular parameters _ _ _ _
  have smooth : SmoothConjugatedFamily parameters lower positive bounded.le kernel :=
    smoothConjugatedFamily_fixed parameters lower positive bounded
      (fun p => angularMeanFreeKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  have same := samePhysical_fullField_eq (curves.action parameters lower positive bounded kernel regular smooth)
    curves.meanFree bounded (by
      filter_upwards [originalPhysicalSlice_action parameters lower positive bounded.le kernel regular row,
        originalPhysicalSlice_coefficient parameters lower positive bounded.le row,
        originalPhysicalSlice_coefficient parameters lower positive bounded.le
          (regularRadialBulkAction parameters 0 lower positive bounded.le kernel regular row),
        curves.physicalCurve_actual bounded 0,curves.meanFree.physicalCurve_actual bounded 0,
        ae_restrict_mem measurableSet_Icc]
          with location action inputCoefficient outputCoefficient inputActual targetActual member
      intro mode
      simp only [pow_zero,one_smul] at inputActual targetActual
      rw [← outputCoefficient mode,action]
      simp only [kernel,angularMeanFreeKernel,scalarModeDiagonalKernel_action_coefficient]
      rw [inputCoefficient mode,← inputActual mode,← targetActual mode,
        physicalCurve_meanFree curves bounded location member mode]
      by_cases zero : mode.1=0 <;> simp [angularMeanFreeMultiplier,zero]) radius inside angles
  rw [curves.fullField_meanFree bounded radius inside angles] at same
  exact same

end Grad.ActualPolarFlux
