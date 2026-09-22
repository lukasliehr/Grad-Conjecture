import AKBD3FullFieldProjectionDerivatives

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
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)

open Grad.ActualPolarFlux Grad.ActualCartesianEquations

variable {row : DivisionRow 7 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

/-- The existing exact unprojected corrected radial flux action. -/
def rawCorrectedPCurves :=
  curves.action parameters lower positive bounded
    (originalUnprojectedPKernel parameters length compact state)
    (originalUnprojectedPKernel_regular parameters length compact state)
    (originalUnprojectedPKernel_smooth parameters length compact lower positive bounded state)

/-- The SAME actual uncorrected signed polar flux m_i. -/
def polarCofactorFluxCurves (component : Fin 3) :=
  (curves.covariant parameters length compact lower positive bounded state.val).signedCofactorRow
    parameters length compact lower positive bounded state component

theorem rawCorrectedP_same (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (rawCorrectedPCurves parameters length compact lower positive bounded state curves).fullField bounded (radius,angles) 0 =
      (polarCofactorFluxCurves parameters length compact lower positive bounded state curves 0).fullField bounded (radius,angles) 0 +
      originalCofactorSmoothEntry parameters length compact state 1 0 radius angles * curves.fullField bounded (radius,angles) 3 := by
  have raw := congrArg (fun value : ComplexEuclidean 1 => value 0)
    (fullField_unprojectedP parameters length compact lower positive bounded state curves radius inside angles)
  have coefficient := originalCofactorSmoothEntry_literal parameters length compact state 1 0
    ⟨radius,⟨positive.le.trans inside.1,inside.2⟩⟩ angles
  dsimp only at coefficient
  rw [coefficient,polarCofactorFluxCurves,fullField_signedCofactorRow parameters length compact lower positive bounded state _
    (curves.covariant parameters length compact lower positive bounded state.val) radius inside angles]
  simpa [rawCorrectedPCurves,Fin.sum_univ_three,PiLp.add_apply,PiLp.smul_apply,matrixUnit_apply,operatorBasis] using raw

theorem bThree_same (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.bThree parameters length compact lower positive bounded state).fullField bounded (radius,angles) 0 =
      (polarCofactorFluxCurves parameters length compact lower positive bounded state curves 2).fullField bounded (radius,angles) 0 +
      originalCofactorSmoothEntry parameters length compact state 1 2 radius angles * curves.fullField bounded (radius,angles) 3 := by
  have coefficient := originalCofactorSmoothEntry_literal parameters length compact state 1 2
    ⟨radius,⟨positive.le.trans inside.1,inside.2⟩⟩ angles
  dsimp only at coefficient
  rw [coefficient,polarCofactorFluxCurves,fullField_signedCofactorRow parameters length compact lower positive bounded state _
    (curves.covariant parameters length compact lower positive bounded state.val) radius inside angles]
  exact fullField_originalBThree parameters length compact lower positive bounded state curves radius inside angles

/-- The genuine corrected p retains its outer P; it is not identified with
its unprojected flux, which can have a nonzero angular mean. -/
theorem correctedP_projection_same (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.correctedP parameters length compact lower positive bounded state).fullField bounded (radius,angles) 0 =
      removePolarMean (fun query =>
        (rawCorrectedPCurves parameters length compact lower positive bounded state curves).fullField bounded (radius,query) 0) angles := by
  let raw := rawCorrectedPCurves parameters length compact lower positive bounded state curves
  have rawSame := funext (fun query => fullField_unprojectedP parameters length compact lower positive bounded state curves radius inside query)
  have projected := fullField_originalCorrectedP parameters length compact lower positive bounded state curves radius inside angles
  rw [← rawSame] at projected
  have coordinate := congrArg (fun value : ComplexEuclidean 1 => value 0) projected
  change (curves.correctedP parameters length compact lower positive bounded state).fullField bounded (radius,angles) 0 =
    (removePolarMean (fun query => raw.fullField bounded (radius,query)) angles) 0 at coordinate
  rw [removePolarMean_coordinate (fun query => raw.fullField bounded (radius,query))
    (raw.fullField_continuous_angles bounded radius inside) angles] at coordinate
  exact coordinate

end Grad.ActualDeterminantEquations
