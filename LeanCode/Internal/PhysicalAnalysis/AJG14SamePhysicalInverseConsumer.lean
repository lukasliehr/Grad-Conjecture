import AJG13SameInverseUniformReconstruction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace Grad.AnnularPhysicalReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularReconstruction
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.AnnularCurrentLow Grad.GaugeCoefficients.Physical.Allocation

/-- Exact original seven-slot physical coefficients, with the source supplied
once and all analytic/radial weights cancelled literally. -/
theorem sharedFull_inputFidelity (parameters : PhaseParameters) (L lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < L)
    (data : StrongDataCarrier parameters lower positive bounded 0 0)
    (solution : CoupledSpace lower L positive lengthPositive) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode slot,
      negativeTraceCoefficient (radialKernelParameters parameters (collarRadius lower positive bounded radius)) 0 0
        (physicalBulkSevenTrace parameters lower positive (collarRadius lower positive bounded radius)
          (collectRadial lower (fullStrongSevenInput parameters L lower lengthPositive positive bounded data solution) radius) slot) mode 0 =
      lowRhoPhysicalCoefficient parameters lower positive
        (fullStrongSevenInput parameters L lower lengthPositive positive bounded data solution) radius mode slot := by
  filter_upwards [collectRadial_ae lower (fullStrongSevenInput parameters L lower lengthPositive positive bounded data solution),
    ae_restrict_mem measurableSet_Icc] with radius collected inside
  intro mode slot
  rw [physicalBulkSevenTrace_coefficient, collected mode, collarRadius_literal lower positive bounded radius inside]
  rfl

/-- Public consumer: the SAME shared-source inverse satisfies the original
force/gauge/flux reconstruction. No compatibility premise is supplied by the
caller and neither the original B8 ball nor either analytic width is changed. -/
theorem sameSharedInverse_physicalLaws (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters L compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0) :
    let bounded : lower ≤ 1 := lowerHalf.trans (by norm_num)
    let solution := sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      let radial := collarRadius lower positive bounded radius
      let input := physicalBulkSevenTrace parameters lower positive radial
        (collectRadial lower (fullStrongSevenInput parameters L lower lengthPositive positive bounded data solution) radius)
      let covariant := originalPhysicalSlice parameters lower positive bounded
        (sharedFullCovariant parameters L compact lower positive bounded lengthPositive state.val data solution) radius
      let rotated := originalPhysicalSlice parameters lower positive bounded
        (sharedFullRotatedCovariant parameters L compact lower positive bounded lengthPositive state.val data solution) radius
      OriginalSliceLaws parameters L compact state.val radial input covariant rotated ∧
        radialCorrectedFluxTrace parameters L compact state.val.val radial 0 0 covariant (input 3) =
          physicalBulkFlux parameters lower positive radial
            (collectRadial lower (fullStrongSevenInput parameters L lower lengthPositive positive bounded data solution) radius) := by
  dsimp only
  exact (sharedFull_originalSliceLaws parameters L compact lower positive (lowerHalf.trans (by norm_num)) lengthPositive state.val data
    (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)).and
    (sharedFull_originalCorrectedFlux parameters L compact lower positive (lowerHalf.trans (by norm_num)) lengthPositive state.val data
      (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data))

end Grad.AnnularPhysicalReconstruction
