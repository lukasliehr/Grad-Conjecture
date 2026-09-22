import AKBM22ActualRadialFourierConverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ActualCartesianEquations
open Grad.ActualPolarEquations Grad.ActualPolarFlux Grad.ActualDeterminantEquations Grad.AnnularCurrentLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.SourceCollarFullSource Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.OriginalKernelGraphRestriction Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelRetainedDecay
open Grad.AnnularPhysicalReconstruction Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

/-- The exact axial curve followed by P realizes the projected genuine
axial derivative, at the same physical radius and angles. -/
theorem originalProjectedAxial_fullField {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {row : DivisionRow 1 lower} (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower<1)
    (radius : ℝ) (inside : radius∈Ioo lower 1) (angles : ℝ×ℝ) :
    removePolarMean (fun query => scalarDirectionalField curves bounded 0 (0,0,1) (radius,query)) angles=
      (originalDifferentiatedCurves curves bounded true).2.meanFree.fullField bounded (radius,angles) 0 := by
  let derivative := (originalDifferentiatedCurves curves bounded true).2
  have closed : radius∈Icc lower 1 := ⟨inside.1.le,inside.2.le⟩
  have same (query : ℝ×ℝ) : scalarDirectionalField curves bounded 0 (0,0,1) (radius,query)=
      derivative.fullField bounded (radius,query) 0 := by
    have given := ((PiLp.proj (𝕜:=ℂ) 2 (fun _ : Fin 1 => ℂ) 0).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt query.2
      (originalDifferentiatedCurves_axial curves bounded radius closed query.1 query.2)
    exact (scalarAxial_hasDerivAt curves bounded 0 radius inside query.1 query.2).unique given
  rw [funext same,SmoothLowPhysicalRow.fullField_meanFree _ bounded radius closed angles,
    removePolarMean_coordinate _ (derivative.fullField_continuous_angles bounded radius closed) angles]

/-- Exact original negative traces of the same differentiated and projected
curve; the original axial multiplier and angular P retain their order. -/
theorem originalProjectedAxial_coefficient {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {row : DivisionRow 1 lower} (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower<1)
    (radius : Icc lower (1:ℝ)) (mode : ℤ×ℤ) :
    (originalDifferentiatedCurves curves bounded true).2.meanFree.physicalCurve 0 radius.val mode=
      (Complex.I*(mode.2:ℂ)) • (angularMeanFreeMultiplier mode • negativeTraceCoefficient _ 0 0
        (originalCurveNegativeTrace curves radius) mode) := by
  rw [← SmoothLowPhysicalRow.fullField_doubleCoefficient _ bounded radius.val radius.property mode,
    ← originalCurveNegativeTrace_coefficient _ bounded radius mode,originalCurveNegativeTrace_meanFree,
    forceMeanFreeTrace,angularMeanFreeKernel,scalarModeDiagonalKernel_action_coefficient,
    originalDifferentiatedCurves_negativeAxial,originalCurveNegativeAxial_coefficient curves bounded radius mode]
  exact smul_comm _ _ _

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 8≤originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (total vector : ACore parameters 3) (scalar : ACore parameters 1)

/-- Literal b3 trace of the actual original seven packet. -/
theorem originalKernelSevenCurves_bThree (compact : ℝ) (state : RetainedInverseState parameters length compact)
    (radius : Icc lower (1:ℝ)) :
    originalCurveNegativeTrace
      ((originalKernelSevenCurves parameters length rho epsilon base small lower positive bounded total vector scalar).bThree
        parameters length compact lower positive bounded state) radius=
      tupleBThreeTrace parameters length compact lower positive state
        (originalKernelSmoothTuple parameters length rho epsilon base small lower positive bounded total vector scalar) radius := by
  have action := originalCurveNegativeTrace_action parameters lower positive bounded
    (radialNormalizedBThreeKernel parameters length compact state)
    (originalBThreeKernel_regular parameters length compact state)
    (originalBThreeKernel_smooth parameters length compact lower positive bounded state)
    (originalKernelSevenCurves parameters length rho epsilon base small lower positive bounded total vector scalar) radius
  change originalCurveNegativeTrace
    ((originalKernelSevenCurves parameters length rho epsilon base small lower positive bounded total vector scalar).bThree
      parameters length compact lower positive bounded state) radius=_ at action
  rw [action,originalKernelSevenCurves_negative,tupleBThreeTrace_normalized]

end Grad.OriginalKernelHomogeneousGraph
