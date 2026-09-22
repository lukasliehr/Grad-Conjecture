import AKBM12ActualSmoothForceTraceAlgebra
import AKBM10SameScalarSlotDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ActualCartesianEquations Grad.ActualDeterminantEquations
open Grad.ActualPolarEquations Grad.AnnularCurrentLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.SourceCollarFullSource Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.OriginalKernelGraphRestriction Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelRetainedDecay
open Grad.AnnularPhysicalReconstruction Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 8≤originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (total vector : ACore parameters 3) (scalar : ACore parameters 1)


theorem originalKernelSevenSlot_negative (slot : Fin 7) (radius : Icc lower (1:ℝ)) :
    originalCurveNegativeTrace
      ((originalKernelSevenCurves parameters length rho epsilon base small lower positive bounded total vector scalar).bulkUnit (0:Fin 1) slot) radius=
    tupleNormalizedInput parameters lower positive
      (originalKernelSmoothTuple parameters length rho epsilon base small lower positive bounded total vector scalar) radius slot := by
  rw [originalCurveNegativeTrace_bulkUnit,originalKernelSevenCurves_negative]
  exact sevenInputSlotKernel_flatten _ 0 0 _ slot

theorem originalKernelSevenCovariant_scalarAngular (compact : ℝ) (state : RetainedInverseState parameters length compact)
    (component : Fin 3) (radius : ℝ) (inside : radius∈Ioo lower 1) (polar axial : ℝ) :
    scalarDirectionalField
      ((originalKernelSevenCurves parameters length rho epsilon base small lower positive bounded total vector scalar).covariant
        parameters length compact lower positive bounded state.val) bounded component (0,1,0) (radius,polar,axial)=
      ((originalKernelSevenCurves parameters length rho epsilon base small lower positive bounded total vector scalar).rotatedCovariant
        parameters length compact lower positive bounded state.val).fullField bounded (radius,polar,axial) component := by
  have derivative := ((PiLp.proj (𝕜:=ℂ) 2 (fun _ : Fin 3 => ℂ) component).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt polar
    (originalKernelSevenCurves_covariantAngular parameters length rho epsilon base small lower positive bounded total vector scalar compact state
      radius ⟨inside.1.le,inside.2.le⟩ polar axial)
  exact (scalarPolar_hasDerivAt _ bounded component radius inside polar axial).unique derivative

end Grad.OriginalKernelHomogeneousGraph
