import AKBM6ActualCurveAngularDerivatives
import AKBD17SameDeterminantProductExpansion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ActualDeterminantEquations
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualBoundaryPrimitives Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.SourceCollar Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation Grad.ActualPolarFlux Grad.ActualCartesianEquations
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularSourceGraph
open Grad.AnnularGeneralSourceRegularity Grad.AnnularHighGenerators


variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0<lower) (bounded : lower<1) (state : RetainedInverseState parameters length compact)
    {row : DivisionRow 7 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

def originalPolarDivergence (radius : ℝ) (angles : ℝ×ℝ) : ℂ :=
  scalarDirectionalField (polarCofactorFluxCurves parameters length compact lower positive bounded state curves 0) bounded 0 (1,0,0) (radius,angles) +
  (polarCofactorFluxCurves parameters length compact lower positive bounded state curves 0).fullField bounded (radius,angles) 0 / (radius : ℂ) +
  scalarDirectionalField (polarCofactorFluxCurves parameters length compact lower positive bounded state curves 1) bounded 0 (0,1,0) (radius,angles) / (radius : ℂ) +
  scalarDirectionalField (polarCofactorFluxCurves parameters length compact lower positive bounded state curves 2) bounded 0 (0,0,1) (radius,angles) / (length : ℂ)

/-- Reuse the accepted finite AD13--AD17 identity with genuine smooth
curves and explicit angular rows; no solved-direction solution carrier is used. -/
theorem originalDeterminant_productExpansion (lengthNonzero : length≠0)
    (radius : ℝ) (inside : radius∈Ioo lower 1) (polar axial : ℝ)
    (first : scalarDirectionalField (curves.covariant parameters length compact lower positive bounded state.val)
      bounded 0 (0,1,0) (radius,polar,axial)=
      curves.fullField bounded (radius,polar,axial) 3+
      (radius:ℂ)*scalarDirectionalField curves bounded 3 (1,0,0) (radius,polar,axial)+
      removePolarMean (fun angles => ((curves.covariant parameters length compact lower positive bounded state.val).retainedForce
        parameters length compact lower positive bounded state).fullField bounded (radius,angles) 0) (polar,axial))
    (second : scalarDirectionalField (curves.covariant parameters length compact lower positive bounded state.val)
      bounded 1 (0,1,0) (radius,polar,axial)=
      scalarDirectionalField curves bounded 3 (0,1,0) (radius,polar,axial)+
      ((curves.covariant parameters length compact lower positive bounded state.val).forceZero
        parameters length compact lower positive bounded state).fullField bounded (radius,polar,axial) 0)
    (third : scalarDirectionalField (curves.covariant parameters length compact lower positive bounded state.val)
      bounded 2 (0,1,0) (radius,polar,axial)=
      (radius:ℂ)/(length:ℂ)*scalarDirectionalField curves bounded 3 (0,0,1) (radius,polar,axial)-
      removePolarMean (fun angles => (physicalForceCurves parameters length compact lower positive bounded state.val 1
        (curves.covariant parameters length compact lower positive bounded state.val)).fullField bounded (radius,angles) 0) (polar,axial))
    (angular : scalarDirectionalField curves bounded 3 (0,1,0) (radius,polar,axial)=curves.fullField bounded (radius,polar,axial) 1) :
    scalarDirectionalField (rawCorrectedPCurves parameters length compact lower positive bounded state curves) bounded 0 (1,0,0) (radius,polar,axial) +
      (rawCorrectedPCurves parameters length compact lower positive bounded state curves).fullField bounded (radius,polar,axial) 0 / (radius : ℂ) +
      scalarDirectionalField (curves.bThree parameters length compact lower positive bounded state) bounded 0 (0,0,1) (radius,polar,axial) / (length : ℂ) +
      retainedRVRawField parameters length compact lower positive bounded state curves radius (polar,axial) 0 / (radius : ℂ) =
    originalPolarDivergence parameters length compact lower positive bounded state curves radius (polar,axial) := by
  let covariant := curves.covariant parameters length compact lower positive bounded state.val
  have closed : radius∈Icc lower 1 := ⟨inside.1.le,inside.2.le⟩
  let point : RadialPoint := ⟨radius,⟨(positive.trans inside.1).le,inside.2.le⟩⟩
  have samePoint : collarRadius lower positive bounded.le radius=point :=
    Subtype.ext (collarRadius_literal lower positive bounded.le radius closed)
  have product := correctedFlux_sourceCancellation (radius : ℂ) (length : ℂ)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (positive.trans inside.1)))
    (Complex.ofReal_ne_zero.mpr lengthNonzero)
    ((polarCofactorFluxCurves parameters length compact lower positive bounded state curves 0).fullField bounded (radius,polar,axial) 0)
    (scalarDirectionalField (polarCofactorFluxCurves parameters length compact lower positive bounded state curves 0) bounded 0 (1,0,0) (radius,polar,axial))
    (scalarDirectionalField (polarCofactorFluxCurves parameters length compact lower positive bounded state curves 2) bounded 0 (0,0,1) (radius,polar,axial))
    (curves.fullField bounded (radius,polar,axial) 3)
    (scalarDirectionalField curves bounded 3 (1,0,0) (radius,polar,axial))
    (scalarDirectionalField curves bounded 3 (0,1,0) (radius,polar,axial))
    (scalarDirectionalField curves bounded 3 (0,0,1) (radius,polar,axial))
    (fun component => originalCofactorSmoothEntry parameters length compact state 1 component radius (polar,axial))
    (originalCofactorJetSeries parameters length compact state 1 0 1 0 point (polar,axial))
    (originalCofactorJetSeries parameters length compact state 1 2 0 2 point (polar,axial))
    (∑ component : Fin 3,originalCofactorJetSeries parameters length compact state 1 component 0 1 point (polar,axial) * covariant.fullField bounded (radius,polar,axial) component)
    ((covariant.forceZero parameters length compact lower positive bounded state).fullField bounded (radius,polar,axial) 0)
    (removePolarMean (fun angles => (covariant.retainedForce parameters length compact lower positive bounded state).fullField bounded (radius,angles) 0) (polar,axial))
    (removePolarMean (fun angles => (physicalForceCurves parameters length compact lower positive bounded state.val 1 covariant).fullField bounded (radius,angles) 0) (polar,axial))
    0 0 0
    (fun component => scalarDirectionalField covariant bounded component (0,1,0) (radius,polar,axial)) (by simpa only [sub_zero] using first)
      (by simpa only [sub_zero] using second) (by simpa only [add_zero] using third)
  rw [rawCorrectedP_radial parameters length compact lower positive bounded state curves radius inside polar axial,
    rawCorrectedP_same parameters length compact lower positive bounded state curves radius closed (polar,axial),
    bThree_axial parameters length compact lower positive bounded state curves radius inside polar axial,
    retainedRVRawField_scalar parameters length compact lower positive bounded state curves radius (polar,axial),
    sameKV_scalar parameters length compact lower positive bounded state covariant radius closed (polar,axial)]
  unfold originalPolarDivergence
  change _ = _ + _ + scalarDirectionalField (covariant.signedCofactorRow parameters length compact lower positive bounded state 1) bounded 0 (0,1,0) (radius,polar,axial) / (radius : ℂ) + _
  rw [signedCofactorFlux_polar parameters length compact lower positive bounded state covariant 1 radius inside polar axial,
    ← angular]
  simp only [samePoint,mul_zero,sub_zero,add_zero,zero_div,Fin.sum_univ_three] at product ⊢
  convert product using 1 <;> dsimp only [point,covariant] <;> ring

end Grad.OriginalKernelHomogeneousGraph
