import AKBD5SameScalarDirectionalFields

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

/-- Genuine radial product rule for the SAME unprojected corrected p. -/
theorem rawCorrectedP_radial (radius : ℝ) (inside : radius ∈ Ioo lower 1) (polar axial : ℝ) :
    scalarDirectionalField (rawCorrectedPCurves parameters length compact lower positive bounded state curves) bounded 0 (1,0,0) (radius,polar,axial) =
      scalarDirectionalField (polarCofactorFluxCurves parameters length compact lower positive bounded state curves 0) bounded 0 (1,0,0) (radius,polar,axial) +
      originalCofactorJetSeries parameters length compact state 1 0 1 0
        ⟨radius,⟨(positive.trans inside.1).le,inside.2.le⟩⟩ (polar,axial) * curves.fullField bounded (radius,polar,axial) 3 +
      originalCofactorSmoothEntry parameters length compact state 1 0 radius (polar,axial) *
        scalarDirectionalField curves bounded 3 (1,0,0) (radius,polar,axial) := by
  let m := polarCofactorFluxCurves parameters length compact lower positive bounded state curves 0
  let raw := rawCorrectedPCurves parameters length compact lower positive bounded state curves
  have kappa := originalCofactorSmoothEntry_radial parameters length compact state 1 0
    ⟨radius,⟨(positive.trans inside.1).le,inside.2.le⟩⟩ ⟨positive.trans inside.1,inside.2⟩ (polar,axial)
  have product := correctedRadialFlux_hasDerivAt
    (fun value => m.fullField bounded (value,polar,axial) 0)
    (fun value => originalCofactorSmoothEntry parameters length compact state 1 0 value (polar,axial))
    (fun value => curves.fullField bounded (value,polar,axial) 3) radius _ _ _
    (scalarRadial_hasDerivAt m bounded 0 radius inside polar axial) kappa
    (scalarRadial_hasDerivAt curves bounded 3 radius inside polar axial)
  have actual : HasDerivAt (fun value => raw.fullField bounded (value,polar,axial) 0)
      (scalarDirectionalField m bounded 0 (1,0,0) (radius,polar,axial) +
        originalCofactorJetSeries parameters length compact state 1 0 1 0
          ⟨radius,⟨(positive.trans inside.1).le,inside.2.le⟩⟩ (polar,axial) * curves.fullField bounded (radius,polar,axial) 3 +
        originalCofactorSmoothEntry parameters length compact state 1 0 radius (polar,axial) *
          scalarDirectionalField curves bounded 3 (1,0,0) (radius,polar,axial)) radius := by
    apply product.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds inside] with value member
    exact rawCorrectedP_same parameters length compact lower positive bounded state curves value ⟨member.1.le,member.2.le⟩ (polar,axial)
  exact (scalarRadial_hasDerivAt raw bounded 0 radius inside polar axial).unique actual

/-- Genuine axial product rule for the SAME corrected toroidal flux b3. -/
theorem bThree_axial (radius : ℝ) (inside : radius ∈ Ioo lower 1) (polar axial : ℝ) :
    scalarDirectionalField (curves.bThree parameters length compact lower positive bounded state) bounded 0 (0,0,1) (radius,polar,axial) =
      scalarDirectionalField (polarCofactorFluxCurves parameters length compact lower positive bounded state curves 2) bounded 0 (0,0,1) (radius,polar,axial) +
      originalCofactorJetSeries parameters length compact state 1 2 0 2
        ⟨radius,⟨(positive.trans inside.1).le,inside.2.le⟩⟩ (polar,axial) * curves.fullField bounded (radius,polar,axial) 3 +
      originalCofactorSmoothEntry parameters length compact state 1 2 radius (polar,axial) *
        scalarDirectionalField curves bounded 3 (0,0,1) (radius,polar,axial) := by
  let m := polarCofactorFluxCurves parameters length compact lower positive bounded state curves 2
  let b := curves.bThree parameters length compact lower positive bounded state
  have kappa := originalCofactorSmoothEntry_axial parameters length compact state 1 2
    ⟨radius,⟨(positive.trans inside.1).le,inside.2.le⟩⟩ polar axial
  have product := correctedRadialFlux_hasDerivAt
    (fun value => m.fullField bounded (radius,polar,value) 0)
    (fun value => originalCofactorSmoothEntry parameters length compact state 1 2 radius (polar,value))
    (fun value => curves.fullField bounded (radius,polar,value) 3) axial _ _ _
    (scalarAxial_hasDerivAt m bounded 0 radius inside polar axial) kappa
    (scalarAxial_hasDerivAt curves bounded 3 radius inside polar axial)
  have actual : HasDerivAt (fun value => b.fullField bounded (radius,polar,value) 0)
      (scalarDirectionalField m bounded 0 (0,0,1) (radius,polar,axial) +
        originalCofactorJetSeries parameters length compact state 1 2 0 2
          ⟨radius,⟨(positive.trans inside.1).le,inside.2.le⟩⟩ (polar,axial) * curves.fullField bounded (radius,polar,axial) 3 +
        originalCofactorSmoothEntry parameters length compact state 1 2 radius (polar,axial) *
          scalarDirectionalField curves bounded 3 (0,0,1) (radius,polar,axial)) axial := by
    apply product.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun value => bThree_same parameters length compact lower positive bounded state curves radius ⟨inside.1.le,inside.2.le⟩ (polar,value))
  exact (scalarAxial_hasDerivAt b bounded 0 radius inside polar axial).unique actual

end Grad.ActualDeterminantEquations
