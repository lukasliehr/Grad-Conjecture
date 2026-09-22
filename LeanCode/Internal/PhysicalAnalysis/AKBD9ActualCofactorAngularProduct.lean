import AKBD7SameProjectedRadialFluxDerivative
import AKBD8ProjectedDeterminantResidual

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

variable {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

theorem cofactorSmoothEntry_continuous_angles (cofactorRow component : Fin 3) (r : RadialPoint) :
    Continuous (originalCofactorSmoothEntry parameters length compact state cofactorRow component r.val) := by
  rw [funext (originalCofactorSmoothEntry_series parameters length compact state cofactorRow component r)]
  exact (originalCofactorJetSeries_continuous parameters length compact state cofactorRow component 0 0 r).sub continuous_const

/-- Genuine angular product rule for each actual signed cofactor flux row,
using the accepted coefficient angular jets and the SAME covariant field. -/
theorem signedCofactorFlux_polar (cofactorRow : Fin 3) (radius : ℝ)
    (inside : radius ∈ Ioo lower 1) (polar axial : ℝ) :
    scalarDirectionalField (curves.signedCofactorRow parameters length compact lower positive bounded state cofactorRow)
      bounded 0 (0,1,0) (radius,polar,axial) =
      (∑ component : Fin 3, originalCofactorJetSeries parameters length compact state cofactorRow component 0 1
        ⟨radius,⟨(positive.trans inside.1).le,inside.2.le⟩⟩ (polar,axial) * curves.fullField bounded (radius,polar,axial) component) +
      ∑ component : Fin 3, originalCofactorSmoothEntry parameters length compact state cofactorRow component radius (polar,axial) *
        scalarDirectionalField curves bounded component (0,1,0) (radius,polar,axial) := by
  let flux := curves.signedCofactorRow parameters length compact lower positive bounded state cofactorRow
  let point : RadialPoint := ⟨radius,⟨(positive.trans inside.1).le,inside.2.le⟩⟩
  have product (component : Fin 3) :=
    (originalCofactorSmoothEntry_angular parameters length compact state cofactorRow component point polar axial).fun_mul
      (scalarPolar_hasDerivAt curves bounded component radius inside polar axial)
  have summed := HasDerivAt.fun_sum (u := Finset.univ) (fun component _ => product component)
  have equal (angle : ℝ) : flux.fullField bounded (radius,angle,axial) 0 =
      ∑ component : Fin 3,originalCofactorSmoothEntry parameters length compact state cofactorRow component radius (angle,axial) *
        curves.fullField bounded (radius,angle,axial) component := by
    rw [fullField_signedCofactorRow parameters length compact lower positive bounded state cofactorRow curves radius
      ⟨inside.1.le,inside.2.le⟩ (angle,axial)]
    apply Finset.sum_congr rfl
    intro component _
    rw [originalCofactorSmoothEntry_literal parameters length compact state cofactorRow component point (angle,axial)]
  have actual := summed.congr_of_eventuallyEq (Filter.Eventually.of_forall equal)
  have unique := (scalarPolar_hasDerivAt flux bounded 0 radius inside polar axial).unique actual
  simpa only [Finset.sum_add_distrib] using unique

end Grad.ActualDeterminantEquations
