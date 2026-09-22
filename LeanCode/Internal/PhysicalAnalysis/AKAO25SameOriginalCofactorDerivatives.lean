import AKAO24SameRadialScalarAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualPolarFlux
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualBoundaryPrimitives Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.SourceCollar Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact : ℝ)
    (state : RetainedInverseState parameters length compact) (row component : Fin 3)

/-- A total radial extension of the SAME original signed polar cofactor entry. -/
def originalCofactorSmoothEntry (radius : ℝ) (angles : ℝ × ℝ) : ℂ :=
  polarRadialScalarSeries parameters (originalCofactorDeviation parameters length state.val.val.epsilon state.val.val.field)
    (originalCofactorDeviation_coherent parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low)
    row component 0 radius angles - if row=component then 1 else 0

theorem originalCofactorSmoothEntry_series (r : RadialPoint) (angles : ℝ × ℝ) :
    originalCofactorSmoothEntry parameters length compact state row component r.val angles =
      originalCofactorJetSeries parameters length compact state row component 0 0 r angles - if row=component then 1 else 0 := by
  rw [originalCofactorJetSeries_radial parameters length compact state row component 0 r angles]
  rfl

/-- Pointwise equality with the original physical signed cofactor; this is not an assumed extension. -/
theorem originalCofactorSmoothEntry_literal (r : RadialPoint) (angles : ℝ × ℝ) :
    originalCofactorSmoothEntry parameters length compact state row component r.val angles =
      originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field row angles.2 angles.1
        (polarClosedPoint r.val angles.1 r.property.1 r.property.2) component := by
  rw [originalCofactorSmoothEntry_series parameters length compact state row component r angles,
    originalCofactorJetSeries_literal parameters length compact state row component r angles]
  exact add_sub_cancel_right _ _

/-- The radial kernel jet is the genuine radial derivative of that same coefficient. -/
theorem originalCofactorSmoothEntry_radial (r : RadialPoint) (interior : r.val ∈ Ioo 0 1) (angles : ℝ × ℝ) :
    HasDerivAt (fun radius => originalCofactorSmoothEntry parameters length compact state row component radius angles)
      (originalCofactorJetSeries parameters length compact state row component 1 0 r angles) r.val := by
  have derivative := (polarRadialScalarSeries_hasDerivAt parameters
    (originalCofactorDeviation parameters length state.val.val.epsilon state.val.val.field)
    (originalCofactorDeviation_coherent parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low)
    row component 0 r.val interior angles).sub_const (if row=component then (1 : ℂ) else 0)
  rw [originalCofactorJetSeries_radial parameters length compact state row component 1 r angles]
  exact derivative

/-- The angular kernel jet is the genuine R derivative of that same coefficient. -/
theorem originalCofactorSmoothEntry_angular (r : RadialPoint) (polar axial : ℝ) :
    HasDerivAt (fun angle => originalCofactorSmoothEntry parameters length compact state row component r.val (angle,axial))
      (originalCofactorJetSeries parameters length compact state row component 0 1 r (polar,axial)) polar := by
  have derivative := (originalCofactorJetSeries_angular parameters length compact state row component 0 r polar axial).sub_const
    (if row=component then (1 : ℂ) else 0)
  simpa only [← funext (fun angle => originalCofactorSmoothEntry_series parameters length compact state row component r (angle,axial))] using derivative

/-- The axial kernel jet is the genuine axial derivative of that same coefficient. -/
theorem originalCofactorSmoothEntry_axial (r : RadialPoint) (polar axial : ℝ) :
    HasDerivAt (fun angle => originalCofactorSmoothEntry parameters length compact state row component r.val (polar,angle))
      (originalCofactorJetSeries parameters length compact state row component 0 2 r (polar,axial)) axial := by
  have derivative := (originalCofactorJetSeries_axial parameters length compact state row component 0 r polar axial).sub_const
    (if row=component then (1 : ℂ) else 0)
  simpa only [← funext (fun angle => originalCofactorSmoothEntry_series parameters length compact state row component r (polar,angle))] using derivative

end Grad.ActualPolarFlux
