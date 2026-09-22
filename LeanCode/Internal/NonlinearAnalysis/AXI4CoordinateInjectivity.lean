import AXI3CompletedCoreMap

noncomputable section

open MeasureTheory

namespace Grad.RawSourceFaithfulness

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.AxisSourceLift Grad.NonlinearProduct

variable {dimension : ℕ}

def zCompleted (parameters : PhaseParameters) :
    AGrade parameters dimension 0 →L[ℂ] AGrade parameters dimension 0 :=
  completeCoreMap parameters (zMulCore parameters) (2 * coordinateGradeConstant 0)
    (fun field => zMulCore_bound field 0)

def starZCompleted (parameters : PhaseParameters) :
    AGrade parameters dimension 0 →L[ℂ] AGrade parameters dimension 0 :=
  completeCoreMap parameters (starZMulCore parameters) (2 * coordinateGradeConstant 0)
    (fun field => starZMulCore_bound field 0)

theorem zCompleted_core (parameters : PhaseParameters) (field : ACore parameters dimension) :
    zCompleted parameters (aGradeEta parameters (GradeCore.ofCoreLinear field)) =
      aGradeEta parameters (GradeCore.ofCoreLinear (zMulCore parameters field)) :=
  completeCoreMap_core parameters _ _ _ field

theorem starZCompleted_core (parameters : PhaseParameters) (field : ACore parameters dimension) :
    starZCompleted parameters (aGradeEta parameters (GradeCore.ofCoreLinear field)) =
      aGradeEta parameters (GradeCore.ofCoreLinear (starZMulCore parameters field)) :=
  completeCoreMap_core parameters _ _ _ field

theorem starCoordinate_norm (point : SpatialPlane) :
    ‖signedComplexCoordinate (-1) point‖ = ‖point‖ := by
  have conjugate : signedComplexCoordinate (-1) point =
      star (signedComplexCoordinate 1 point) := by
    apply Complex.ext <;> simp [signedComplexCoordinate]
  rw [conjugate, norm_star, signedComplexCoordinate_one_norm]

theorem offAxis_ae : ∀ᵐ point : SpatialPlane ∂volume.restrict openUnitDisk, point ≠ 0 := by
  rw [ae_iff]
  simp

theorem zCompleted_injective (parameters : PhaseParameters) :
    Function.Injective (zCompleted (dimension := dimension) parameters) := by
  apply completeCoreMap_injective parameters (zMulCore parameters) (2 * coordinateGradeConstant 0)
    (fun field => zMulCore_bound field 0) (signedComplexCoordinate 1)
    (signedComplexCoordinate_smooth 1).continuous 1
  · intro point member
    rw [signedComplexCoordinate_one_norm]
    exact (show ‖point‖ < 1 from member).le
  · intro field cell point
    rw [zMulCore_jet, coordinateMultiplyJet_value]
  · filter_upwards [offAxis_ae] with point nonzero
    exact coordinate_ne_zero nonzero

theorem starZCompleted_injective (parameters : PhaseParameters) :
    Function.Injective (starZCompleted (dimension := dimension) parameters) := by
  apply completeCoreMap_injective parameters (starZMulCore parameters) (2 * coordinateGradeConstant 0)
    (fun field => starZMulCore_bound field 0) (signedComplexCoordinate (-1))
    (signedComplexCoordinate_smooth (-1)).continuous 1
  · intro point member
    rw [starCoordinate_norm]
    exact (show ‖point‖ < 1 from member).le
  · intro field cell point
    rw [starZMulCore_jet, coordinateMultiplyJet_value]
  · filter_upwards [offAxis_ae] with point nonzero
    exact starCoordinate_ne_zero nonzero

/-- Literal squared-radius multiplication on the full original completion.
Injectivity uses the measure-zero axis, never an unbounded inverse map. -/
def radiusSquaredCompleted (parameters : PhaseParameters) :
    AGrade parameters dimension 0 →L[ℂ] AGrade parameters dimension 0 :=
  (starZCompleted parameters).comp (zCompleted parameters)

theorem radiusSquaredCompleted_core (parameters : PhaseParameters) (field : ACore parameters dimension) :
    radiusSquaredCompleted parameters (aGradeEta parameters (GradeCore.ofCoreLinear field)) =
      aGradeEta parameters (GradeCore.ofCoreLinear (radiusSquaredCore parameters field)) := by
  unfold radiusSquaredCompleted
  rw [ContinuousLinearMap.comp_apply, zCompleted_core, starZCompleted_core]
  rfl

theorem radiusSquaredCompleted_injective (parameters : PhaseParameters) :
    Function.Injective (radiusSquaredCompleted (dimension := dimension) parameters) :=
  (starZCompleted_injective parameters).comp (zCompleted_injective parameters)

end Grad.RawSourceFaithfulness
