import AIP6SingleCellFourier

noncomputable section
open Set MeasureTheory

namespace Grad.InteriorPeriodization
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.DiskExtension.Operator Grad.FourierGrade Grad.COR12Extension

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private theorem normalizedSpatialIntegral (field : UnitAddCircle → ComplexEuclidean 1) :
    (∫ point : UnitAddCircle, field point) =
      ∫ point : SpatialCircle, field (spatialCircleToUnit point) ∂AddCircle.haarAddCircle := by
  change (∫ point : UnitAddCircle, field point ∂AddCircle.haarAddCircle) = _
  exact (MeasurePreserving.integral_comp'
    (f := spatialCircleToUnit.toMeasurableEquiv)
    spatialCircleToUnit_measurePreserving field).symm

theorem spatialHaar_integral_Ico {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : SpatialCircle → E) :
    (∫ point, field point ∂AddCircle.haarAddCircle) =
      (1 / 4 : ℝ) • ∫ coordinate in Ico (-2 : ℝ) 2, field (coordinate : SpatialCircle) := by
  rw [spatialHaar_integral, restrict_Ico_eq_restrict_Ioc]

def negativeDiskCharacter (firstMode secondMode : ℤ) (point : SpatialPlane) : ℂ :=
  fourier (-firstMode) (spatialCircleToUnit (point 0 : SpatialCircle)) *
    fourier (-secondMode) (spatialCircleToUnit (point 1 : SpatialCircle))

theorem negativeDiskCharacter_continuous (firstMode secondMode : ℤ) :
    Continuous (negativeDiskCharacter firstMode secondMode) := by
  unfold negativeDiskCharacter
  fun_prop

theorem normalizedSpatialPair (first second : ℝ) :
    ![spatialCircleToUnit (first : SpatialCircle), spatialCircleToUnit (second : SpatialCircle), (0 : UnitAddCircle)] =
      normalizedTorusPoint first second 0 := by
  simp [spatialCircleToUnit, normalizedTorusPoint, div_eq_mul_inv]

theorem spatialCoreCoefficient_box (field : ClosedJet 1)
    (supported : ∀ point : ClosedDisk, (3 / 4 : ℝ) < ‖point.val‖ → field.value point = 0)
    (firstMode secondMode : ℤ) :
    spatialCoreCoefficient field firstMode secondMode =
      (1 / 16 : ℝ) • ∫ second in Ico (-2 : ℝ) 2, ∫ first in Ico (-2 : ℝ) 2,
        negativeDiskCharacter firstMode secondMode (WithLp.toLp 2 ![first, second]) •
          closedDiskLift field.value (WithLp.toLp 2 ![first, second]) := by
  let integrand := fun first second : UnitAddCircle =>
    (fourier (-firstMode) first * fourier (-secondMode) second) • diskCoreTorus field ![first, second, 0]
  have firstChange (second : UnitAddCircle) :
      (∫ first : UnitAddCircle, integrand first second) =
        ∫ first : SpatialCircle, integrand (spatialCircleToUnit first) second ∂AddCircle.haarAddCircle := by
    exact normalizedSpatialIntegral (fun first => integrand first second)
  have secondChange :
      (∫ second : UnitAddCircle, ∫ first : SpatialCircle,
        integrand (spatialCircleToUnit first) second ∂AddCircle.haarAddCircle) =
      ∫ second : SpatialCircle, ∫ first : SpatialCircle,
        integrand (spatialCircleToUnit first) (spatialCircleToUnit second)
          ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle := by
    exact normalizedSpatialIntegral (fun second => ∫ first : SpatialCircle,
      integrand (spatialCircleToUnit first) second ∂AddCircle.haarAddCircle)
  change (∫ second : UnitAddCircle, ∫ first : UnitAddCircle, integrand first second) = _
  simp_rw [firstChange]
  rw [secondChange, spatialHaar_integral_Ico]
  simp_rw [spatialHaar_integral_Ico]
  rw [integral_smul, smul_smul]
  norm_num only [show (1 / 4 : ℝ) * (1 / 4) = 1 / 16 by norm_num]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ico] with second secondInside
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ico] with first firstInside
  have inside : WithLp.toLp 2 ![first, second] ∈ fundamentalHalfOpenSquare :=
    ⟨firstInside.1, firstInside.2, secondInside.1, secondInside.2⟩
  change (fourier (-firstMode) (spatialCircleToUnit (first : SpatialCircle)) *
      fourier (-secondMode) (spatialCircleToUnit (second : SpatialCircle))) •
    diskCoreTorus field ![spatialCircleToUnit (first : SpatialCircle), spatialCircleToUnit (second : SpatialCircle), 0] = _
  rw [normalizedSpatialPair]
  exact congrArg (fun value => negativeDiskCharacter firstMode secondMode (WithLp.toLp 2 ![first, second]) • value)
    (compact_diskCoreTorus_literal field supported (WithLp.toLp 2 ![first, second]) 0 inside)

end Grad.InteriorPeriodization
