import AIP5ActualTorusField

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Grad.InteriorPeriodization
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.DiskExtension.Operator Grad.FourierGrade Grad.COR12Extension

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem compact_diskCoreTorus_cell (field : ClosedJet 1)
    (supported : ∀ point : ClosedDisk, (3 / 4 : ℝ) < ‖point.val‖ → field.value point = 0)
    (first second cell : UnitAddCircle) :
    diskCoreTorus field ![first, second, cell] = diskCoreTorus field ![first, second, 0] := by
  change ambientExtensionFromValue (constantDiskCellJet field).value
      (spatialTorusRepresentative (spatialCircleToUnit.symm first, spatialCircleToUnit.symm second))
      (cellCircleToUnit.symm cell) =
    ambientExtensionFromValue (constantDiskCellJet field).value
      (spatialTorusRepresentative (spatialCircleToUnit.symm first, spatialCircleToUnit.symm second))
      (cellCircleToUnit.symm 0)
  rw [compact_ambientExtension_literal field supported, compact_ambientExtension_literal field supported]

theorem negativeTorusCharacter_three (mode : FourierMode) (first second cell : UnitAddCircle) :
    UnitAddTorus.mFourier (-(modeVector mode)) ![first, second, cell] =
      fourier (-mode.2.2) cell * (fourier (-mode.1) first * fourier (-mode.2.1) second) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, modeVector, Pi.neg_apply,
    Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue,
    Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton]
  ring

theorem unit_fourier_integral (mode : ℤ) :
    (∫ point : UnitAddCircle, fourier (-mode) point) = if mode = 0 then 1 else 0 := by
  have coefficient := congrFun (fourierCoeff_fourier (T := 1) 0) mode
  change (∫ point : UnitAddCircle, fourier (-mode) point ∂AddCircle.haarAddCircle) = _
  change (∫ point : UnitAddCircle, fourier (-mode) point • fourier 0 point
    ∂AddCircle.haarAddCircle) = (Pi.single 0 (1 : ℂ) : ℤ → ℂ) mode at coefficient
  simpa only [fourier_zero, Pi.one_apply, smul_eq_mul, mul_one, Pi.single_apply] using coefficient

def spatialCoreCoefficient (field : ClosedJet 1) (firstMode secondMode : ℤ) : ComplexEuclidean 1 :=
  ∫ second : UnitAddCircle, ∫ first : UnitAddCircle,
    (fourier (-firstMode) first * fourier (-secondMode) second) • diskCoreTorus field ![first, second, 0]

/-- The actual periodized compact disk field has precisely cell zero;
all other cell coefficients vanish by normalized Haar orthogonality. -/
theorem diskFourier_compact_single_cell (parameters : PhaseParameters) (field : ClosedJet 1)
    (supported : ∀ point : ClosedDisk, (3 / 4 : ℝ) < ‖point.val‖ → field.value point = 0)
    (mode : FourierMode) :
    coefficient 0 (diskFourier parameters (closedL2Core field)) mode =
      if mode.2.2 = 0 then spatialCoreCoefficient field mode.1 mode.2.1 else 0 := by
  rw [diskFourier_core_coefficient]
  let integrand : C(ProductTorus, ComplexEuclidean 1) :=
    ⟨fun point => UnitAddTorus.mFourier (-(modeVector mode)) point • diskCoreTorus field point,
      (UnitAddTorus.mFourier _).continuous.smul (diskCoreTorus field).continuous⟩
  change (∫ point : ProductTorus, integrand point) = _
  rw [productTorus_integral_three_vector]
  have factor (first second cell : UnitAddCircle) :
      integrand ![first, second, cell] = fourier (-mode.2.2) cell •
        ((fourier (-mode.1) first * fourier (-mode.2.1) second) • diskCoreTorus field ![first, second, 0]) := by
    change UnitAddTorus.mFourier (-(modeVector mode)) ![first, second, cell] •
      diskCoreTorus field ![first, second, cell] = _
    rw [negativeTorusCharacter_three, compact_diskCoreTorus_cell field supported, mul_smul]
  simp_rw [factor, integral_smul]
  rw [integral_smul_const, unit_fourier_integral]
  by_cases zero : mode.2.2 = 0
  · simp only [if_pos zero, one_smul]
    rfl
  · simp only [if_neg zero, zero_smul]

end Grad.InteriorPeriodization
