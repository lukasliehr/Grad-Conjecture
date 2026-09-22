import AXF3RadialProfileBounds

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.FlatSourceProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.AxisJet
open Grad.NonlinearQuotientBounds Grad.QuotientProjection Grad.ChartAxisLift Grad.AxisCore

variable {parameters : PhaseParameters}

def valueCorrection : SmoothQuotient parameters →ₗ[ℂ] SmoothQuotient parameters :=
  LinearMap.pi ![radialValueInsertion.comp (traceZero.comp (LinearMap.proj 0)),
    radialValueInsertion.comp (traceZero.comp (LinearMap.proj 1)), 0, 0]

def radialAffineInsertion : AxisSmoothCore parameters 1 →ₗ[ℂ] SmoothQuotient parameters :=
  LinearMap.pi ![Complex.I • (radialFirstInsertion 0 + Complex.I • radialFirstInsertion 1),
    (-Complex.I) • (radialFirstInsertion 0 - Complex.I • radialFirstInsertion 1), 0, 0]

theorem firstMode_valueCorrection (source : SmoothQuotient parameters) :
    firstMode parameters (valueCorrection source) = 0 := by
  change (1 / 2 : ℂ) •
    (angularCore parameters 1 (radialValueInsertion (traceZero (source 0))) +
      reflection parameters (angularCore parameters (-1) (radialValueInsertion (traceZero (source 1))))) = 0
  rw [radialValueInsertion_mode, radialValueInsertion_mode]
  norm_num

theorem affineTrace_valueCorrection (source : SmoothQuotient parameters) :
    affineTrace parameters (valueCorrection source) = 0 := by
  change (4 * Complex.I)⁻¹ •
    ((traceFirst 0 (radialValueInsertion (traceZero (source 0))) -
      Complex.I • traceFirst 1 (radialValueInsertion (traceZero (source 0)))) -
    (traceFirst 0 (radialValueInsertion (traceZero (source 1))) +
      Complex.I • traceFirst 1 (radialValueInsertion (traceZero (source 1))))) = 0
  rw [traceFirst_radialValueInsertion, traceFirst_radialValueInsertion,
    traceFirst_radialValueInsertion, traceFirst_radialValueInsertion]
  simp

theorem affineTrace_radialAffineInsertion (data : AxisSmoothCore parameters 1) :
    affineTrace parameters (radialAffineInsertion data) = data := by
  change (4 * Complex.I)⁻¹ •
    ((traceFirst 0 (Complex.I • (radialFirstInsertion 0 data + Complex.I • radialFirstInsertion 1 data)) -
      Complex.I • traceFirst 1 (Complex.I • (radialFirstInsertion 0 data + Complex.I • radialFirstInsertion 1 data))) -
    (traceFirst 0 ((-Complex.I) • (radialFirstInsertion 0 data - Complex.I • radialFirstInsertion 1 data)) +
      Complex.I • traceFirst 1 ((-Complex.I) • (radialFirstInsertion 0 data - Complex.I • radialFirstInsertion 1 data)))) = data
  simp only [map_smul, map_add, map_sub, traceFirst_radialFirstInsertion]
  norm_num
  simp only [smul_add, smul_sub, smul_smul, Complex.I_mul_I]
  calc _ = -(Complex.I ^ 2) • data := by module
       _ = data := by simp

theorem coordinateJet_spin {dimension : ℕ} (field : ClosedJet dimension) (sign : ℝ) :
    coordinateJet 0 field + (Complex.I * (sign : ℂ)) • coordinateJet 1 field =
      coordinateMultiplyJet sign field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro component
  simp only [closedJet_value_add, closedJet_value_smul, ContinuousMap.add_apply,
    ContinuousMap.smul_apply, coordinateJet_value, coordinateMultiplyJet_value]
  change (point.val 0 : ℂ) * field.value point component +
    (Complex.I * (sign : ℂ)) * ((point.val 1 : ℂ) * field.value point component) =
    signedComplexCoordinate sign point.val * field.value point component
  simp only [signedComplexCoordinate]
  ring

theorem firstMode_radialAffineInsertion (data : AxisSmoothCore parameters 1) :
    firstMode parameters (radialAffineInsertion data) = 0 := by
  apply Subtype.ext
  funext cell
  let field := angularClosedJet 0 (profileJetZero cell (data.val cell))
  change (1 / 2 : ℂ) •
    (angularClosedJet 1 (Complex.I • (coordinateJet 0 field + Complex.I • coordinateJet 1 field)) +
      orthogonalJet cartesianReflectionEquiv
        (angularClosedJet (-1) ((-Complex.I) • (coordinateJet 0 field - Complex.I • coordinateJet 1 field)))) = 0
  have plus := coordinateJet_spin field 1
  have minus := coordinateJet_spin field (-1)
  simp only [Complex.ofReal_one, mul_one] at plus
  simp only [Complex.ofReal_neg, Complex.ofReal_one, mul_neg, mul_one,
    neg_smul, ← sub_eq_add_neg] at minus
  rw [plus, minus, angularClosedJet_smul, angularClosedJet_smul,
    angularClosedJet_z, angularClosedJet_zbar]
  norm_num only [Int.sub_self, neg_add_cancel]
  change (1 / 2 : ℂ) •
    (Complex.I • coordinateMultiplyJet 1 (angularClosedJet 0 field) +
      (orthogonalJetLinear 1 cartesianReflectionEquiv)
        ((-Complex.I) • coordinateMultiplyJet (-1) (angularClosedJet 0 field))) = 0
  rw [map_smul]
  change (1 / 2 : ℂ) •
    (Complex.I • coordinateMultiplyJet 1 (angularClosedJet 0 field) +
      (-Complex.I) • orthogonalJet cartesianReflectionEquiv
        (coordinateMultiplyJet (-1) (angularClosedJet 0 field))) = 0
  rw [reflection_coordinate_zbar, reflection_mean_jet, neg_smul, add_neg_cancel, smul_zero]

theorem modeProjection_radialAffineInsertion (data : AxisSmoothCore parameters 1) :
    modeProjection parameters (radialAffineInsertion data) = 0 := by
  rw [modeProjection_apply, firstMode_radialAffineInsertion, map_zero]
  funext coordinate
  fin_cases coordinate <;> rfl

theorem modeProjection_valueCorrection (source : SmoothQuotient parameters) :
    modeProjection parameters (valueCorrection source) = 0 := by
  rw [modeProjection_apply, firstMode_valueCorrection, map_zero]
  funext coordinate
  fin_cases coordinate <;> rfl

end Grad.FlatSourceProjection
