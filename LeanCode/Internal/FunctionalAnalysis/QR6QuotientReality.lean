import QR5JetReality
import QP9Consumer

noncomputable section

open scoped ComplexConjugate

namespace Grad.CompletedReality

open Grad.ClosedJets Grad.CartesianState Grad.AxisCore Grad.Constraints Grad.AxisJet
open Grad.QuotientProjection

theorem reflection_conjugate (parameters : PhaseParameters) (field : ACore parameters 1) :
    cartesianCoreConjugation parameters (reflection parameters field) =
      reflection parameters (cartesianCoreConjugation parameters field) :=
  orthogonalCore_conjugate parameters _ field

theorem firstMode_conjugate (parameters : PhaseParameters) (field : SmoothQuotient parameters) :
    firstMode parameters (zCoreConjugation parameters field) =
      cartesianCoreConjugation parameters (reflection parameters (firstMode parameters field)) := by
  rw [reflection_conjugate, firstMode_apply, firstMode_apply,
    coreConjugation_complex_smul, map_add, reflection_conjugate,
    angularCore_conjugate, angularCore_conjugate, map_smul, map_add, reflection_involutive]
  simp only [zCoreConjugation, LinearMap.coe_mk, AddHom.coe_mk, spinSwap,
    Equiv.swap_apply_left, Equiv.swap_apply_right, neg_neg]
  norm_num [map_div₀, map_ofNat]
  rw [add_comm]

theorem modeProjection_conjugate (parameters : PhaseParameters) (field : SmoothQuotient parameters) :
    modeProjection parameters (zCoreConjugation parameters field) =
      zCoreConjugation parameters (modeProjection parameters field) := by
  rw [modeProjection_apply, firstMode_conjugate, modeProjection_apply]
  funext coordinate
  fin_cases coordinate
  · rfl
  · change reflection parameters (cartesianCoreConjugation parameters
        (reflection parameters (firstMode parameters field))) =
      cartesianCoreConjugation parameters (firstMode parameters field)
    rw [reflection_conjugate, reflection_involutive]
  · exact (map_zero (cartesianCoreConjugation parameters)).symm
  · exact (map_zero (cartesianCoreConjugation parameters)).symm

theorem removeMean_conjugate (parameters : PhaseParameters) (field : SmoothQuotient parameters)
    (coordinate : Fin 4) (fixed : spinSwap coordinate = coordinate) :
    removeMean parameters coordinate (zCoreConjugation parameters field) =
      zCoreConjugation parameters (removeMean parameters coordinate field) := by
  funext index
  have equals : spinSwap index = coordinate ↔ index = coordinate := by
    constructor
    · intro equality
      have := congrArg spinSwap equality
      simpa only [spinSwap_involutive, fixed] using this
    · rintro rfl
      exact fixed
  simp only [removeMean, zCoreConjugation, LinearMap.pi_apply, LinearMap.coe_mk,
    AddHom.coe_mk]
  by_cases same : index = coordinate
  · simp only [if_pos same, if_pos (equals.mpr same)]
    change cartesianCoreConjugation parameters (field (spinSwap index)) -
      angularCore parameters 0 (cartesianCoreConjugation parameters (field (spinSwap index))) =
      cartesianCoreConjugation parameters
        (field (spinSwap index) - angularCore parameters 0 (field (spinSwap index)))
    rw [map_sub, angularCore_conjugate, neg_zero]
  · simp only [if_neg same, if_neg (not_congr equals |>.mpr same)]
    rfl

theorem affineTrace_conjugate (parameters : PhaseParameters) (field : SmoothQuotient parameters) :
    affineTrace parameters (zCoreConjugation parameters field) =
      axisCoreInvolution parameters 1 (affineTrace parameters field) := by
  change (4 * Complex.I)⁻¹ •
    ((traceFirst 0 (cartesianCoreConjugation parameters (field 1)) -
        Complex.I • traceFirst 1 (cartesianCoreConjugation parameters (field 1))) -
      (traceFirst 0 (cartesianCoreConjugation parameters (field 0)) +
        Complex.I • traceFirst 1 (cartesianCoreConjugation parameters (field 0)))) =
    axisCoreInvolution parameters 1 ((4 * Complex.I)⁻¹ •
      ((traceFirst 0 (field 0) - Complex.I • traceFirst 1 (field 0)) -
        (traceFirst 0 (field 1) + Complex.I • traceFirst 1 (field 1))))
  simp only [traceFirst_conjugate, axisCoreInvolution_smul,
    axisCoreInvolution_sub, axisCoreInvolution_add]
  norm_num [map_ofNat]
  module

theorem affineInsertion_conjugate (parameters : PhaseParameters)
    (family : AxisSmoothCore parameters 1) :
    zCoreConjugation parameters (affineInsertion parameters family) =
      affineInsertion parameters (axisCoreInvolution parameters 1 family) := by
  funext coordinate
  fin_cases coordinate
  · change cartesianCoreConjugation parameters
        ((-Complex.I) • (insertOne 0 family - Complex.I • insertOne 1 family)) =
      Complex.I • (insertOne 0 (axisCoreInvolution parameters 1 family) +
        Complex.I • insertOne 1 (axisCoreInvolution parameters 1 family))
    simp only [coreConjugation_complex_smul, map_sub, insertOne_conjugate]
    norm_num
    module
  · change cartesianCoreConjugation parameters
        (Complex.I • (insertOne 0 family + Complex.I • insertOne 1 family)) =
      (-Complex.I) • (insertOne 0 (axisCoreInvolution parameters 1 family) -
        Complex.I • insertOne 1 (axisCoreInvolution parameters 1 family))
    simp only [coreConjugation_complex_smul, map_add, insertOne_conjugate]
    norm_num
    module
  · exact map_zero (cartesianCoreConjugation parameters)
  · exact map_zero (cartesianCoreConjugation parameters)

/-- Literal N38/N39 factor-by-factor commutation on the smooth fourfold core. -/
theorem quotientProjection_conjugate (parameters : PhaseParameters) (field : SmoothQuotient parameters) :
    zCoreConjugation parameters (quotientProjection parameters field) =
      quotientProjection parameters (zCoreConjugation parameters field) := by
  change zCoreConjugation parameters
    ((removeMean parameters 2 (removeMean parameters 3 field) -
        modeProjection parameters (removeMean parameters 2 (removeMean parameters 3 field))) -
      affineInsertion parameters (affineTrace parameters
        (removeMean parameters 2 (removeMean parameters 3 field) -
          modeProjection parameters (removeMean parameters 2 (removeMean parameters 3 field))))) = _
  simp only [map_sub, affineInsertion_conjugate, ← affineTrace_conjugate,
    ← modeProjection_conjugate,
    ← removeMean_conjugate parameters _ 2 (by decide),
    ← removeMean_conjugate parameters _ 3 (by decide)]
  simp only [quotientProjection, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.id_apply, map_sub]
  abel

end Grad.CompletedReality
