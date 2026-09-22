import AEG10LiteralPhysicalDualPairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentEnergy
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularTiltedReference Grad.AnnularKernelL2
open Grad.GaugeCoefficients.Physical.Ledger Grad.BoundaryKernelAction

section Core
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- On the literal b-weighted physical core, the first packet slot is exactly
w'-(Phi'-9/(4r))w, including the derivative of the radial weight. -/
theorem highPhysicalDerivative_core (core : HighAnnularMode →₀ complexSmoothRadialCore 1)
    (mode : HighAnnularMode) :
    highPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength
      (bEnergyCore lower length positive core) mode =
      weightedCurveComplex 1 lower ((core mode).val.2 -
        continuousCurveWeight 1 (annularTiltCurve parameters lower positive mode.val.2) (core mode).val.1) := by
  change annularEnergyDerivative lower length positive
      (bEnergyDecode lower length positive (bEnergyCore lower length positive core)) mode -
    annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength
      (bEnergyDecode lower length positive (bEnergyCore lower length positive core)) mode = _
  rw [bEnergyCore_decode, annularEnergyDerivative_core_mode, annularTiltEnergyPhase_core_mode, map_sub]

/-- The test has exactly the opposite phase slope on the same physical core. -/
theorem highPhysicalTestDerivative_core (core : HighAnnularMode →₀ complexSmoothRadialCore 1)
    (mode : HighAnnularMode) :
    highPhysicalTestDerivative parameters lower length positive lengthPositive widthHalf widthLength
      (bEnergyCore lower length positive core) mode =
      weightedCurveComplex 1 lower ((core mode).val.2 +
        continuousCurveWeight 1 (annularTiltCurve parameters lower positive mode.val.2) (core mode).val.1) := by
  change annularEnergyDerivative lower length positive
      (bEnergyDecode lower length positive (bEnergyCore lower length positive core)) mode +
    annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength
      (bEnergyDecode lower length positive (bEnergyCore lower length positive core)) mode = _
  rw [bEnergyCore_decode, annularEnergyDerivative_core_mode, annularTiltEnergyPhase_core_mode, map_add]

/-- All four prescribed-source slots are literally zero in the homogeneous
packet, not merely bounded by an omitted norm. -/
theorem highEightEnergyPacket_sources_zero (field : annularEnergySpace lower length positive) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : HighAnnularMode, ∀ coordinate : Fin 8,
      4 ≤ coordinate.val →
      highEightEnergyPacket parameters lower length positive lengthPositive widthHalf widthLength field mode.val radius coordinate = 0 := by
  filter_upwards [highEightEnergyPacket_ae parameters lower length positive lengthPositive widthHalf widthLength field]
    with radius actual
  intro mode coordinate source
  rw [actual mode]
  fin_cases coordinate <;> simp_all [operatorBasis]

/-- Exact common-collar consumer: original physical input coordinates,
uniform energy/test bounds, and the literal b-weighted finite-core derivative. -/
theorem actualHighEnergyPacket_consumer (field test : annularEnergySpace lower length positive)
    (core : HighAnnularMode →₀ complexSmoothRadialCore 1) :
    ‖highEightEnergyPacket parameters lower length positive lengthPositive widthHalf widthLength field‖ ≤
      (4 + 2 * |length|) * ‖field‖ ∧
    ‖highEnergyTestPacket parameters lower length positive lengthPositive widthHalf widthLength test‖ ≤ 5 * ‖test‖ ∧
    (∀ mode : HighAnnularMode,
      highPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength
        (bEnergyCore lower length positive core) mode =
      weightedCurveComplex 1 lower ((core mode).val.2 -
        continuousCurveWeight 1 (annularTiltCurve parameters lower positive mode.val.2) (core mode).val.1)) :=
  ⟨highEightEnergyPacket_bound parameters lower length positive lengthPositive widthHalf widthLength field,
    highEnergyTestPacket_bound parameters lower length positive lengthPositive widthHalf widthLength test,
    highPhysicalDerivative_core parameters lower length positive lengthPositive widthHalf widthLength core⟩

end Core
end Grad.AnnularCurrentEnergy
