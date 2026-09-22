import AJA2ExactPhysicalPacketTranslations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.AnnularHighInverseOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularKernelL2 Grad.AnnularCurrentEnergy
open Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
local instance bulkRealInner (lower : ℝ) : InnerProductSpace ℝ (DivisionRow 3 lower) :=
  InnerProductSpace.rclikeToReal ℂ (DivisionRow 3 lower)

variable (parameters : PhaseParameters) (L lower : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))

private def bulkPairingLinear :
    (DivisionRow 8 lower →L[ℂ] DivisionRow 3 lower) →ₗ[ℝ]
      (annularEnergySpace lower L positive →L[ℝ] annularEnergySpace lower L positive →L[ℝ] ℝ) where
  toFun := highBulkPairing parameters L lower positive lengthPositive widthHalf widthLength
  map_add' := by
    intro first second
    ext field test
    change -inner ℝ
      (first (highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength field) +
        second (highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength field))
      (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test) = _
    rw [inner_add_left, neg_add]
    rfl
  map_smul' := by
    intro scalar action
    ext field test
    change highBulkPairing parameters L lower positive lengthPositive widthHalf widthLength (scalar • action) field test =
      scalar * highBulkPairing parameters L lower positive lengthPositive widthHalf widthLength action field test
    rw [highBulkPairing_literal, highBulkPairing_literal]
    change (-inner ℂ
      (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test)
      ((scalar : ℂ) • action (highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength field))).re = _
    simp only [inner_smul_right, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring

theorem highBulkPairing_norm_bound (action : DivisionRow 8 lower →L[ℂ] DivisionRow 3 lower) :
    ‖highBulkPairing parameters L lower positive lengthPositive widthHalf widthLength action‖ ≤
      (5 * (4 + 2 * |L|)) * ‖action‖ := by
  have nonnegative : 0 ≤ 5 * (4 + 2 * |L|) := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg nonnegative (norm_nonneg action))
  intro field
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg nonnegative (norm_nonneg action)) (norm_nonneg field))
  intro test
  rw [highBulkPairing_literal, Real.norm_eq_abs]
  apply (Complex.abs_re_le_norm _).trans
  rw [norm_neg]
  have paired := norm_inner_le_norm (𝕜 := ℂ)
    (highEnergyTestPacket parameters lower L positive lengthPositive widthHalf widthLength test)
    (action (highEightEnergyPacket parameters lower L positive lengthPositive widthHalf widthLength field))
  have output := (action.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left
      (highEightEnergyPacket_bound parameters lower L positive lengthPositive widthHalf widthLength field) (norm_nonneg action))
  exact paired.trans ((mul_le_mul
    (highEnergyTestPacket_bound parameters lower L positive lengthPositive widthHalf widthLength test) output
      (norm_nonneg _) (by positivity)).trans_eq (by ring))

/-- The literal AEJ bulk pairing is a bounded real-linear map of the actual
completed coefficient operator. -/
def bulkPairingAction :
    (DivisionRow 8 lower →L[ℂ] DivisionRow 3 lower) →L[ℝ]
      (annularEnergySpace lower L positive →L[ℝ] annularEnergySpace lower L positive →L[ℝ] ℝ) :=
  LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := DivisionRow 8 lower →L[ℂ] DivisionRow 3 lower)
    (F := annularEnergySpace lower L positive →L[ℝ] annularEnergySpace lower L positive →L[ℝ] ℝ)
    (σ := RingHom.id ℝ) (bulkPairingLinear parameters L lower positive lengthPositive widthHalf widthLength)
    (5 * (4 + 2 * |L|)) (highBulkPairing_norm_bound parameters L lower positive lengthPositive widthHalf widthLength)

variable (compact : ℝ) (bounded : lower ≤ 1) (state : RetainedInverseState parameters L compact)

/-- The original power-zero bulk form with the actual conjugated physical
coefficient action, on the unchanged completed energy graph. -/
def highBulkFormOrbit (tau : OrbitParameter) :=
  bulkPairingAction parameters L lower positive lengthPositive widthHalf widthLength
    (actualEliminatedOrbit parameters L compact lower positive bounded state 0 tau)

def highBulkFormOrbitJet (tau : OrbitParameter) (angular cell : ℕ) :=
  bulkPairingAction parameters L lower positive lengthPositive widthHalf widthLength
    (actualEliminatedOrbitJet parameters L compact lower positive bounded state 0 tau angular cell)

theorem highBulkFormOrbit_hasFDerivAt (tau : OrbitParameter) :
    HasFDerivAt (highBulkFormOrbit parameters L lower positive lengthPositive widthHalf widthLength compact bounded state)
      ((bulkPairingAction parameters L lower positive lengthPositive widthHalf widthLength).comp
        (orbitDifferential
          (actualEliminatedOrbitJet parameters L compact lower positive bounded state 0 tau 1 0)
          (actualEliminatedOrbitJet parameters L compact lower positive bounded state 0 tau 0 1))) tau :=
  HasFDerivAt.comp (𝕜 := ℝ) (E := OrbitParameter)
    (F := DivisionRow 8 lower →L[ℂ] DivisionRow 3 lower)
    (G := annularEnergySpace lower L positive →L[ℝ] annularEnergySpace lower L positive →L[ℝ] ℝ)
    tau (ContinuousLinearMap.hasFDerivAt
      (E := DivisionRow 8 lower →L[ℂ] DivisionRow 3 lower)
      (F := annularEnergySpace lower L positive →L[ℝ] annularEnergySpace lower L positive →L[ℝ] ℝ)
      (bulkPairingAction parameters L lower positive lengthPositive widthHalf widthLength))
    (actualEliminatedOrbit_hasFDerivAt parameters L compact lower positive bounded state 0 tau)

end Grad.AnnularHighInverseOrbit
