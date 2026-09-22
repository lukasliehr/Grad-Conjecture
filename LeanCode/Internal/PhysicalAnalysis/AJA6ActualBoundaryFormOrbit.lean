import AJA3ActualBulkFormOrbit
import AJA5OriginalBoundaryTranslationLaws

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularHighInverseOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularKernelL2 Grad.AnnularCurrentEnergy Grad.AnnularCurrentBoundary
open Grad.AnnularUniformBoundary Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse
open Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
local instance boundaryRealInner (parameters : PhaseParameters) : InnerProductSpace ℝ (NegativeTrace parameters 0 0 1) :=
  InnerProductSpace.rclikeToReal ℂ (NegativeTrace parameters 0 0 1)

variable (parameters : PhaseParameters) (L lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)

def retainedEnergyInput : annularEnergySpace lower L positive →L[ℂ] NegativeTrace parameters 0 0 3 :=
  (originalRetainedBoundaryLinear parameters L lengthPositive 0 0).comp
    (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0)

def highBoundaryPairing (action : NegativeTrace parameters 0 0 3 →L[ℂ] NegativeTrace parameters 0 0 1) :
    annularEnergySpace lower L positive →L[ℝ] annularEnergySpace lower L positive →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp
    ((action.comp (retainedEnergyInput parameters L lower positive lowerHalf lengthPositive)).restrictScalars ℝ)
    ((actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0).restrictScalars ℝ)

theorem highBoundaryPairing_literal (action : NegativeTrace parameters 0 0 3 →L[ℂ] NegativeTrace parameters 0 0 1)
    (field test : annularEnergySpace lower L positive) :
    highBoundaryPairing parameters L lower positive lowerHalf lengthPositive action field test =
      (inner ℂ (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test)
        (action (retainedEnergyInput parameters L lower positive lowerHalf lengthPositive field))).re :=
  inner_re_symm (𝕜 := ℂ) _ _

private def boundaryPairingLinear :
    (NegativeTrace parameters 0 0 3 →L[ℂ] NegativeTrace parameters 0 0 1) →ₗ[ℝ]
      (annularEnergySpace lower L positive →L[ℝ] annularEnergySpace lower L positive →L[ℝ] ℝ) where
  toFun := highBoundaryPairing parameters L lower positive lowerHalf lengthPositive
  map_add' := by
    intro first second
    ext field test
    change inner ℝ
      (first (retainedEnergyInput parameters L lower positive lowerHalf lengthPositive field) +
        second (retainedEnergyInput parameters L lower positive lowerHalf lengthPositive field))
      (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test) = _
    rw [inner_add_left]
    rfl
  map_smul' := by
    intro scalar action
    ext field test
    change highBoundaryPairing parameters L lower positive lowerHalf lengthPositive (scalar • action) field test =
      scalar * highBoundaryPairing parameters L lower positive lowerHalf lengthPositive action field test
    rw [highBoundaryPairing_literal, highBoundaryPairing_literal]
    change (inner ℂ
      (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 test)
      ((scalar : ℂ) • action (retainedEnergyInput parameters L lower positive lowerHalf lengthPositive field))).re = _
    simp only [inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem highBoundaryPairing_norm_bound (action : NegativeTrace parameters 0 0 3 →L[ℂ] NegativeTrace parameters 0 0 1) :
    ‖highBoundaryPairing parameters L lower positive lowerHalf lengthPositive action‖ ≤
      (originalRetainedBoundaryConstant parameters 0 0 * uniformOuterTraceConstant L ^ 2) * ‖action‖ := by
  have retainedNonnegative := originalRetainedBoundaryConstant_nonnegative parameters 0 0
  have traceNonnegative := uniformOuterTraceConstant_nonnegative L
  have nonnegative : 0 ≤ originalRetainedBoundaryConstant parameters 0 0 * uniformOuterTraceConstant L ^ 2 := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg nonnegative (norm_nonneg action))
  intro field
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg nonnegative (norm_nonneg action)) (norm_nonneg field))
  intro test
  rw [highBoundaryPairing_literal, Real.norm_eq_abs]
  apply (Complex.abs_re_le_norm _).trans
  have input := (originalRetainedBoundaryLinear_bound parameters L lengthPositive 0 0
    (actualCurrentHighOuterTrace parameters lower L positive lowerHalf lengthPositive 0 0 field)).trans
      (mul_le_mul_of_nonneg_left
        (actualCurrentHighOuterTrace_bound parameters lower L positive lowerHalf lengthPositive 0 0 field) retainedNonnegative)
  have output := (action.le_opNorm _).trans (mul_le_mul_of_nonneg_left input (norm_nonneg action))
  exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans ((mul_le_mul
    (actualCurrentHighOuterTrace_bound parameters lower L positive lowerHalf lengthPositive 0 0 test)
    output (norm_nonneg _) (mul_nonneg traceNonnegative (norm_nonneg test))).trans_eq (by ring))

/-- The original physical boundary pairing as a bounded coefficient-to-form map. -/
def boundaryPairingAction :
    (NegativeTrace parameters 0 0 3 →L[ℂ] NegativeTrace parameters 0 0 1) →L[ℝ]
      (annularEnergySpace lower L positive →L[ℝ] annularEnergySpace lower L positive →L[ℝ] ℝ) :=
  LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := NegativeTrace parameters 0 0 3 →L[ℂ] NegativeTrace parameters 0 0 1)
    (F := annularEnergySpace lower L positive →L[ℝ] annularEnergySpace lower L positive →L[ℝ] ℝ)
    (σ := RingHom.id ℝ) (boundaryPairingLinear parameters L lower positive lowerHalf lengthPositive)
    (originalRetainedBoundaryConstant parameters 0 0 * uniformOuterTraceConstant L ^ 2)
    (highBoundaryPairing_norm_bound parameters L lower positive lowerHalf lengthPositive)

variable (compact : ℝ) (state : RetainedInverseState parameters L compact)

def highBoundaryFormOrbitJet (tau : OrbitParameter) (angular cell : ℕ) :=
  boundaryPairingAction parameters L lower positive lowerHalf lengthPositive
    (boundaryOrbitJetAction parameters 0 0 (actualRetainedBoundaryLiftKernel state.outerInverseState) tau angular cell)

theorem highBoundaryFormOrbitJet_hasFDerivAt (tau : OrbitParameter) (angular cell : ℕ) :
    HasFDerivAt (fun sigma => highBoundaryFormOrbitJet parameters L lower positive lowerHalf lengthPositive compact state sigma angular cell)
      ((boundaryPairingAction parameters L lower positive lowerHalf lengthPositive).comp
        (orbitDifferential
          (boundaryOrbitJetAction parameters 0 0 (actualRetainedBoundaryLiftKernel state.outerInverseState) tau (angular + 1) cell)
          (boundaryOrbitJetAction parameters 0 0 (actualRetainedBoundaryLiftKernel state.outerInverseState) tau angular (cell + 1)))) tau :=
  HasFDerivAt.comp (𝕜 := ℝ) (E := OrbitParameter)
    (F := NegativeTrace parameters 0 0 3 →L[ℂ] NegativeTrace parameters 0 0 1)
    (G := annularEnergySpace lower L positive →L[ℝ] annularEnergySpace lower L positive →L[ℝ] ℝ)
    tau (ContinuousLinearMap.hasFDerivAt
      (E := NegativeTrace parameters 0 0 3 →L[ℂ] NegativeTrace parameters 0 0 1)
      (F := annularEnergySpace lower L positive →L[ℝ] annularEnergySpace lower L positive →L[ℝ] ℝ)
      (boundaryPairingAction parameters L lower positive lowerHalf lengthPositive))
      (boundaryOrbitJetAction_hasFDerivAt parameters 0 0 (actualRetainedBoundaryLiftKernel state.outerInverseState) tau angular cell)

end Grad.AnnularHighInverseOrbit
