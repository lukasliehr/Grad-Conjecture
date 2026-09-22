import AJA7ActualBoundaryOrbitConjugacy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.AnnularHighInverseOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularCurrentEnergy Grad.AnnularCurrentBoundary
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse
open Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)

/-- The actual complete high form orbit, on the unchanged energy space. -/
def currentHighFormOrbit (tau : OrbitParameter) :=
  highBulkFormOrbit parameters L lower positive lengthPositive widthHalf widthLength compact
    (lowerHalf.trans (by norm_num)) state tau +
  highBoundaryFormOrbitJet parameters L lower positive lowerHalf lengthPositive compact state tau 0 0

theorem currentHighFormOrbit_differentiableAt (tau : OrbitParameter) :
    DifferentiableAt ℝ (currentHighFormOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state) tau := by
  exact (HasFDerivAt.add (𝕜 := ℝ) (E := OrbitParameter)
    (F := annularEnergySpace lower L positive →L[ℝ] annularEnergySpace lower L positive →L[ℝ] ℝ)
    (highBulkFormOrbit_hasFDerivAt parameters L lower positive lengthPositive widthHalf widthLength compact
      (lowerHalf.trans (by norm_num)) state tau)
    (highBoundaryFormOrbitJet_hasFDerivAt parameters L lower positive lowerHalf lengthPositive compact state tau 0 0)).differentiableAt

def currentHighFormOrbitDerivative (tau : OrbitParameter) : OrbitParameter →L[ℝ]
    (annularEnergySpace lower L positive →L[ℝ] annularEnergySpace lower L positive →L[ℝ] ℝ) :=
  fderiv ℝ (currentHighFormOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state) tau

theorem currentHighFormOrbit_hasFDerivAt (tau : OrbitParameter) :
    HasFDerivAt (currentHighFormOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state)
      (currentHighFormOrbitDerivative parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau) tau :=
  (currentHighFormOrbit_differentiableAt parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau).hasFDerivAt

/-- Genuine conjugation of the SAME complete physical form. -/
theorem currentHighFormOrbit_pullback (tau : OrbitParameter) (field test : annularEnergySpace lower L positive) :
    currentHighFormOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau field test =
      currentHighForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
        (energyTranslation lower L positive (-tau) field) (energyTranslation lower L positive (-tau) test) := by
  change highBulkFormOrbit parameters L lower positive lengthPositive widthHalf widthLength compact
    (lowerHalf.trans (by norm_num)) state tau field test +
    highBoundaryFormOrbitJet parameters L lower positive lowerHalf lengthPositive compact state tau 0 0 field test = _
  rw [highBulkFormOrbit_pullback, highBoundaryFormOrbit_pullback]
  rfl

end Grad.AnnularHighInverseOrbit
