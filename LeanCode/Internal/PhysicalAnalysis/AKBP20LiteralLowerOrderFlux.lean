import AKBP19SameAxialMomentAction
import AKBP4LiteralPrincipalCoordinateConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.Constraints Grad.Constraints.Gauges Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger

def startupComponentEntry {input output : ℕ} (target : Fin output) (source : Fin input) : OperatorValue input output :=
  (PiLp.proj 2 (fun _ : Fin input => ℂ) source).smulRight
    (PiLp.single (β := fun _ : Fin output => ℂ) 2 target 1)

theorem startupComponentEntry_pairing {input output : ℕ}
    (target coordinate : Fin output) (source : Fin input) (field : StartupL2 input)
    (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell coordinate test (originalValueKernel (startupComponentEntry target source) field) =
      (if coordinate = target then 1 else 0 : ℂ) * startupCoordinateTestPairing cell source test field := by
  apply startupCoordinate_value_component
  intro value
  by_cases same : coordinate = target
  · subst coordinate
    simp [startupComponentEntry]
  · simp [startupComponentEntry,same]

def startupERSourceFlux (source : StartupL2 2) : StartupL2 2 :=
  (1/2 : ℂ) • originalValueKernel quarterValueMap (originalAverageKernel source)

def startupERLowerScalar (scale : ℝ) (determinant scalarMoment scalarFluxMoment : StartupL2 1) : StartupL2 1 :=
  -determinant - startupAxialField scale scalarMoment + startupAxialField scale scalarFluxMoment

theorem startupERLowerDivergence_L2 (scale : ℝ)
    (scalar determinant scalarFlux scalarMoment scalarFluxMoment : StartupL2 1) (source : StartupL2 2)
    (scalarSame : StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell) scalarMoment scalar)
    (fluxSame : StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell) scalarFluxMoment scalarFlux)
    (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupERLowerDivergence (fun cell => (scale : ℂ) * (Complex.I * (cell : ℂ)))
      scalar determinant scalarFlux source cell test =
      startupCoordinateTestPairing cell 0 test (startupERLowerScalar scale determinant scalarMoment scalarFluxMoment) +
        startupWeakDivergencePairing (startupERSourceFlux source) cell test := by
  simp only [startupERLowerDivergence,startupERLowerScalar,startupERSourceFlux,map_add,map_sub,map_neg,
    startupAxialField_pairing scale scalarMoment scalar scalarSame,
    startupAxialField_pairing scale scalarFluxMoment scalarFlux fluxSame]

/-- Every unknown lower-order term is a literal L2 flux. Only the given first
cell moments are differentiated axially; the spatial derivative stays on tests. -/
def startupERLowerFlux (lower : StartupL2 1) (axialGradient : StartupL2 2) (direction : Fin 2) : StartupL2 3 :=
  (if direction = 0 then
    -originalValueKernel (startupComponentEntry 0 0) lower +
      (2 : ℂ) • originalValueKernel (startupComponentEntry 1 0) (startupTrueAngularInverse 1 0 lower)
   else -(2 : ℂ) • originalValueKernel (startupComponentEntry 0 0) (startupTrueAngularInverse 1 0 lower) -
      originalValueKernel (startupComponentEntry 1 0) lower) -
    originalValueKernel (startupComponentEntry 2 direction) axialGradient

theorem startupERLowerFlux_planar (lower : StartupL2 1) (axialGradient : StartupL2 2)
    (cell : ℤ) (coordinate : Fin 2) (test : TestFunction openUnitDisk) :
    (∑ direction : Fin 2, startupCoordinateTestPairing cell coordinate.castSucc (startupDerivativeTest direction test)
      (startupERLowerFlux lower axialGradient direction)) =
      if coordinate = 0 then
        -startupCoordinateTestPairing cell 0 (startupDerivativeTest 0 test) lower -
          (2 : ℂ) * startupCoordinateTestPairing cell 0 (startupTrueInverseTest (startupDerivativeTest 1 test)) lower
      else -startupCoordinateTestPairing cell 0 (startupDerivativeTest 1 test) lower +
          (2 : ℂ) * startupCoordinateTestPairing cell 0 (startupTrueInverseTest (startupDerivativeTest 0 test)) lower := by
  simp only [Fin.sum_univ_two,startupERLowerFlux]
  norm_num only [Fin.isValue,ite_true,show (1 : Fin 2) ≠ 0 by decide,ite_false]
  simp only [map_add,map_sub,map_neg,map_smul,smul_eq_mul,startupComponentEntry_pairing,
    startupCoordinate_trueInverse_apply]
  fin_cases coordinate <;> norm_num [Fin.ext_iff] <;> ring

theorem startupERLowerFlux_scalar (lower : StartupL2 1) (axialGradient : StartupL2 2)
    (cell : ℤ) (test : TestFunction openUnitDisk) :
    (∑ direction : Fin 2, startupCoordinateTestPairing cell 2 (startupDerivativeTest direction test)
      (startupERLowerFlux lower axialGradient direction)) = startupWeakDivergencePairing axialGradient cell test := by
  simp only [Fin.sum_univ_two,startupERLowerFlux]
  norm_num only [Fin.isValue,ite_true,show (1 : Fin 2) ≠ 0 by decide,ite_false]
  simp only [map_add,map_sub,map_neg,map_smul,smul_eq_mul,startupComponentEntry_pairing]
  norm_num [Fin.ext_iff,startupWeakDivergencePairing]
  ring

theorem startupERPlanarRemainder_L2 (lower : StartupL2 1) (source : StartupL2 2)
    (axialGradient : StartupL2 2) (cell : ℤ) (coordinate : Fin 2) (test : TestFunction openUnitDisk) :
    startupERPlanarRemainder
      (fun test => startupCoordinateTestPairing cell 0 test lower +
        startupWeakDivergencePairing (startupERSourceFlux source) cell test) source cell coordinate test =
      startupERPlanarPrincipal (-source) (startupERSourceFlux source) cell coordinate test +
        ∑ direction : Fin 2, startupCoordinateTestPairing cell coordinate.castSucc (startupDerivativeTest direction test)
          (startupERLowerFlux lower axialGradient direction) := by
  rw [startupERLowerFlux_planar]
  simp only [startupERPlanarRemainder,startupERPlanarPrincipal,startupWeakCurlPairing,map_neg]
  split_ifs <;> ring

end Grad.CartesianStartup
