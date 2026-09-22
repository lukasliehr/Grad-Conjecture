import AKBQ4SameNativeGaugeProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
namespace Grad.ActualScaledNativeCoefficients
open Grad.GenericCarriers Grad.PDEBootstrap
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollar Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.ActualSmoothPhysicalField Grad.OriginalKernelCovariantRecovery Grad.SourceCollarFullSource
open Grad.Constraints Grad.Constraints.Gauges Grad.CartesianStartup Grad.AnnularReconstruction

variable {L ell compact : ℝ} {parameters : PhaseParameters}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (state : RadialCoefficientState parameters L compact)
    (ledger : ActualLedger parameters admissible state.data.rho state.data.alpha state.data.delta
      state.data.parameter state.data.epsilon state.data.field)

/-- Exact row fidelity on a scaled circle; `same` is the raw covariant identity, not an equation or gauge premise. -/
theorem scaledRawGauge_nativeProduct (raw : ℝ×Spatial → PhysicalValue 3)
    (radius : ℝ) (positive : 0 < radius) (bounded : |radius| ≤ 1)
    (source : ℝ×ℝ → ComplexEuclidean 3)
    (same : ∀ polar axial, raw (axial,(Grad.Constraints.polarClosedPoint radius bounded polar).val) =
      cartesianCovariantValue polar (source (polar,axial))) (polar axial : ℝ) :
    let product := startupRawMatrix (fullGaugeFamily ledger.val.gaugeDeviation) raw
      (axial,(Grad.Constraints.polarClosedPoint radius bounded polar).val)
    let r : RadialPoint := ⟨ell*radius,mul_nonneg admissible.2.2.2.1.le positive.le,
      (mul_le_of_le_one_left positive.le (admissible.2.2.2.2.trans (min_le_left _ _))).trans ((le_abs_self radius).trans bounded)⟩
    polarTangentialComponent polar (planarPartMap product) =
      originalTotalGaugeProduct parameters L compact state r 0 source (polar,axial) 0 ∧
    toroidalPartMap product = originalTotalGaugeProduct parameters L compact state r 1 source (polar,axial) := by
  dsimp only
  rw [startupRawMatrix_value,same]
  have point : Grad.Constraints.polarClosedPoint radius bounded polar =
      Grad.SourceCollarDivision.polarClosedPoint radius polar positive.le ((le_abs_self radius).trans bounded) :=
    (divisionPolarPoint_eq_original radius polar positive.le ((le_abs_self radius).trans bounded)).symm
  rw [point]
  exact scaledGauge_nativeProduct admissible state ledger radius positive ((le_abs_self radius).trans bounded) source polar axial

end Grad.ActualScaledNativeCoefficients
