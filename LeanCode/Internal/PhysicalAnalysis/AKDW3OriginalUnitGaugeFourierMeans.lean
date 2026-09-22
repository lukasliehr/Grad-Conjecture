import AKDW2OriginalUnitRawGaugeRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
namespace Grad.ActualScaledNativeCoefficients
open Grad.GaugeCoefficients.Physical.Allocation Grad.ActualGaugeSigmaPrimitives
open Grad.GenericCarriers Grad.PDEBootstrap
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollar Grad.SourceCollarCoefficients Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.ActualSmoothPhysicalField Grad.OriginalKernelCovariantRecovery Grad.SourceCollarFullSource
open Grad.Constraints Grad.Constraints.Gauges Grad.CartesianStartup Grad.AnnularReconstruction Grad.BoundaryTrace
open scoped BigOperators

variable {L compact : ℝ} {parameters : PhaseParameters}
    (state : RadialCoefficientState parameters L compact)
    (gauge : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3)
    (sameGauge : ∀ grade angle point, familyMatrix (fullGaugeFamily gauge) grade angle point =
      originalPhysicalGaugeMatrix parameters L state.data.rho state.data.alpha state.data.delta
        state.data.parameter state.data.epsilon state.data.field angle point)

include sameGauge


/-- Fourier cells are selected after the genuine C0 multiplication; both literal native polar means pass unchanged. -/
theorem originalUnitRawGauge_cellMeans (raw : ℝ×Spatial → PhysicalValue 3)
    (regular : StartupOrbitContinuous raw)
    (radius : ℝ) (positive : 0 < radius) (inside : radius < 1) (bounded : |radius| ≤ 1)
    (source : ℝ×ℝ → ComplexEuclidean 3) (continuousSource : Continuous source)
    (same : ∀ polar axial, raw (axial,(Grad.Constraints.polarClosedPoint radius bounded polar).val) =
      cartesianCovariantValue polar (source (polar,axial)))
    (cell : ℤ)
    (nativeMean : ∀ kind : Fin 2,
      angularCoefficient (fun polar => angularCoefficient (fun axial =>
        originalTotalGaugeProduct parameters L compact state
          ⟨radius,positive.le,(le_abs_self radius).trans bounded⟩
          kind source (polar,axial)) cell) 0 = 0) :
    angularCoefficient (fun polar => polarTangentialComponent polar (planarPartMap
      (angularCoefficient (fun axial => startupRawMatrix (fullGaugeFamily gauge) raw
        (axial,(Grad.Constraints.polarClosedPoint radius bounded polar).val)) cell))) 0 = 0 ∧
    angularCoefficient (fun polar => toroidalPartMap
      (angularCoefficient (fun axial => startupRawMatrix (fullGaugeFamily gauge) raw
        (axial,(Grad.Constraints.polarClosedPoint radius bounded polar).val)) cell)) 0 = 0 := by
  let output := startupRawMatrix (fullGaugeFamily gauge) raw
  let point := fun polar => Grad.Constraints.polarClosedPoint radius bounded polar
  let r : RadialPoint := ⟨radius,positive.le,(le_abs_self radius).trans bounded⟩
  let native := fun kind => originalTotalGaugeProduct parameters L compact state r kind source
  have outContinuous (polar : ℝ) : Continuous (fun axial => output (axial,(point polar).val)) :=
    (regular.matrix (unitDiskAdmissible parameters) (fullGaugeFamily gauge)).axial (point polar)
      (by rw [startupPolarClosedPoint_norm,abs_of_pos positive]; exact positive)
      (by rw [startupPolarClosedPoint_norm,abs_of_pos positive]; exact inside)
  have row0 (polar axial : ℝ) : gaugeTangentialMap polar (output (axial,(point polar).val)) = native 0 (polar,axial) := by
    apply PiLp.ext
    intro coordinate
    have unique : coordinate = 0 := Subsingleton.elim _ _
    subst coordinate
    exact (gaugeTangentialMap_apply polar (output (axial,(point polar).val))).trans
      (originalUnitRawGauge_nativeProduct state gauge sameGauge raw radius positive bounded source same polar axial).1
  have row1 (polar axial : ℝ) : toroidalPartMap (output (axial,(point polar).val)) = native 1 (polar,axial) :=
    (originalUnitRawGauge_nativeProduct state gauge sameGauge raw radius positive bounded source same polar axial).2
  have cell0 (polar : ℝ) : gaugeTangentialMap polar
      (angularCoefficient (fun axial => output (axial,(point polar).val)) cell) =
      angularCoefficient (fun axial => native 0 (polar,axial)) cell := by
    rw [← angularCoefficient_valueMap _ _ (outContinuous polar)]
    simp_rw [row0]
  have cell1 (polar : ℝ) : toroidalPartMap
      (angularCoefficient (fun axial => output (axial,(point polar).val)) cell) =
      angularCoefficient (fun axial => native 1 (polar,axial)) cell := by
    rw [← angularCoefficient_valueMap _ _ (outContinuous polar)]
    simp_rw [row1]
  have firstZero : angularCoefficient (fun polar => gaugeTangentialMap polar
      (angularCoefficient (fun axial => output (axial,(point polar).val)) cell)) 0 = 0 := by
    simp_rw [cell0]
    exact nativeMean 0
  have firstContinuous : Continuous (fun polar => gaugeTangentialMap polar
      (angularCoefficient (fun axial => output (axial,(point polar).val)) cell)) := by
    simp_rw [cell0]
    exact angularCoefficient_continuous_parameter _
      (originalTotalGaugeProduct_continuous parameters L compact state r 0 source continuousSource) cell
  constructor
  · have coordinate := angularCoefficient_component _ firstContinuous 0 0
    rw [firstZero] at coordinate
    change (0 : ℂ) = _ at coordinate
    simpa only [gaugeTangentialMap_apply] using coordinate.symm
  · change angularCoefficient (fun polar => toroidalPartMap
      (angularCoefficient (fun axial => output (axial,(point polar).val)) cell)) 0 = 0
    simp_rw [cell1]
    exact nativeMean 1

end Grad.ActualScaledNativeCoefficients
