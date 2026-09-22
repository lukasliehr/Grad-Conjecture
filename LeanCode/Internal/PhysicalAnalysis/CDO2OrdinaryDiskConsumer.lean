import CDO1WithinClosedJet
import AIG2ActualGlobalGluing

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace Grad.ClosedDiskRegularity
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.CircularHighRegularity
open Grad.OrdinaryDiskCalculus Grad.ActualInverseInduction Grad.InteriorLocalization
open Grad.OrdinaryInteriorBootstrap Grad.PDEBootstrap
attribute [local instance] unitNormedSpace

def withinOrdinaryDisk (grade : ℕ) (field : SpatialPlane → ComplexEuclidean 1)
    (smooth : ContDiffOn ℝ ∞ field closedUnitDisk) : unitDiskSobolev grade :=
  unitDiskCoreInto grade (withinClosedJet field smooth)

theorem withinOrdinaryDisk_bulk (grade : ℕ) (field : SpatialPlane → ComplexEuclidean 1)
    (smooth : ContDiffOn ℝ ∞ field closedUnitDisk) :
    unitDiskBulk grade (withinOrdinaryDisk grade field smooth) =
      closedL2Core (withinClosedJet field smooth) :=
  unitDiskBulk_core grade (withinClosedJet field smooth)

theorem withinOrdinaryDisk_bulk_ae (grade : ℕ) (field : SpatialPlane → ComplexEuclidean 1)
    (smooth : ContDiffOn ℝ ∞ field closedUnitDisk) :
    ∀ᵐ point ∂volume.restrict openUnitDisk,
      unitDiskBulk grade (withinOrdinaryDisk grade field smooth) point = field point := by
  rw [withinOrdinaryDisk_bulk]
  filter_upwards [closedContinuousToDiskL2_ae (withinClosedJet field smooth).value,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point literal inside
  exact literal.trans (withinClosedValue_lift field smooth inside)

theorem withinOrdinaryDisk_derivative (grade : ℕ) (index : DerivativeIndex grade)
    (field : SpatialPlane → ComplexEuclidean 1)
    (smooth : ContDiffOn ℝ ∞ field closedUnitDisk) :
    unitDiskDerivative grade index (withinOrdinaryDisk grade field smooth) =
      closedDerivativeL2 (derivativeMultiIndex index) (withinClosedJet field smooth) :=
  unitDiskDerivative_core grade index (withinClosedJet field smooth)

theorem withinOrdinaryDisk_norm_sq (grade : ℕ) (field : SpatialPlane → ComplexEuclidean 1)
    (smooth : ContDiffOn ℝ ∞ field closedUnitDisk) :
    ‖withinOrdinaryDisk grade field smooth‖ ^ 2 =
      ∑ index : DerivativeIndex grade,
        ‖closedDerivativeL2 (derivativeMultiIndex index) (withinClosedJet field smooth)‖ ^ 2 := by
  rw [unitDiskSobolev_norm_sq]
  apply Finset.sum_congr rfl
  intro index _
  rw [withinOrdinaryDisk_derivative]

/-- The exact ordinary completion representative follows from within smoothness
and the literal field identity; no outer Sobolev representative is assumed. -/
theorem withinOrdinaryDisk_same (grade : ℕ) (field : SpatialPlane → ComplexEuclidean 1)
    (smooth : ContDiffOn ℝ ∞ field closedUnitDisk) (target : DiskL2 1)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, field point = target point) :
    unitDiskBulk grade (withinOrdinaryDisk grade field smooth) = target := by
  apply Lp.ext
  filter_upwards [withinOrdinaryDisk_bulk_ae grade field smooth, same] with point first second
  exact first.trans second

/-- Immediate consumer of the new adapter at the accepted actual global
induction boundary. The finite outer field's within smoothness and bulk law
are precisely the remaining geometric construction inputs. -/
theorem actualGlobal_of_outerWithinSmooth (parameters : PhaseParameters) (grade : ℕ)
    (parameter : ℝ) (source : highDiskL2)
    (state : unitDiskSobolev (grade + 1)) (forcing : unitDiskSobolev grade)
    (stateSame : unitDiskBulk (grade + 1) state = highDiskBulk (highRobinWeakInverse parameter source))
    (sourceSame : unitDiskBulk grade forcing = source.val)
    (field : SpatialPlane → ComplexEuclidean 1)
    (smooth : ContDiffOn ℝ ∞ field closedUnitDisk)
    (outerSame : ∀ᵐ point ∂volume.restrict openUnitDisk, field point =
      diskScalar outerCutoffScalar outerCutoffScalar_smooth
        (highDiskBulk (highRobinWeakInverse parameter source)) point) :
    ∃ global : unitDiskSobolev (grade + 2),
      unitDiskBulk (grade + 2) global = highDiskBulk (highRobinWeakInverse parameter source) ∧
      HasDiskWeakLaplacian (unitDiskBulk (grade + 2) global) (weakLaplacianValue parameter source) ∧
      ‖global‖ ≤ inverseInteriorStateConstant grade parameter * ‖state‖ +
        ordinaryInteriorSourceConstant grade * ‖forcing‖ +
          ‖withinOrdinaryDisk (grade + 2) field smooth‖ :=
  actualGlobal_inductionStep parameters grade parameter source state forcing stateSame sourceSame
    (withinOrdinaryDisk (grade + 2) field smooth)
    (withinOrdinaryDisk_same (grade + 2) field smooth _ outerSame)

end Grad.ClosedDiskRegularity
