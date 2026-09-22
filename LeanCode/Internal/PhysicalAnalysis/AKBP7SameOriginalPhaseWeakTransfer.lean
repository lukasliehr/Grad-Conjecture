import AKBP6FixedTensorRadialCovariance

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.WeightedJets
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.AnalyticWeights.Calculus
open Grad.RepresentedKernel.SpatialProduct Grad.WeightedJets.SpatialMultiplier

theorem startupPhysicalWeight_radial (sigma gamma ell : ℝ) (cell : ℤ) (angle : ℝ) (point : Spatial) :
    physicalWeight sigma gamma ell cell (Grad.GaugeCoefficients.Radial.planeRotationEquiv angle point) =
      physicalWeight sigma gamma ell cell point := by
  simp only [physicalWeight,LinearIsometryEquiv.norm_map]

theorem startupWeightRelated_inverse {dimension : ℕ} (sigma gamma ell : ℝ)
    {weighted original : StartupL2 dimension}
    (same : StartupRadialRelated (physicalWeight sigma gamma ell) weighted original) :
    StartupRadialRelated (inverseWeight sigma gamma ell) original weighted := by
  filter_upwards [same] with point same
  intro cell
  rw [same cell,smul_smul,mul_comm (inverseWeight sigma gamma ell cell point),
    (formulaGoal sigma gamma ell cell point).2.2.2.2,one_smul]

theorem startupWeightedRaw_pairing (sigma gamma ell : ℝ) (weighted original : StartupL2 3)
    (same : StartupRadialRelated (physicalWeight sigma gamma ell) weighted original)
    (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk) :
    startupTestPairing cell vector test weighted =
      startupTestPairing cell vector (multiplyTest (physicalWeight sigma gamma ell cell)
        (smoothGoal sigma gamma ell cell).2.1 test) original :=
  startupTestPairing_cellScalar _ (smoothGoal sigma gamma ell cell).2.1 cell vector test original weighted
    (same.mono (fun _ same => same cell))

theorem startupUnweightedRaw_pairing (sigma gamma ell : ℝ) (weighted original : StartupL2 3)
    (same : StartupRadialRelated (physicalWeight sigma gamma ell) weighted original)
    (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk) :
    startupTestPairing cell vector test original =
      startupTestPairing cell vector (multiplyTest (inverseWeight sigma gamma ell cell)
        (smoothGoal sigma gamma ell cell).2.2 test) weighted :=
  startupTestPairing_cellScalar _ (smoothGoal sigma gamma ell cell).2.2 cell vector test weighted original
    ((startupWeightRelated_inverse sigma gamma ell same).mono (fun _ same => same cell))

theorem startupScaledConjugatedFirstTest (sigma gamma ell : ℝ) (cell : ℤ) (direction : Fin 2)
    (test : TestFunction openUnitDisk) :
    multiplyTest (inverseWeight sigma gamma ell cell) (smoothGoal sigma gamma ell cell).2.2
      (startupDerivativeTest direction
        (multiplyTest (physicalWeight sigma gamma ell cell) (smoothGoal sigma gamma ell cell).2.1 test)) =
      startupAddTest (startupDerivativeTest direction test)
        (multiplyTest (startupScaledPhaseSlope sigma gamma ell cell direction)
          (startupScaledPhaseSlope_smooth sigma gamma ell cell direction) test) := by
  apply startupTest_ext
  intro point
  exact startupScaledPhaseTest_first sigma gamma ell cell direction test point

/-- One derivative of the original scaled phase has its literal moment-paid
L2 remainder, before any weak derivative of the unknown exists. -/
theorem startupWeightedRaw_first (sigma gamma ell : ℝ) (nonnegative : 0 ≤ gamma)
    (ellNonnegative : 0 ≤ ell) (ellOne : ell ≤ 1)
    (weighted original moment : StartupL2 3)
    (same : StartupRadialRelated (physicalWeight sigma gamma ell) weighted original)
    (momentSame : StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell) moment weighted)
    (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk) (direction : Fin 2) :
    startupTestPairing cell vector (startupDerivativeTest direction
      (multiplyTest (physicalWeight sigma gamma ell cell) (smoothGoal sigma gamma ell cell).2.1 test)) original =
      startupTestPairing cell vector (startupDerivativeTest direction test) weighted +
      startupTestPairing cell vector test
        (startupScaledPhaseFirstField sigma gamma ell nonnegative ellNonnegative ellOne direction moment) := by
  rw [startupUnweightedRaw_pairing sigma gamma ell weighted original same,
    startupScaledConjugatedFirstTest,startupTestPairing_add,add_apply,
    startupScaledPhaseFirstField_pairing sigma gamma ell nonnegative ellNonnegative ellOne direction weighted moment momentSame]

/-- The complete Hessian and squared phase-gradient terms are retained in
second-order weak conjugation; every moment is of the SAME field. -/
theorem startupWeightedRaw_second (sigma gamma ell : ℝ) (nonnegative : 0 ≤ gamma)
    (ellNonnegative : 0 ≤ ell) (ellOne : ell ≤ 1)
    (weighted original firstMoment secondMoment : StartupL2 3)
    (same : StartupRadialRelated (physicalWeight sigma gamma ell) weighted original)
    (firstSame : StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell) firstMoment weighted)
    (secondSame : StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell ^ 2) secondMoment weighted)
    (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk) (outer inner : Fin 2) :
    startupTestPairing cell vector (startupDerivativeTest outer (startupDerivativeTest inner
      (multiplyTest (physicalWeight sigma gamma ell cell) (smoothGoal sigma gamma ell cell).2.1 test))) original =
      startupTestPairing cell vector (startupDerivativeTest outer (startupDerivativeTest inner test)) weighted +
      startupTestPairing cell vector (startupDerivativeTest outer test)
        (startupScaledPhaseFirstField sigma gamma ell nonnegative ellNonnegative ellOne inner firstMoment) +
      startupTestPairing cell vector (startupDerivativeTest inner test)
        (startupScaledPhaseFirstField sigma gamma ell nonnegative ellNonnegative ellOne outer firstMoment) +
      startupTestPairing cell vector test
        (startupScaledPhaseSecondField sigma gamma ell nonnegative ellNonnegative ellOne outer inner secondMoment) := by
  rw [startupUnweightedRaw_pairing sigma gamma ell weighted original same]
  exact startupScaledPhaseWeakSecond sigma gamma ell nonnegative ellNonnegative ellOne weighted
    firstMoment secondMoment firstSame secondSame cell vector test outer inner

end Grad.CartesianStartup
