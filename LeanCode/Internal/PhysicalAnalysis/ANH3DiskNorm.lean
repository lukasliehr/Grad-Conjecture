import ANH2HighDisk

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.CircularHighWeak

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope

def diskXIndex : DerivativeIndex 1 := ⟨(1, 0), by decide⟩
def diskYIndex : DerivativeIndex 1 := ⟨(0, 1), by decide⟩

theorem diskIndices :
    (Finset.univ : Finset (DerivativeIndex 1)) =
      {zeroGradeIndex 1, diskXIndex, diskYIndex} := by decide

theorem diskIndex_sum (value : DerivativeIndex 1 → ℝ) :
    ∑ index, value index = value (zeroGradeIndex 1) + value diskXIndex + value diskYIndex := by
  rw [diskIndices]
  simp [diskXIndex, diskYIndex, zeroGradeIndex]
  ring

def diskGradX : diskGrade →L[ℂ] DiskL2 1 := diskCoordinate diskXIndex
def diskGradY : diskGrade →L[ℂ] DiskL2 1 := diskCoordinate diskYIndex

/-- The auxiliary completed norm is exactly the usual disk H1 sum, with
one bulk coordinate and both Cartesian first derivatives, each once. -/
theorem diskGrade_norm_sq (field : diskGrade) :
    ‖field‖ ^ 2 = ‖diskBulk field‖ ^ 2 + ‖diskGradX field‖ ^ 2 + ‖diskGradY field‖ ^ 2 := by
  apply isClosed_property diskCoreInto_denseRange
    (isClosed_eq (continuous_norm.pow 2)
      (((diskBulk.continuous.norm.pow 2).add (diskGradX.continuous.norm.pow 2)).add
        (diskGradY.continuous.norm.pow 2))) _ field
  intro core
  have coordinate (index : DerivativeIndex 1) :
      ‖closedDerivativeL2 (derivativeMultiIndex index) core‖ ^ 2 =
        ‖diskCoordinate index (diskCoreInto core)‖ ^ 2 :=
    congrArg (fun value : DiskL2 1 => ‖value‖ ^ 2) (diskCoordinate_core index core).symm
  exact (diskCore_norm_sq core).trans
    ((diskIndex_sum (fun index =>
      ‖closedDerivativeL2 (derivativeMultiIndex index) core‖ ^ 2)).trans
        (congrArg₂ (fun first second : ℝ => first + second)
          (congrArg₂ (fun first second : ℝ => first + second)
            (coordinate (zeroGradeIndex 1)) (coordinate diskXIndex))
          (coordinate diskYIndex)))

theorem diskGradX_core (field : ClosedJet 1) :
    diskGradX (diskCoreInto field) = closedDerivativeL2 (1, 0) field :=
  diskCoordinate_core diskXIndex field

theorem diskGradY_core (field : ClosedJet 1) :
    diskGradY (diskCoreInto field) = closedDerivativeL2 (0, 1) field :=
  diskCoordinate_core diskYIndex field

theorem highDiskGrade_norm_sq (field : highDiskGrade) :
    ‖field‖ ^ 2 = ‖highDiskBulk field‖ ^ 2 +
      ‖diskGradX field.val‖ ^ 2 + ‖diskGradY field.val‖ ^ 2 :=
  diskGrade_norm_sq field.val

end Grad.CircularHighWeak
