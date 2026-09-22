import AKDW30SameCutoffTensorCores
import AKDW27OriginalPacketSourcePayment

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxRecDepth 4000
open Set
open scoped ContDiff
namespace Grad.CartesianStartup.StartupOriginalUnitNormPacket
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets Grad.NonlinearProduct
open Grad.OriginalCoreRealization Grad.SourceCollarCoefficients Grad.TensorBootstrap

/-- Quantitative actual second-divergence remainder after the fixed
radial cutoff. Only the source norm and one high budget times M0(w) remain. -/
theorem cutoffTensor_remainder_bound (parameters : PhaseParameters) (length radius : ℝ) (radiusNonnegative : 0≤radius)
    (rank : ℕ) (scale : ℝ) (index : TensorIndex)
    (cutoff : Spatial → ℝ) (cutoffSmooth : ContDiff ℝ ∞ cutoff) (cutoffCompact : HasCompactSupport cutoff)
    (radial : ∀ first second : Spatial,‖first‖=‖second‖ → cutoff first=cutoff second)
    (outer : Spatial → ℝ) (smooth : ContDiff ℝ ∞ outer) (compact : HasCompactSupport outer)
    (plateau : ∀ point∈tsupport cutoff,outer point=1) (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ constant : ℝ,0≤constant ∧ ∀ (packet : StartupOriginalUnitNormPacket parameters length radius)
      (data : StartupCompactSpatialEquation rank (tsupport cutoff)),
      base 3 rank openUnitDisk (fun _ => 0) data.field=startupCutoffL2 cutoff cutoffSmooth cutoffCompact packet.field.field →
      base 3 rank openUnitDisk (fun _ => 0) (data.tensor index.1 index.2)=
        startupCutoffL2 cutoff cutoffSmooth cutoffCompact (packet.tensorFamily radiusNonnegative index.1 index.2).field →
      ‖startupActualRankTensorRemainder data outer smooth compact
        (fun first second => StartupRankOperator.principalTensor (unitDiskAdmissible parameters) rank packet.coefficient.data
          (packet.coefficient.coherent radiusNonnegative) (packet.coefficient.inverseCoherent radiusNonnegative) first second) index‖≤
        epsilon*originalGradeNorm rank packet.core+
          constant*(Grad.OriginalCartesianTameEstimate.originalCellNorm parameters rank packet.core+
            OriginalUnitRankState.budget rank packet.coefficient*originalGradeNorm 0 packet.core+sourcePayment rank scale packet) := by
  let highCut := ‖startupCutoffMixedGraph cutoff cutoffSmooth cutoffCompact rank‖
  let baseCut := ‖startupCutoffMixedGraph cutoff cutoffSmooth cutoffCompact 0‖
  have highCut0 : 0≤highCut := norm_nonneg (startupCutoffMixedGraph cutoff cutoffSmooth cutoffCompact rank)
  have baseCut0 : 0≤baseCut := norm_nonneg (startupCutoffMixedGraph cutoff cutoffSmooth cutoffCompact 0)
  let delta := epsilon/(highCut+1)
  have deltaPositive : 0<delta := div_pos positive (by positivity)
  let certificate := OriginalUnitRankState.compactTensor_remainder_bound parameters length radius radiusNonnegative rank index
    (isClosed_tsupport cutoff) outer smooth compact plateau delta deltaPositive
  let cost := certificate.choose
  have cost0 : 0≤cost := certificate.choose_spec.1
  refine ⟨cost*(highCut+baseCut+1),mul_nonneg cost0 (by positivity),?_⟩
  intro packet data fieldSame tensorSame
  have fieldIdentical : base 3 rank openUnitDisk (fun _ => 0) data.field=
      originalSourceFieldLinear parameters (packet.cutoffCore cutoff cutoffSmooth cutoffCompact) := by
    rw [fieldSame,packet.fieldSame,packet.cutoffCore_same]
  have tensorIdentical : base 3 rank openUnitDisk (fun _ => 0) (data.tensor index.1 index.2)=
      originalSourceFieldLinear parameters
        (packet.cutoffPrincipalCore cutoff cutoffSmooth cutoffCompact radiusNonnegative index.1 index.2+
          packet.cutoffKnownTensorCore cutoff cutoffSmooth cutoffCompact index.1 index.2) :=
    tensorSame.trans (packet.cutoffTensor_same cutoff cutoffSmooth cutoffCompact radiusNonnegative radial index.1 index.2)
  have original := certificate.choose_spec.2 packet.coefficient
    (packet.cutoffCore cutoff cutoffSmooth cutoffCompact)
    (packet.cutoffPrincipalCore cutoff cutoffSmooth cutoffCompact radiusNonnegative index.1 index.2)
    (packet.cutoffKnownTensorCore cutoff cutoffSmooth cutoffCompact index.1 index.2) data fieldIdentical tensorIdentical
    (packet.cutoffPrincipalCore_same cutoff cutoffSmooth cutoffCompact radiusNonnegative index.1 index.2)
  have inputBound : originalGradeNorm rank (packet.cutoffCore cutoff cutoffSmooth cutoffCompact)≤highCut*originalGradeNorm rank packet.core :=
    startupOriginalCutoff_core_bound parameters cutoff cutoffSmooth cutoffCompact rank packet.core _
      (packet.cutoffCore_same cutoff cutoffSmooth cutoffCompact)
  have baseBound : originalGradeNorm 0 (packet.cutoffCore cutoff cutoffSmooth cutoffCompact)≤baseCut*originalGradeNorm 0 packet.core :=
    startupOriginalCutoff_core_bound parameters cutoff cutoffSmooth cutoffCompact 0 packet.core _
      (packet.cutoffCore_same cutoff cutoffSmooth cutoffCompact)
  have knownBound : originalGradeNorm rank (packet.cutoffKnownTensorCore cutoff cutoffSmooth cutoffCompact index.1 index.2)≤
      highCut*sourcePayment rank scale packet := by
    have cutBound := startupOriginalCutoff_core_bound parameters cutoff cutoffSmooth cutoffCompact rank
      (packet.knownTensorCore index.1 index.2) (packet.cutoffKnownTensorCore cutoff cutoffSmooth cutoffCompact index.1 index.2)
      (packet.cutoffKnownTensorCore_same cutoff cutoffSmooth cutoffCompact index.1 index.2)
    exact cutBound.trans (mul_le_mul_of_nonneg_left (knownTensor_paid rank scale packet index.1 index.2) highCut0)
  let remainder := Grad.OriginalCartesianTameEstimate.originalCellNorm parameters rank packet.core+
    OriginalUnitRankState.budget rank packet.coefficient*originalGradeNorm 0 packet.core+sourcePayment rank scale packet
  have sourceDominated : sourcePayment rank scale packet≤remainder :=
    startupOriginalRemainderPayment_source parameters rank (fun p : StartupOriginalUnitNormPacket parameters length radius => p.coefficient) (fun p => p.core) (sourcePayment rank scale) packet
  have cell0 : 0≤Grad.OriginalCartesianTameEstimate.originalCellNorm parameters rank packet.core := Real.sqrt_nonneg _
  have baseDominated : OriginalUnitRankState.budget rank packet.coefficient*originalGradeNorm 0 packet.core≤remainder := by
    dsimp only [remainder]
    linarith only [cell0,sourcePayment_nonnegative rank scale packet]
  have remainder0 : 0≤remainder := (sourcePayment_nonnegative rank scale packet).trans sourceDominated
  have budget0 := OriginalUnitRankState.budget_nonnegative rank packet.coefficient
  have knownPaid := knownBound.trans (mul_le_mul_of_nonneg_left sourceDominated highCut0)
  have basePaid : OriginalUnitRankState.budget rank packet.coefficient*originalGradeNorm 0 (packet.cutoffCore cutoff cutoffSmooth cutoffCompact)≤
      baseCut*remainder := by
    calc
      _ ≤ OriginalUnitRankState.budget rank packet.coefficient*(baseCut*originalGradeNorm 0 packet.core) := mul_le_mul_of_nonneg_left baseBound budget0
      _ = baseCut*(OriginalUnitRankState.budget rank packet.coefficient*originalGradeNorm 0 packet.core) := by ring
      _ ≤ baseCut*remainder := mul_le_mul_of_nonneg_left baseDominated baseCut0
  have lowerPaid : originalGradeNorm rank (packet.cutoffKnownTensorCore cutoff cutoffSmooth cutoffCompact index.1 index.2)+
      OriginalUnitRankState.budget rank packet.coefficient*originalGradeNorm 0 (packet.cutoffCore cutoff cutoffSmooth cutoffCompact)≤
      (highCut+baseCut+1)*remainder := by nlinarith only [knownPaid,basePaid,remainder0]
  have allocated : delta*highCut≤epsilon := by
    have exactDelta : delta*(highCut+1)=epsilon := div_mul_cancel₀ epsilon (by positivity)
    nlinarith only [exactDelta,deltaPositive]
  have highPaid : delta*originalGradeNorm rank (packet.cutoffCore cutoff cutoffSmooth cutoffCompact)≤epsilon*originalGradeNorm rank packet.core :=
    (mul_le_mul_of_nonneg_left inputBound deltaPositive.le).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right allocated (originalGradeNorm_nonnegative rank packet.core))
  have result := original.trans (add_le_add highPaid (mul_le_mul_of_nonneg_left lowerPaid cost0))
  simpa only [mul_assoc] using result

end Grad.CartesianStartup.StartupOriginalUnitNormPacket
