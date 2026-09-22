import AKDW7OriginalUnitNativeSpatialEquation
import AKDS34OriginalUnitLedgerFidelity
import AKCX52SameClosedNativeInduction
import AKCX44ActualNativeLowerSpatialGraphs
import AKDW16ActualOriginalKnownSourceCores
import AKDS8ActualNativeXiWeakRecoveryBound
import AKBT12SameNativeERRowRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000
open Set Filter MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.CartesianState Grad.WeightedJets
open Grad.AnalyticWeights.Calculus Grad.SpatialDilation Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Ledger

open Grad.OriginalCoreRealization Grad.OriginalVectorCoreRecovery Grad.NonlinearProduct
open Grad.ActualOriginalSourceMoments Grad.ActualScaledNativeCoefficients
open Grad.QuotientProjection Grad.FlatSourceProjection

/-- Literal known-row core identities at unit coordinates; physical L is retained. -/
theorem startupOriginalUnitRows_knownBases (parameters : PhaseParameters) (length : ℝ)
    (source : SmoothQuotient parameters) (covariant force cofactor : StartupMoments 3) :
    let rows := nativeERRows covariant force cofactor
      ((originalSourceMoments parameters (cartesianSourceVector source)).dilate startupOriginalUnitScale)
      (((originalSourceMoments parameters (source 3)).dilate startupOriginalUnitScale).smul (length : ℂ)⁻¹)
      (((originalSourceMoments parameters (source 2)).dilate startupOriginalUnitScale).smul ((1 : ℂ)/(length : ℂ)));
    originalSourceFieldLinear parameters (startupOriginalKnownForceCore parameters source)=rows.knownForce.field ∧
    originalSourceFieldLinear parameters (startupOriginalKnownScalarCore parameters length source 3)=rows.knownThird.field ∧
    originalSourceFieldLinear parameters (startupOriginalKnownScalarCore parameters length source 2)=rows.determinant.field := by
  have dilation {dimension : ℕ} (field : StartupL2 dimension) : startupMomentDilation startupOriginalUnitScale field=field :=
    actualRecovery_dilation_one field
  refine ⟨?_,?_,?_⟩
  · change originalSourceFieldLinear parameters (startupOriginalKnownForceCore parameters source)=
      startupGenuineQradKernel (startupMomentDilation startupOriginalUnitScale (originalSourceMoments parameters (cartesianSourceVector source)).field)
    rw [dilation]
    exact startupOriginalKnownForceCore_same parameters source
  · change originalSourceFieldLinear parameters (startupOriginalKnownScalarCore parameters length source 3)=
      (length : ℂ)⁻¹ • startupMomentDilation startupOriginalUnitScale (originalSourceMoments parameters (source 3)).field
    rw [dilation]
    exact startupOriginalKnownScalarCore_same parameters length source 3
  · change originalSourceFieldLinear parameters (startupOriginalKnownScalarCore parameters length source 2)=
      ((1 : ℂ)/(length : ℂ)) • startupMomentDilation startupOriginalUnitScale (originalSourceMoments parameters (source 2)).field
    rw [dilation,one_div]
    exact startupOriginalKnownScalarCore_same parameters length source 2

end Grad.CartesianStartup
