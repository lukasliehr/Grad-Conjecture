import AKDW29PacketPhaseCutoffBesselNorm
import AKDW31PacketCutoffTensorNorm
import AKDP83GenericCompactPlanarEstimate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
open Set
open scoped ContDiff
namespace Grad.CartesianStartup.StartupOriginalUnitNormPacket
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets Grad.NonlinearProduct
open Grad.OriginalCoreRealization Grad.SourceCollarCoefficients Grad.WeightedJets.ZeroExtension Grad.TensorBootstrap
open Grad.OriginalCartesianTameEstimate
open Grad.GaugeCoefficients.Physical.Allocation

/-- All actual phase/cutoff/Bessel and second-tensor remainders close the
compact planar estimate on the SAME w, with one common principal ball. -/
theorem actualCompact_planar_bound {State : Type*} (parameters : PhaseParameters) (length radius : ℝ)
    (radiusNonnegative : 0≤radius) (rank : ℕ) (scale : ℝ)
    (packets : State → StartupOriginalUnitNormPacket parameters length radius)
    (cutoff : Spatial → ℝ) (cutoffSmooth : ContDiff ℝ ∞ cutoff) (cutoffCompact : HasCompactSupport cutoff)
    (radial : ∀ first second : Spatial,‖first‖=‖second‖ → cutoff first=cutoff second)
    (localizer : TestLocalizer openUnitDisk (tsupport cutoff))
    (outer : Spatial → ℝ) (smooth : ContDiff ℝ ∞ outer) (compact : HasCompactSupport outer)
    (plateau : ∀ point∈tsupport cutoff,outer point=1)
    (small : ∀ state,physicalBudget parameters (packets state).coefficient.field (packets state).coefficient.rho
      (packets state).coefficient.epsilon 10<originalUnitPrincipalRadius parameters length radius outer smooth compact)
    (data : State → StartupCompactSpatialEquation (rank+2) (tsupport cutoff))
    (fieldSame : ∀ state,base 3 (rank+2) openUnitDisk (fun _ => 0) (data state).field=
      startupCutoffL2 cutoff cutoffSmooth cutoffCompact (packets state).field.field)
    (zeroSame : ∀ state,base 3 (rank+2) openUnitDisk (fun _ => 0) (data state).zeroth=
      startupCutoffEquationZeroth cutoff cutoffSmooth cutoffCompact (packets state).field.field
        (startupSignedPhaseZeroth parameters one_ne_zero startupOriginalUnitScale (packets state).field
          ((packets state).tensorFamily radiusNonnegative) ((packets state).fluxFamily radiusNonnegative scale) 0)
        (fun first second => ((packets state).tensorFamily radiusNonnegative first second).field)
        (startupSignedPhaseFlux parameters one_ne_zero startupOriginalUnitScale (packets state).field
          ((packets state).tensorFamily radiusNonnegative) ((packets state).fluxFamily radiusNonnegative scale) 0))
    (tensorSame : ∀ state first second,base 3 (rank+2) openUnitDisk (fun _ => 0) ((data state).tensor first second)=
      startupCutoffL2 cutoff cutoffSmooth cutoffCompact ((packets state).tensorFamily radiusNonnegative first second).field)
    (fluxSame : ∀ state direction,base 3 (rank+2) openUnitDisk (fun _ => 0) ((data state).flux direction)=
      startupCutoffEquationFlux cutoff cutoffSmooth cutoffCompact (packets state).field.field
        (fun first second => ((packets state).tensorFamily radiusNonnegative first second).field)
        (startupSignedPhaseFlux parameters one_ne_zero startupOriginalUnitScale (packets state).field
          ((packets state).tensorFamily radiusNonnegative) ((packets state).fluxFamily radiusNonnegative scale) 0) direction)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ constant : ℝ,0≤constant ∧ ∀ state (image : ACore parameters 3),
      originalSourceFieldLinear parameters image=
        startupCutoffL2 cutoff cutoffSmooth cutoffCompact (originalSourceFieldLinear parameters (packets state).core) →
      originalPlanarNorm parameters (rank+2) image≤epsilon*originalGradeNorm (rank+2) (packets state).core+
        constant*low parameters length radius (rank+2) scale (packets state) := by
  let operators := fun state first second => StartupRankOperator.principalTensor (unitDiskAdmissible parameters) (rank+2)
    (packets state).coefficient.data ((packets state).coefficient.coherent radiusNonnegative)
      ((packets state).coefficient.inverseCoherent radiusNonnegative) first second
  have principalSmall (state : State) : ‖startupOrderedSecondSum (rank+2)
      (fun index => (operators state index.1 index.2).localizedCoarse outer smooth compact)‖≤(1/8 : ℝ) :=
    ((packets state).coefficient.localized_principal_oneEighth radiusNonnegative outer smooth compact (small state) (rank+2)).le
  have bessel := compactBessel_lower parameters length radius radiusNonnegative scale cutoff cutoffSmooth cutoffCompact
    packets rank localizer data fieldSame zeroSame fluxSame
  have tensor (index : TensorIndex) (eta : ℝ) (etaPositive : 0<eta) :
      ∃ constant : ℝ,0≤constant ∧ ∀ state,
        ‖startupActualRankTensorRemainder (data state) outer smooth compact (operators state) index‖≤
          eta*high parameters length radius (rank+2) (packets state)+constant*low parameters length radius (rank+2) scale (packets state) := by
    let result := cutoffTensor_remainder_bound parameters length radius radiusNonnegative (rank+2) scale index
      cutoff cutoffSmooth cutoffCompact radial outer smooth compact plateau eta etaPositive
    refine ⟨result.choose,result.choose_spec.1,?_⟩
    intro state
    exact result.choose_spec.2 (packets state) (data state) (fieldSame state) (tensorSame state index.1 index.2)
  have lower : StartupAdjustableSpatialGraph (rank+1)
      (fun state => base 3 (rank+2) openUnitDisk (fun _ => 0) (data state).field)
      (fun state => high parameters length radius (rank+2) (packets state))
      (fun state => low parameters length radius (rank+2) scale (packets state)) :=
    ((StartupAdjustableSpatialGraph.cutoffGraph cutoff cutoffSmooth cutoffCompact
      (field_lower parameters length radius (rank+2) scale (rank+1) (by omega))
      (high_nonnegative parameters length radius (rank+2))).reindex packets).congr (fun state => (fieldSame state).symm)
  have result := startupGenericCompactPlanar_estimate (rank+2) (isClosed_tsupport cutoff) localizer outer smooth compact data operators principalSmall
    (fun state => high parameters length radius (rank+2) (packets state))
    (fun state => low parameters length radius (rank+2) scale (packets state))
    (fun state => high_nonnegative parameters length radius (rank+2) (packets state)) bessel tensor
    (by simpa only [show rank+2-1=rank+1 by omega] using lower) epsilon positive
  refine ⟨result.choose,result.choose_spec.1,?_⟩
  intro state image imageSame
  have graphSame : base 3 (rank+2) openUnitDisk (fun _ => 0) (data state).field=
      (Grad.ActualOriginalSourceMoments.originalSourceMoments parameters image).field := by
    rw [fieldSame,(packets state).fieldSame]
    exact imageSame.symm
  rw [startupOriginalPlanarNorm_eq_graph parameters image (data state).field graphSame]
  exact result.choose_spec.2 state

end Grad.CartesianStartup.StartupOriginalUnitNormPacket
