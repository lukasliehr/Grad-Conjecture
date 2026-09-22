import AKR25EveryLiteralTupleGraphImage

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.PhaseAlgebra
open Grad.AnnularOriginalHigh Grad.AnnularOriginalLow Grad.AnnularLowEnergy Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.WeightedTrace

open Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger

open Grad.AnnularCurrentLow Grad.AnnularCurrentSource Grad.AnnularHighTilt

open Grad.AnnularFullGraph

open Grad.AnnularHighRadial Grad.AnnularTiltedReference Grad.AnnularOmegaGraph Grad.CircularHighRegularity

theorem ordinaryRadialStorage_faithful (lower : ℝ) (positive : 0 < lower) :
    Function.Injective (radialOrdinary 1 lower positive) :=
  collarScalar_injective_of_pos lower
    ⟨reciprocalRadialWeight lower (fun _ => 1),reciprocalRadialWeight_continuous lower positive _ continuous_const⟩
    (fun radius => by
      change 0 < 1 / Real.sqrt (max lower radius)
      exact div_pos zero_lt_one (Real.sqrt_pos.mpr (positive.trans_le (le_max_left _ _))))

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (lengthPositive : 0 < length)

/-- Physical p and xi determine the entire original retained graph,
including the forced weak derivatives, energy mass and endpoints. -/
theorem sameCoupledCoefficients_faithful
    (first second : CoupledSpace lower length positive lengthPositive)
    (xi : ∀ radius : Icc lower (1 : ℝ), ∀ mode,
      sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive first 0 radius mode =
        sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive second 0 radius mode)
    (x : ∀ radius : Icc lower (1 : ℝ), ∀ mode,
      sameCoupledXCoefficient parameters lower length positive bounded lengthPositive first 0 radius mode =
        sameCoupledXCoefficient parameters lower length positive bounded lengthPositive second 0 radius mode) : first = second := by
  have highXi : first.ofLp.1.ofLp.1 = second.ofLp.1.ofLp.1 := by
    have decoded : bEnergyDecode lower length positive first.ofLp.1.ofLp.1 =
        bEnergyDecode lower length positive second.ofLp.1.ofLp.1 := by
      apply annularEnergyValue_injective lower length positive bounded
      apply lp.ext
      funext mode
      apply ordinaryRadialStorage_faithful lower positive
      apply collarScalar_injective_of_pos lower (rawHighPhase parameters lower positive mode.val.2)
        (rawHighPhase_positive parameters lower positive mode.val.2)
      rw [← rawHighXiSection_bulk,← rawHighXiSection_bulk]
      congr 1
      apply ContinuousMap.ext
      intro radius
      have equal := xi radius mode.val
      simpa only [sameCoupledXiCoefficient_high] using equal
    have equality := congrArg (bEnergyNormalize lower length positive) decoded
    simpa only [bEnergyNormalize_decode] using equality
  have highX : first.ofLp.1.ofLp.2 = second.ofLp.1.ofLp.2 := by
    apply annularOmegaGraph_value_injective lower length positive bounded lengthPositive
    apply lp.ext
    funext mode
    apply ordinaryRadialStorage_faithful lower positive
    apply collarScalar_injective_of_pos lower (rawHighPhase parameters lower positive mode.val.2)
      (rawHighPhase_positive parameters lower positive mode.val.2)
    rw [← rawHighXSection_bulk,← rawHighXSection_bulk]
    congr 1
    apply ContinuousMap.ext
    intro radius
    have equal := x radius mode.val
    simpa only [sameCoupledXCoefficient_high] using equal
  have low : first.ofLp.2 = second.ofLp.2 := by
    apply lowPhysicalSection_injective parameters lower length positive bounded
    funext index
    apply ContinuousMap.ext
    intro radius
    rcases index with ⟨row,mode⟩
    have small := mode.property
    have large : ¬3 ≤ |mode.val.1| := by omega
    fin_cases row
    · change lowPhysicalSection parameters lower length positive bounded first.ofLp.2 (0,mode) radius =
        lowPhysicalSection parameters lower length positive bounded second.ofLp.2 (0,mode) radius
      have equal := xi radius mode.val
      simpa only [sameCoupledXiCoefficient,dif_neg large,dif_pos small,pow_zero,Complex.ofReal_one,one_smul,Subtype.coe_eta] using equal
    · change lowPhysicalSection parameters lower length positive bounded first.ofLp.2 (1,mode) radius =
        lowPhysicalSection parameters lower length positive bounded second.ofLp.2 (1,mode) radius
      have equal := x radius mode.val
      simpa only [sameCoupledXCoefficient,dif_neg large,dif_pos small,pow_zero,Complex.ofReal_one,one_smul,Subtype.coe_eta] using equal
  apply (WithLp.equiv 2 _).injective
  exact Prod.ext ((WithLp.equiv 2 _).injective (Prod.ext highXi highX)) low

end Grad.AnnularOriginalCoreRealization
