import AKR2FullOriginalTupleSourceGraphs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore Grad.AnnularReconstruction Grad.AnnularVariational Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The actual derivative/potential/outer energy coordinates of a genuine
radial H1 mode. The outer value is its forced trace. -/
def radialGraphEnergyMode (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : HighAnnularMode) : WeightedRadialH1 1 lower →L[ℝ] AnnularModeEnergyAmbient lower :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    ((weightedRadialCoordinate 1 lower 1).prod
      ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
        ((((collarScalar 1 lower (annularPotentialWeight lower length positive mode.val.1 mode.val.2)).restrictScalars ℝ).comp
          (weightedRadialCoordinate 1 lower 0)).prod
          (Real.sqrt 2 • weightedRadialTrace 1 lower positive bounded 1))))

theorem radialGraphEnergyMode_core (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : HighAnnularMode) (core : SmoothRadialCore 1) :
    radialGraphEnergyMode lower length positive bounded mode (weightedRadialCoreInto 1 lower core) =
      annularModeEnergyCore lower length positive mode.val.1 mode.val.2 (acceptedCoreToComplex 1 core) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
  apply Prod.ext
  · exact weightedRadialCoordinate_core_one 1 lower core
  · apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
    apply Prod.ext
    · change collarScalar 1 lower (annularPotentialWeight lower length positive mode.val.1 mode.val.2)
        (weightedRadialCoordinate 1 lower 0 (weightedRadialCoreInto 1 lower core)) = _
      rw [weightedRadialCoordinate_core_zero]
      exact collarScalar_weightedCurve lower _ core.val.val.1
    · change Real.sqrt 2 • weightedRadialTrace 1 lower positive bounded 1 (weightedRadialCoreInto 1 lower core) = _
      rw [weightedRadialTrace_core]
      rfl

def radialGraphEnergySingle (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : HighAnnularMode) : WeightedRadialH1 1 lower →L[ℝ] AnnularEnergyAmbient lower :=
  (lp.singleContinuousLinearMap ℝ (fun _ : HighAnnularMode => AnnularModeEnergyAmbient lower) 2 mode).comp
    (radialGraphEnergyMode lower length positive bounded mode)

/-- Genuine H1 modes lie in the closure of the actual original smooth
energy core; no independent energy graph predicate is substituted. -/
theorem radialGraphEnergySingle_mem (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : HighAnnularMode) (field : WeightedRadialH1 1 lower) :
    radialGraphEnergySingle lower length positive bounded mode field ∈ annularEnergySpace lower length positive := by
  apply isClosed_property (weightedRadialCoreInto_denseRange 1 lower)
    ((LinearMap.range (finiteAnnularEnergyCore lower length positive)).isClosed_topologicalClosure.preimage
      (radialGraphEnergySingle lower length positive bounded mode).continuous) _ field
  intro core
  apply Submodule.le_topologicalClosure
  refine ⟨Finsupp.single mode (acceptedCoreToComplex 1 core), ?_⟩
  rw [finiteAnnularEnergyCore,Finsupp.lsum_single]
  change (lp.single 2 mode (annularModeEnergyCore lower length positive mode.val.1 mode.val.2
    (acceptedCoreToComplex 1 core)) : AnnularEnergyAmbient lower) = (lp.single 2 mode
    (radialGraphEnergyMode lower length positive bounded mode (weightedRadialCoreInto 1 lower core)) : AnnularEnergyAmbient lower)
  rw [radialGraphEnergyMode_core]

def radialGraphEnergy (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : HighAnnularMode) : WeightedRadialH1 1 lower →L[ℝ] annularEnergySpace lower length positive :=
  (radialGraphEnergySingle lower length positive bounded mode).codRestrict
    ((annularEnergySpace lower length positive).restrictScalars ℝ)
    (radialGraphEnergySingle_mem lower length positive bounded mode)

theorem radialGraphEnergy_core (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : HighAnnularMode) (core : SmoothRadialCore 1) :
    radialGraphEnergy lower length positive bounded mode (weightedRadialCoreInto 1 lower core) =
      annularEnergyCoreInto lower length positive (Finsupp.single mode (acceptedCoreToComplex 1 core)) := by
  apply Subtype.ext
  change (lp.single 2 mode (radialGraphEnergyMode lower length positive bounded mode
    (weightedRadialCoreInto 1 lower core)) : AnnularEnergyAmbient lower) = _
  rw [radialGraphEnergyMode_core]
  rw [annularEnergyCoreInto]
  change _ = finiteAnnularEnergyCore lower length positive (Finsupp.single mode (acceptedCoreToComplex 1 core))
  rw [finiteAnnularEnergyCore,Finsupp.lsum_single]
  rfl

end Grad.AnnularOriginalCoreRealization
