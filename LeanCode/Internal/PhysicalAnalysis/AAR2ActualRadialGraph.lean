import AAR1ActualBulkRecovery
import ASG37ActualWeakRadialRepresentative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem finiteEnergy_mode (lower length : ℝ) (positive : 0 < lower)
    (core : HighAnnularMode →₀ complexSmoothRadialCore 1) (mode : HighAnnularMode) :
    finiteAnnularEnergyCore lower length positive core mode =
      annularModeEnergyCore lower length positive mode.val.1 mode.val.2 (core mode) := by
  classical
  rw [finiteAnnularEnergyCore, Finsupp.lsum_apply, Finsupp.sum, lp.coeFn_sum, Finset.sum_apply]
  change (∑ other ∈ core.support,
    (lp.single 2 other (annularModeEnergyCore lower length positive other.val.1 other.val.2 (core other)) :
      AnnularEnergyAmbient lower) mode) = _
  simp only [lp.single_apply, Pi.single_apply]
  rw [Finset.sum_eq_single mode]
  · simp only [ite_true]
  · intro other _ different
    exact if_neg (Ne.symm different)
  · intro missing
    rw [Finsupp.notMem_support_iff.mp missing, map_zero]
    simp

theorem annularEnergyDerivative_core_mode (lower length : ℝ) (positive : 0 < lower)
    (core : HighAnnularMode →₀ complexSmoothRadialCore 1) (mode : HighAnnularMode) :
    annularEnergyDerivative lower length positive
        (annularEnergyCoreInto lower length positive core) mode =
      weightedCurveComplex 1 lower (core mode).val.2 := by
  change annularModeDerivative lower (finiteAnnularEnergyCore lower length positive core mode) = _
  rw [finiteEnergy_mode]
  rfl

theorem annularEnergyMass_core_mode (lower length : ℝ) (positive : 0 < lower)
    (core : HighAnnularMode →₀ complexSmoothRadialCore 1) (mode : HighAnnularMode) :
    annularEnergyMass lower length positive
        (annularEnergyCoreInto lower length positive core) mode =
      weightedCurveComplex 1 lower
        (continuousCurveWeight 1 (annularPotentialWeight lower length positive mode.val.1 mode.val.2)
          (core mode).val.1) := by
  change annularModeMass lower (finiteAnnularEnergyCore lower length positive core mode) = _
  rw [finiteEnergy_mode]
  rfl

theorem annularEnergyValue_core_mode (lower length : ℝ) (positive : 0 < lower)
    (core : HighAnnularMode →₀ complexSmoothRadialCore 1) (mode : HighAnnularMode) :
    annularEnergyValue lower length positive
        (annularEnergyCoreInto lower length positive core) mode =
      weightedCurveComplex 1 lower (core mode).val.1 := by
  change annularValueMassMap lower length positive mode
    (annularEnergyMass lower length positive (annularEnergyCoreInto lower length positive core) mode) = _
  rw [annularEnergyMass_core_mode]
  change scalarRadialMap lower (annularValueMassRatio lower length positive mode) (1 / 3)
    (annularValueMassRatio_bound lower length positive mode)
      (weightedCurveComplex 1 lower
        (continuousCurveWeight 1 (annularPotentialWeight lower length positive mode.val.1 mode.val.2)
          (core mode).val.1)) = _
  rw [scalarRadialMap_weightedCurve]
  congr 1
  apply ContinuousMap.ext
  intro radius
  change (annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius)⁻¹ •
    (annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius • (core mode).val.1 radius) = _
  rw [smul_smul, inv_mul_cancel₀ (annularPotentialWeight_pos lower length positive mode radius).ne', one_smul]

def annularModeWeightedGraph (lower length : ℝ) (positive : 0 < lower) (mode : HighAnnularMode) :
    annularEnergySpace lower length positive →L[ℝ] WeightedRadialAmbient 1 lower :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => RadialL2 1 lower)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![
      ((lp.evalCLM ℂ (fun _ : HighAnnularMode => RadialL2 1 lower) 2 mode).comp
        (annularEnergyValue lower length positive)).restrictScalars ℝ,
      ((lp.evalCLM ℂ (fun _ : HighAnnularMode => RadialL2 1 lower) 2 mode).comp
        (annularEnergyDerivative lower length positive)).restrictScalars ℝ])

theorem annularModeWeightedGraph_core (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (core : HighAnnularMode →₀ complexSmoothRadialCore 1) :
    annularModeWeightedGraph lower length positive mode
        (annularEnergyCoreInto lower length positive core) =
      weightedRadialCore 1 lower (complexCoreToAccepted 1 (core mode)) := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · change annularEnergyValue lower length positive
      (annularEnergyCoreInto lower length positive core) mode = _
    exact annularEnergyValue_core_mode lower length positive core mode
  · change annularEnergyDerivative lower length positive
      (annularEnergyCoreInto lower length positive core) mode = _
    exact annularEnergyDerivative_core_mode lower length positive core mode

/-- Every completed energy element has the genuine radial derivative graph;
no extra regularity or independent endpoint is assumed. -/
theorem annularModeWeightedGraph_mem (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (field : annularEnergySpace lower length positive) :
    annularModeWeightedGraph lower length positive mode field ∈ WeightedRadialH1 1 lower := by
  apply isClosed_property (annularEnergyCoreInto_denseRange lower length positive)
    ((LinearMap.range (weightedRadialCore 1 lower)).isClosed_topologicalClosure.preimage
      (annularModeWeightedGraph lower length positive mode).continuous) _ field
  intro core
  rw [annularModeWeightedGraph_core]
  exact Submodule.le_topologicalClosure _ ⟨complexCoreToAccepted 1 (core mode), rfl⟩

def annularModeRadialH1 (lower length : ℝ) (positive : 0 < lower) (mode : HighAnnularMode) :
    annularEnergySpace lower length positive →L[ℝ] WeightedRadialH1 1 lower :=
  (annularModeWeightedGraph lower length positive mode).codRestrict _
    (annularModeWeightedGraph_mem lower length positive mode)

theorem annularModeRadialH1_value (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (field : annularEnergySpace lower length positive) :
    weightedRadialCoordinate 1 lower 0 (annularModeRadialH1 lower length positive mode field) =
      annularEnergyValue lower length positive field mode := rfl

theorem annularModeRadialH1_derivative (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (field : annularEnergySpace lower length positive) :
    weightedRadialCoordinate 1 lower 1 (annularModeRadialH1 lower length positive mode field) =
      annularEnergyDerivative lower length positive field mode := rfl

theorem annularModeRadialH1_core (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (core : HighAnnularMode →₀ complexSmoothRadialCore 1) :
    annularModeRadialH1 lower length positive mode (annularEnergyCoreInto lower length positive core) =
      weightedRadialCoreInto 1 lower (complexCoreToAccepted 1 (core mode)) :=
  Subtype.ext (annularModeWeightedGraph_core lower length positive mode core)

theorem annularModeRadialH1_weak (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (mode : HighAnnularMode) (field : annularEnergySpace lower length positive) :
    CollarWeakDerivative lower
      (collarH1Coordinate (ComplexEuclidean 1) lower 0
        (weightedToOrdinary 1 lower positive bounded (annularModeRadialH1 lower length positive mode field)))
      (collarH1Coordinate (ComplexEuclidean 1) lower 1
        (weightedToOrdinary 1 lower positive bounded (annularModeRadialH1 lower length positive mode field))) :=
  weightedRadial_weak 1 lower positive bounded _

end Grad.AnnularReconstruction
