import AAR2ActualRadialGraph

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

theorem annularValueMassMap_injective (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) : Function.Injective (annularValueMassMap lower length positive mode) := by
  intro first second same
  apply Lp.ext
  filter_upwards [scalarRadialMap_ae lower (annularValueMassRatio lower length positive mode) (1 / 3)
      (annularValueMassRatio_bound lower length positive mode) first,
    scalarRadialMap_ae lower (annularValueMassRatio lower length positive mode) (1 / 3)
      (annularValueMassRatio_bound lower length positive mode) second] with radius firstLaw secondLaw
  have pointwise := congrArg (fun field : RadialL2 1 lower => field radius) same
  change scalarRadialMap lower (annularValueMassRatio lower length positive mode) (1 / 3)
      (annularValueMassRatio_bound lower length positive mode) first radius =
    scalarRadialMap lower (annularValueMassRatio lower length positive mode) (1 / 3)
      (annularValueMassRatio_bound lower length positive mode) second radius at pointwise
  rw [firstLaw, secondLaw] at pointwise
  have rescaled := congrArg (fun value : ComplexEuclidean 1 =>
    annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius • value) pointwise
  change annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius •
      ((annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius)⁻¹ • first radius) =
    annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius •
      ((annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius)⁻¹ • second radius) at rescaled
  simpa only [smul_smul,
    mul_inv_cancel₀ (annularPotentialWeight_pos lower length positive mode radius).ne', one_smul] using rescaled

theorem annularEnergyOuter_core_mode (lower length : ℝ) (positive : 0 < lower)
    (core : HighAnnularMode →₀ complexSmoothRadialCore 1) (mode : HighAnnularMode) :
    annularEnergyOuter lower length positive
        (annularEnergyCoreInto lower length positive core) mode =
      (Real.sqrt 2 : ℂ) • (core mode).val.1 1 := by
  change annularModeOuter lower (finiteAnnularEnergyCore lower length positive core mode) = _
  rw [finiteEnergy_mode]
  rfl

/-- The stored outer coordinate is the endpoint of the same genuine radial
representative. It cannot be chosen independently of the bulk field. -/
theorem annularEnergyOuter_eq_trace (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (mode : HighAnnularMode) (field : annularEnergySpace lower length positive) :
    annularEnergyOuter lower length positive field mode =
      (Real.sqrt 2 : ℂ) • weightedRadialTrace 1 lower positive bounded 1
        (annularModeRadialH1 lower length positive mode field) := by
  apply isClosed_property (annularEnergyCoreInto_denseRange lower length positive)
    (isClosed_eq
      (((lp.evalCLM ℂ (fun _ : HighAnnularMode => ComplexEuclidean 1) 2 mode).comp
        (annularEnergyOuter lower length positive)).continuous)
      (((weightedRadialTrace 1 lower positive bounded 1).continuous.comp
        (annularModeRadialH1 lower length positive mode).continuous).const_smul (Real.sqrt 2 : ℂ))) _ field
  intro core
  change annularEnergyOuter lower length positive (annularEnergyCoreInto lower length positive core) mode =
    (Real.sqrt 2 : ℂ) • weightedRadialTrace 1 lower positive bounded 1
      (annularModeRadialH1 lower length positive mode (annularEnergyCoreInto lower length positive core))
  rw [annularEnergyOuter_core_mode, annularModeRadialH1_core, weightedRadialTrace_core]
  rfl

/-- The literal energy completion is faithfully realized by its conjugated
bulk value: mass, derivative and outer value are all determined by it. -/
theorem annularEnergyValue_injective (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) : Function.Injective (annularEnergyValue lower length positive) := by
  intro first second same
  have graphs (mode : HighAnnularMode) :
      annularModeRadialH1 lower length positive mode first =
        annularModeRadialH1 lower length positive mode second := by
    apply weightedRadial_value_injective 1 lower positive bounded.le
    rw [annularModeRadialH1_value, annularModeRadialH1_value]
    exact congrArg (fun field : AnnularBulk lower => field mode) same
  have derivatives (mode : HighAnnularMode) :
      annularEnergyDerivative lower length positive first mode =
        annularEnergyDerivative lower length positive second mode :=
    congrArg (weightedRadialCoordinate 1 lower 1) (graphs mode)
  have masses (mode : HighAnnularMode) :
      annularEnergyMass lower length positive first mode =
        annularEnergyMass lower length positive second mode := by
    apply annularValueMassMap_injective lower length positive mode
    exact congrArg (fun field : AnnularBulk lower => field mode) same
  have outers (mode : HighAnnularMode) :
      annularEnergyOuter lower length positive first mode =
        annularEnergyOuter lower length positive second mode := by
    rw [annularEnergyOuter_eq_trace lower length positive bounded mode first,
      annularEnergyOuter_eq_trace lower length positive bounded mode second, graphs mode]
  apply Subtype.ext
  apply Subtype.ext
  funext mode
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ (RadialL2 1 lower)
    (WithLp 2 (RadialL2 1 lower × ComplexEuclidean 1))).injective
  apply Prod.ext
  · exact derivatives mode
  · apply (WithLp.prodContinuousLinearEquiv 2 ℂ (RadialL2 1 lower) (ComplexEuclidean 1)).injective
    exact Prod.ext (masses mode) (outers mode)

def annularModeRepresentative (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (mode : HighAnnularMode) :
    annularEnergySpace lower length positive →L[ℝ] RadialContinuousSection 1 lower :=
  (weightedRadialSection 1 lower positive bounded).comp
    (annularModeRadialH1 lower length positive mode)

theorem annularModeRepresentative_primitive (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (mode : HighAnnularMode) (field : annularEnergySpace lower length positive)
    (radius : Icc lower (1 : ℝ)) :
    annularModeRepresentative lower length positive bounded mode field radius =
      weightedRadialTrace 1 lower positive bounded 0 (annularModeRadialH1 lower length positive mode field) +
      ∫ point in lower..radius.val, collarH1Coordinate (ComplexEuclidean 1) lower 1
        (weightedToOrdinary 1 lower positive bounded.le
          (annularModeRadialH1 lower length positive mode field)) point :=
  weightedRadialSection_primitive 1 lower positive bounded _ radius

end Grad.AnnularReconstruction
