import JRConsumer
import WTCSmooth
import DR1Consumer
import ZE1Field
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (CellValues PhysicalValue FieldL2)
open Grad.WeightedJets (JetIndex JetTuple WJet TestFunction degree derivativeWord base)
open scoped BigOperators ContDiff Topology

namespace Grad.SpatialDilation

def Scale := {scalar : ℝ // 0 < scalar ∧ scalar ≤ 1}

instance : TopologicalSpace Scale := inferInstanceAs (TopologicalSpace {scalar : ℝ // 0 < scalar ∧ scalar ≤ 1})

instance : FirstCountableTopology Scale :=
  inferInstanceAs (FirstCountableTopology {scalar : ℝ // 0 < scalar ∧ scalar ≤ 1})

def oneScale : Scale := ⟨1, zero_lt_one, le_rfl⟩

def spatialMap (scale : Scale) : Spatial → Spatial := fun point => scale.val • point

def pullDomain (scale : Scale) (domain : Set Spatial) : Set Spatial := spatialMap scale ⁻¹' domain

def disk (radius : ℝ) : Set Spatial := Metric.ball (0 : Spatial) radius

def expandedDisk (radius : ℝ) (scale : Scale) : Set Spatial := pullDomain scale (disk radius)

def jacobian (scale : Scale) : ENNReal := ENNReal.ofReal ((scale.val ^ 2)⁻¹)

theorem map_measure (domain : Set Spatial) (measurableDomain : MeasurableSet domain) (scale : Scale) :
    Measure.map (spatialMap scale) (volume.restrict (pullDomain scale domain)) =
      jacobian scale • volume.restrict domain := by
  have rawMap : Measure.map (spatialMap scale) (volume : Measure Spatial) = jacobian scale • volume := by
    change Measure.map (fun point : Spatial => scale.val • point) volume =
      ENNReal.ofReal ((scale.val ^ 2)⁻¹) • volume
    have nonnegativeJacobian : 0 ≤ (scale.val ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg scale.val)
    simpa only [Spatial, finrank_euclideanSpace_fin,
      abs_of_nonneg nonnegativeJacobian] using
      (Measure.map_addHaar_smul (volume : Measure Spatial) scale.property.1.ne')
  calc
    _ = (Measure.map (spatialMap scale) volume).restrict domain :=
      (Measure.restrict_map (show Measurable (spatialMap scale) from measurable_const_smul scale.val)
        measurableDomain).symm
    _ = (jacobian scale • volume).restrict domain :=
      congrArg (fun measure : Measure Spatial => measure.restrict domain) rawMap
    _ = _ := Measure.restrict_smul _ _ _

def mapPullback (dimension : ℕ) (domain : Set Spatial) (measurableDomain : MeasurableSet domain)
    (scale : Scale) :
    Lp (CellValues dimension) 2 (jacobian scale • volume.restrict domain) →ₗᵢ[ℂ]
      FieldL2 dimension (pullDomain scale domain) :=
  Lp.compMeasurePreservingₗᵢ ℂ (spatialMap scale)
    ⟨measurable_const_smul scale.val, map_measure domain measurableDomain scale⟩

def rawValue (dimension : ℕ) (domain : Set Spatial) (measurableDomain : MeasurableSet domain)
    (scale : Scale) (field : FieldL2 dimension domain) : FieldL2 dimension (pullDomain scale domain) :=
  mapPullback dimension domain measurableDomain scale
    (((Lp.memLp field).smul_measure (c := jacobian scale) ENNReal.ofReal_ne_top).toLp field)

theorem expandedDisk_eq (radius : ℝ) (scale : Scale) :
    expandedDisk radius scale = Metric.ball (0 : Spatial) (radius / scale.val) := by
  ext point
  simp only [expandedDisk, pullDomain, Set.mem_preimage, spatialMap, disk, Metric.mem_ball,
    dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos scale.property.1]
  rw [lt_div_iff₀ scale.property.1, mul_comm]

theorem expandedDisk_open (radius : ℝ) (scale : Scale) : IsOpen (expandedDisk radius scale) :=
  Metric.isOpen_ball.preimage (continuous_const_smul scale.val)

theorem disk_subset_expanded (radius : ℝ) (scale : Scale) : disk radius ⊆ expandedDisk radius scale := by
  intro point membership
  change dist (scale.val • point) 0 < radius
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos scale.property.1]
  have inside : ‖point‖ < radius := by
    simpa only [disk, Metric.mem_ball, dist_zero_right] using membership
  exact (mul_le_of_le_one_left (norm_nonneg point) scale.property.2).trans_lt inside

def diskMargin (radius : ℝ) (scale : Scale) : ℝ := (radius / scale.val - radius) / 3

def tupleValue (dimension order : ℕ) (radius : ℝ) (scale : Scale)
    (tuple : JetTuple dimension order (disk radius)) : JetTuple dimension order (expandedDisk radius scale) :=
  WithLp.toLp 2 (fun index => (scale.val ^ degree index : ℂ) •
    rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale (tuple index))

def restrictExpanded (dimension order : ℕ) (radius : ℝ) (scale : Scale)
    (exponent : JetIndex order → ℕ) :
    WJet dimension order (expandedDisk radius scale) exponent →L[ℂ] WJet dimension order (disk radius) exponent :=
  Grad.WeightedJets.Restriction.restriction dimension order (disk_subset_expanded radius scale)
    (expandedDisk_open radius scale).measurableSet exponent

def GeometryGoal : Prop :=
  (∀ (radius : ℝ) (scale : Scale), expandedDisk radius scale = Metric.ball (0 : Spatial) (radius / scale.val)) ∧
  ∀ (radius : ℝ) (scale : Scale), 0 < radius → scale.val < 1 →
    0 < diskMargin radius scale ∧ radius + 3 * diskMargin radius scale = radius / scale.val ∧
    Metric.closedBall (0 : Spatial) radius ⊆ expandedDisk radius scale

def FieldGoal : Prop :=
  ∀ (dimension : ℕ) (domain : Set Spatial) (measurableDomain : MeasurableSet domain) (scale : Scale),
    (∃ mapping : FieldL2 dimension domain →L[ℂ] FieldL2 dimension (pullDomain scale domain),
      (∀ field, mapping field = rawValue dimension domain measurableDomain scale field) ∧ ‖mapping‖ ≤ scale.val⁻¹) ∧
    (∀ field : FieldL2 dimension domain,
      ‖rawValue dimension domain measurableDomain scale field‖ = scale.val⁻¹ * ‖field‖ ∧
      ∀ᵐ point ∂volume.restrict (pullDomain scale domain), ∀ cell : ℤ,
        rawValue dimension domain measurableDomain scale field point cell = field (scale.val • point) cell) ∧
    (∀ (power : ℕ) (field : FieldL2 dimension domain),
      rawValue dimension domain measurableDomain scale (Grad.CellWeights.inverseFieldCLM dimension domain power field) =
        Grad.CellWeights.inverseFieldCLM dimension (pullDomain scale domain) power
          (rawValue dimension domain measurableDomain scale field))

def TestGoal : Prop :=
  (∀ (scalar : ℝ) (rank : ℕ) (word : Fin rank → Fin 2) (test : Spatial → ℝ), ContDiff ℝ ∞ test →
    Grad.WeakTesting.orderedTestDerivative rank word (fun point => test (scalar • point)) =
      fun point => scalar ^ rank * Grad.WeakTesting.orderedTestDerivative rank word test (scalar • point)) ∧
  ∀ (radius : ℝ) (scale : Scale) (test : TestFunction (expandedDisk radius scale)),
    ∃ pulledTest : TestFunction (disk radius),
      pulledTest.toFun = (fun point => test.toFun (scale.val⁻¹ • point)) ∧
      (∀ (rank : ℕ) (word : Fin rank → Fin 2),
        Grad.WeakTesting.orderedTestDerivative rank word pulledTest.toFun =
          fun point => scale.val⁻¹ ^ rank *
            Grad.WeakTesting.orderedTestDerivative rank word test.toFun (scale.val⁻¹ • point)) ∧
      ∀ (dimension : ℕ) (field : FieldL2 dimension (disk radius)) (cell : ℤ) (vector : PhysicalValue dimension),
        Grad.WeightedJets.testPairing dimension (expandedDisk radius scale) cell vector test
            (rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale field) =
          (scale.val ^ 2)⁻¹ • Grad.WeightedJets.testPairing dimension (disk radius) cell vector pulledTest field ∧
        (∫ point in expandedDisk radius scale, test.toFun point • inner ℂ vector
          (rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale field point cell)) =
          (scale.val ^ 2)⁻¹ • ∫ point in disk radius,
            test.toFun (scale.val⁻¹ • point) • inner ℂ vector (field point cell)

def WeakGoal : Prop :=
  ∀ (dimension order : ℕ) (radius : ℝ) (scale : Scale) (exponent : JetIndex order → ℕ)
    (jet : WJet dimension order (disk radius) exponent) (index : JetIndex order),
    Grad.WeakTesting.Commutation.HasWeakOrderedDerivative dimension (expandedDisk radius scale)
      (degree index) (derivativeWord index)
      (rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale
        (base dimension order (disk radius) exponent jet))
      ((scale.val ^ degree index : ℂ) • rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale
        (Grad.WeightedJets.Realization.recoveredDerivative dimension order (disk radius) exponent index jet))

def TupleGoal : Prop :=
  ∀ (dimension order : ℕ) (radius : ℝ) (scale : Scale) (tuple : JetTuple dimension order (disk radius)),
    ‖tupleValue dimension order radius scale tuple‖ ^ 2 =
      ∑ index : JetIndex order, scale.val ^ (2 * (degree index : ℤ) - 2) * ‖tuple index‖ ^ 2 ∧
    ‖tupleValue dimension order radius scale tuple‖ ≤ scale.val⁻¹ * ‖tuple‖ ∧
    ∀ exponent : JetIndex order → ℕ,
      tuple ∈ Grad.WeightedJets.jetGraph dimension order (disk radius) exponent →
        tupleValue dimension order radius scale tuple ∈
          Grad.WeightedJets.jetGraph dimension order (expandedDisk radius scale) exponent

def PlaneContinuityGoal : Prop :=
  ∀ (dimension : ℕ) (field : FieldL2 dimension Set.univ),
    Filter.Tendsto (fun scale : Scale => rawValue dimension Set.univ MeasurableSet.univ scale field)
      (𝓝 oneScale) (𝓝 field)

def restrictedRaw (dimension : ℕ) (radius : ℝ) (scale : Scale)
    (field : FieldL2 dimension (disk radius)) : FieldL2 dimension (disk radius) :=
  Grad.WeightedJets.Restriction.fieldRestriction (CellValues dimension) (disk_subset_expanded radius scale)
    (rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale field)

def RawRestrictionGoal : Prop :=
  ∀ (dimension : ℕ) (radius : ℝ) (field : FieldL2 dimension (disk radius)),
    (∀ scale : Scale, restrictedRaw dimension radius scale field =
      Grad.WeightedJets.Restriction.fieldRestriction (CellValues dimension) (Set.subset_univ (disk radius))
        (rawValue dimension Set.univ MeasurableSet.univ scale
          (Grad.WeightedJets.ZeroExtension.fieldExtension (CellValues dimension) (disk radius)
            Metric.isOpen_ball.measurableSet field))) ∧
    Filter.Tendsto (fun scale : Scale => restrictedRaw dimension radius scale field) (𝓝 oneScale) (𝓝 field)

def JetLaws (dimension order : ℕ) (radius : ℝ) (scale : Scale) (exponent : JetIndex order → ℕ)
    (mapping : WJet dimension order (disk radius) exponent →L[ℂ]
      WJet dimension order (expandedDisk radius scale) exponent) : Prop :=
  ‖mapping‖ ≤ scale.val⁻¹ ∧
  ∀ jet : WJet dimension order (disk radius) exponent,
    (mapping jet).val = tupleValue dimension order radius scale jet.val ∧
    ‖mapping jet‖ ^ 2 =
      ∑ index : JetIndex order, scale.val ^ (2 * (degree index : ℤ) - 2) * ‖jet.val index‖ ^ 2 ∧
    ‖mapping jet‖ ≤ scale.val⁻¹ * ‖jet‖ ∧
    base dimension order (expandedDisk radius scale) exponent (mapping jet) =
      rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale
        (base dimension order (disk radius) exponent jet) ∧
    (∀ index : JetIndex order,
      Grad.WeightedJets.Realization.recoveredDerivative dimension order (expandedDisk radius scale) exponent index
          (mapping jet) =
        (scale.val ^ degree index : ℂ) • rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale
          (Grad.WeightedJets.Realization.recoveredDerivative dimension order (disk radius) exponent index jet)) ∧
    (∀ᵐ point ∂volume.restrict (expandedDisk radius scale), ∀ (index : JetIndex order) (cell : ℤ),
      (mapping jet).val index point cell = (scale.val ^ degree index : ℂ) • jet.val index (scale.val • point) cell) ∧
    ∀ (index : JetIndex order) (cell : ℤ) (vector : PhysicalValue dimension)
      (test : TestFunction (expandedDisk radius scale)),
      (∫ point in expandedDisk radius scale, test.toFun point • inner ℂ vector
        (Grad.WeightedJets.Realization.recoveredDerivative dimension order (expandedDisk radius scale) exponent index
          (mapping jet) point cell)) =
        (-1 : ℂ) ^ degree index * ∫ point in expandedDisk radius scale,
          Grad.WeakTesting.orderedTestDerivative (degree index) (derivativeWord index) test.toFun point •
            inner ℂ vector (base dimension order (expandedDisk radius scale) exponent (mapping jet) point cell)

def JetGoal : Prop :=
  ∀ (dimension order : ℕ) (radius : ℝ) (exponent : JetIndex order → ℕ),
    ∃ mappings : ∀ scale : Scale, WJet dimension order (disk radius) exponent →L[ℂ]
        WJet dimension order (expandedDisk radius scale) exponent,
      (∀ scale, JetLaws dimension order radius scale exponent (mappings scale)) ∧
      (∀ jet : WJet dimension order (disk radius) exponent,
        Filter.Tendsto (fun scale : Scale => restrictExpanded dimension order radius scale exponent (mappings scale jet))
          (𝓝 oneScale) (𝓝 jet)) ∧
      (restrictExpanded dimension order radius oneScale exponent).comp (mappings oneScale) = ContinuousLinearMap.id ℂ _

def BlockGoal : Prop :=
  GeometryGoal ∧ FieldGoal ∧ TestGoal ∧ WeakGoal ∧ TupleGoal ∧ PlaneContinuityGoal ∧ RawRestrictionGoal ∧ JetGoal

end Grad.SpatialDilation
