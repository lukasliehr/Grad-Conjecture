import SBT11RadialEndpoint

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.SourceBoundaryTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.BoundaryTrace Grad.GaugeCoefficients.Physical.WeightedTrace

theorem weightedCurve_complex_smul {dimension : ℕ} (lower : ℝ) (scalar : ℂ)
    (curve : C(ℝ, ComplexEuclidean dimension)) :
    weightedCurveLinear dimension lower (scalar • curve) =
      scalar • weightedCurveLinear dimension lower curve := by
  apply Lp.ext
  filter_upwards [radialToLp_ae lower (scalar • curve) (scalar • curve).continuous,
    radialToLp_ae lower curve curve.continuous,
    Lp.coeFn_smul scalar (radialToLp lower curve curve.continuous)]
    with radius total curveLaw scaled
  change radialToLp lower (scalar • curve) (scalar • curve).continuous radius =
    (scalar • radialToLp lower curve curve.continuous) radius
  rw [total, scaled, Pi.smul_apply, curveLaw]
  exact smul_comm (Real.sqrt radius) scalar (curve radius)

def scaledSmoothCurve {dimension : ℕ} (scalar : ℂ)
    (core : collarSmoothGraph (ComplexEuclidean dimension)) :
    collarSmoothGraph (ComplexEuclidean dimension) :=
  ⟨(scalar • core.val.1, scalar • core.val.2), fun radius => (core.property radius).const_smul scalar⟩

theorem weightedEndpointCore_complex_smul (dimension : ℕ) (lower : ℝ) (scalar : ℂ)
    (core : collarSmoothGraph (ComplexEuclidean dimension)) :
    weightedEndpointCore dimension lower (scaledSmoothCurve scalar core) =
      scalar • weightedEndpointCore dimension lower core := by
  change ((weightedCurveLinear dimension lower (scalar • core.val.1),
    weightedCurveLinear dimension lower (scalar • core.val.2)), _) = _
  rw [weightedCurve_complex_smul, weightedCurve_complex_smul]
  rfl

theorem radialEndpointGraph_complex_smul {dimension : ℕ} (lower : ℝ) (scalar : ℂ)
    (point : RadialEndpointAmbient dimension lower) (member : point ∈ radialEndpointGraph dimension lower) :
    scalar • point ∈ radialEndpointGraph dimension lower := by
  apply closure_minimal (s := (LinearMap.range (weightedEndpointCore dimension lower) : Set _))
    (fun point coreMember => ?_)
    (((LinearMap.range (weightedEndpointCore dimension lower)).isClosed_topologicalClosure).preimage
      (continuous_const_smul scalar)) member
  rcases coreMember with ⟨core, rfl⟩
  change scalar • weightedEndpointCore dimension lower core ∈ radialEndpointGraph dimension lower
  rw [← weightedEndpointCore_complex_smul]
  exact radialEndpointGraph_core dimension lower (scaledSmoothCurve scalar core)

def restrictionCurve {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (power : ℕ) (mode : ℤ × ℤ) (order : ℕ) :
    C(ℝ, ComplexEuclidean dimension) :=
  ⟨fun radius => (annularFrequency mode.1 mode.2 : ℂ) ^ power •
      radialCoefficientJet (originalPolarValue (phaseWeightedJet parameters mode.2 (field.val mode.2)))
        mode.1 order radius,
    by
      exact (continuous_const (y := (annularFrequency mode.1 mode.2 : ℂ) ^ power)).smul
        (radialCoefficientJet_smooth
          (originalPolarValue (phaseWeightedJet parameters mode.2 (field.val mode.2)))
          (originalPolarValue_smooth _) mode.1 order).continuous⟩

def restrictionSmoothCurve {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (power : ℕ) (mode : ℤ × ℤ) :
    collarSmoothGraph (ComplexEuclidean dimension) :=
  ⟨(restrictionCurve parameters field power mode 0, restrictionCurve parameters field power mode 1),
    fun radius => (radialCoefficientJet_hasDerivAt
      (originalPolarValue (phaseWeightedJet parameters mode.2 (field.val mode.2)))
      (originalPolarValue_smooth _) mode.1 0 radius).const_smul
        ((annularFrequency mode.1 mode.2 : ℂ) ^ power)⟩

theorem restrictionCurve_weighted {dimension : ℕ} (lower : ℝ) (parameters : PhaseParameters)
    (field : ACore parameters dimension) (power : ℕ) (mode : ℤ × ℤ) (order : ℕ) :
    weightedCurveLinear dimension lower (restrictionCurve parameters field power mode order) =
      restrictionModeLp lower power order parameters field mode := by
  let curve : C(ℝ, ComplexEuclidean dimension) :=
    ⟨radialCoefficientJet (originalPolarValue (phaseWeightedJet parameters mode.2 (field.val mode.2)))
      mode.1 order, (radialCoefficientJet_smooth
        (originalPolarValue (phaseWeightedJet parameters mode.2 (field.val mode.2)))
        (originalPolarValue_smooth _) mode.1 order).continuous⟩
  exact weightedCurve_complex_smul lower ((annularFrequency mode.1 mode.2 : ℂ) ^ power) curve

theorem restrictionPolarPoint_one (angle : ℝ) :
    Grad.SourceCollarDivision.polarClosedPoint 1 angle (by norm_num) le_rfl =
      boundaryDiskPoint (angle : CellCircle) := by
  apply Subtype.ext
  change polarPlane (1, angle) = boundaryCirclePoint (angle : CellCircle)
  rw [boundaryCirclePoint_coe]
  simp [polarPlane]

theorem restrictionCurve_endpoint {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (power : ℕ) (mode : ℤ × ℤ) :
    restrictionCurve parameters field power mode 0 1 =
      (sourceBoundaryWeight parameters power mode : ℂ) • originalBoundaryCoefficient parameters field mode := by
  have curve : (fun angle : ℝ =>
      originalPolarValue (phaseWeightedJet parameters mode.2 (field.val mode.2)) (1, angle)) =
      (fun angle : ℝ => (phaseWeightedJet parameters mode.2 (field.val mode.2)).value
        (boundaryDiskPoint (angle : CellCircle))) := by
    funext angle
    rw [originalPolarValue_closed _ 1 angle (by norm_num) le_rfl, restrictionPolarPoint_one]
  change (annularFrequency mode.1 mode.2 : ℂ) ^ power •
    angularCoefficient (fun angle => originalPolarValue
      (phaseWeightedJet parameters mode.2 (field.val mode.2)) (1, angle)) mode.1 = _
  rw [curve, angularCoefficient_circle
    (fun angle : CellCircle => (phaseWeightedJet parameters mode.2 (field.val mode.2)).value
      (boundaryDiskPoint angle)) mode.1, phaseWeightedJet_boundary_coefficient]
  rw [← Complex.coe_smul, smul_smul]
  unfold sourceBoundaryWeight originalBoundaryCoefficient
  push_cast
  congr 1
  ring

theorem restrictionMode_endpoint_core {dimension : ℕ} (lower : ℝ) (parameters : PhaseParameters)
    (field : ACore parameters dimension) (power : ℕ) (mode : ℤ × ℤ) :
    ((restrictionModeLp lower power 0 parameters field mode,
      restrictionModeLp lower power 1 parameters field mode),
      (sourceBoundaryWeight parameters power mode : ℂ) • originalBoundaryCoefficient parameters field mode) ∈
      radialEndpointGraph dimension lower := by
  have core := radialEndpointGraph_core dimension lower (restrictionSmoothCurve parameters field power mode)
  change ((weightedCurveLinear dimension lower (restrictionCurve parameters field power mode 0),
    weightedCurveLinear dimension lower (restrictionCurve parameters field power mode 1)),
    restrictionCurve parameters field power mode 0 1) ∈ radialEndpointGraph dimension lower at core
  simpa only [restrictionCurve_weighted, restrictionCurve_endpoint] using core

/-- Original completion trace and actual radial derivative graph have the
same endpoint, including grades one and two. No point evaluation of an
arbitrary L2 representative is used. -/
theorem completedRestriction_endpoint {dimension : ℕ} (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (parameters : PhaseParameters) (power : ℕ)
    (field : AGrade parameters dimension (power + 1)) (mode : ℤ × ℤ) :
    (((completedRestriction lower positive bounded parameters power 1 field).val 0 mode,
      (completedRestriction lower positive bounded parameters power 1 field).val 1 mode),
      integerSourceTrace parameters power field mode) ∈ radialEndpointGraph dimension lower := by
  let value := (divisionArrayCoordinate dimension lower 1 0 mode).comp
    (completedRestrictionArray lower positive bounded parameters power 1)
  let slope := (divisionArrayCoordinate dimension lower 1 1 mode).comp
    (completedRestrictionArray lower positive bounded parameters power 1)
  let endpoint := (lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode).comp
    (integerSourceTrace parameters power)
  have closed := ((LinearMap.range (weightedEndpointCore dimension lower)).isClosed_topologicalClosure).preimage
    ((value.continuous.prodMk slope.continuous).prodMk endpoint.continuous)
  refine UniformSpace.Completion.induction_on field closed ?_
  intro core
  change (((completedRestriction lower positive bounded parameters power 1 (aGradeEta parameters core)).val 0 mode,
    (completedRestriction lower positive bounded parameters power 1 (aGradeEta parameters core)).val 1 mode),
    integerSourceTrace parameters power (aGradeEta parameters core) mode) ∈ radialEndpointGraph dimension lower
  rw [completedRestriction_core, completedRestriction_core]
  change ((restrictionModeLp lower power 0 parameters core.toCore mode,
    restrictionModeLp lower power 1 parameters core.toCore mode),
    integerSourceTrace parameters power (aGradeEta parameters core) mode) ∈ radialEndpointGraph dimension lower
  rw [← sourceBoundary_weighted parameters power, integerSourceTrace_core]
  exact restrictionMode_endpoint_core lower parameters core.toCore power mode

end Grad.SourceBoundaryTrace
