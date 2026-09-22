import GQ16ActualFlatness

noncomputable section

set_option maxHeartbeats 1800000

open Filter Asymptotics
open scoped Topology BigOperators ContDiff

namespace Grad.GaugeCoefficients.Physical.GaugeTransfer

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.NonlinearDivision
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.PhysicalFamily

theorem closedAxisFlat_of_global {Value : Type} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : SpatialPlane → Value) (zero : field 0 = 0)
    (derivative : HasFDerivAt field (0 : SpatialPlane →L[ℝ] Value) (0 : SpatialPlane)) :
    ClosedAxisFlat (fun point => field point.val) := by
  have little : field =o[𝓝 (0 : SpatialPlane)] (fun point => point) := by
    rw [hasFDerivAt_iff_isLittleO] at derivative
    simpa only [zero, sub_zero, zero_apply] using derivative
  intro tolerance positive
  obtain ⟨radius, radiusPositive, bound⟩ := Metric.mem_nhds_iff.mp (little.bound positive)
  refine ⟨radius, radiusPositive, fun point inside => ?_⟩
  exact bound (by simpa only [Metric.mem_ball, dist_zero_right] using inside)

/-- The quantitative criterion is supplied by the literal closed-jet
value and both first Cartesian jets; no ambient extension is postulated. -/
theorem closedJet_axisFlat {dimension : ℕ} (field : ClosedJet dimension)
    (valueZero : originValue field = 0) (firstZero : ∀ direction, originPartial direction field = 0) :
    ClosedAxisFlat field.value := by
  have zero : smoothClosedExtension field (0 : SpatialPlane) = 0 := by
    change smoothClosedExtension field originPoint.val = 0
    rw [smoothClosedExtension_value]
    exact valueZero
  have derivativeZero : fderiv ℝ (smoothClosedExtension field) (0 : SpatialPlane) = 0 := by
    apply ContinuousLinearMap.ext
    intro vector
    have onBasis (direction : Fin 2) :
        fderiv ℝ (smoothClosedExtension field) (0 : SpatialPlane) (spatialBasis direction) = 0 := by
      change spatialPartial direction (smoothClosedExtension field) originPoint.val = 0
      rw [spatialPartial_eq_ordered, smoothClosedExtension_derivative]
      exact firstZero direction
    have decomposition : vector = vector 0 • spatialBasis 0 + vector 1 • spatialBasis 1 := by
      apply PiLp.ext
      intro coordinate
      fin_cases coordinate <;> simp [spatialBasis]
    rw [decomposition, map_add, map_smul, map_smul, onBasis, onBasis,
      smul_zero, smul_zero, add_zero, zero_apply]
  have flat := closedAxisFlat_of_global (smoothClosedExtension field) zero
    (derivativeZero ▸ (((smoothClosedExtension_smooth field).differentiable (by simp)).differentiableAt
      (x := (0 : SpatialPlane))).hasFDerivAt)
  have equality : (fun point : ClosedDisk => smoothClosedExtension field point.val) = field.value :=
    funext (smoothClosedExtension_value field)
  rwa [equality] at flat

theorem ClosedAxisFlat.sum {Index : Type*} {dimension : ℕ} (indices : Finset Index)
    (fields : Index → ClosedDisk → ComplexEuclidean dimension)
    (flat : ∀ index ∈ indices, ClosedAxisFlat (fields index)) :
    ClosedAxisFlat (fun point => ∑ index ∈ indices, fields index point) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
      intro tolerance positive
      refine ⟨1, zero_lt_one, fun point _ => ?_⟩
      simp only [Finset.sum_empty, norm_zero]
      positivity
  | @insert index rest missing induction =>
      have first := flat index (Finset.mem_insert_self _ _)
      have remaining := induction (fun other member => flat other (Finset.mem_insert_of_mem member))
      simpa only [Finset.sum_insert missing] using first.add remaining

theorem apFiniteInto_firstJetZero {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension grade : ℕ} (large : 2 ≤ grade) (core : ℤ →₀ ClosedJet dimension)
    (valueZero : ∀ cell, originValue (core cell) = 0)
    (firstZero : ∀ cell direction, originPartial direction (core cell) = 0) :
    APAxisFirstJetZero admissible large (apFiniteInto L sigma gamma ell core) := by
  intro angle
  apply (closedAxisFlat_iff_firstJet _).mp
  rw [apPhysicalValue_core]
  have flat := ClosedAxisFlat.sum core.support
    (fun cell point => axialPhase cell angle • (core cell).value point)
    (fun cell _ => (closedJet_axisFlat (core cell) (valueZero cell) (firstZero cell)).smul (axialPhase cell angle))
  convert flat using 1
  funext point
  simp

/-- Universal finite-Fourier smooth-core consumer, followed by the exact
completed Qa. Arbitrary cells remain; no fixed spectral truncation. -/
theorem actualGaugeFlatness_core {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) {grade : ℕ} (large : 2 ≤ grade)
    (core : ℤ →₀ ClosedJet 3) (valueZero : ∀ cell, originValue (core cell) = 0)
    (firstZero : ∀ cell direction, originPartial direction (core cell) = 0) :
    APAxisFirstJetZero admissible large
      (apCurrentProjection admissible gauge grade (apFiniteInto L sigma gamma ell core)) :=
  apCurrentProjection_preserves_firstJet admissible gauge large _
    (apFiniteInto_firstJetZero admissible large core valueZero firstZero)

end Grad.GaugeCoefficients.Physical.GaugeTransfer
