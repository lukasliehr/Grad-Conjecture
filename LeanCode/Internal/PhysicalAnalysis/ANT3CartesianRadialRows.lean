import ANT2ScalarCommutators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.CartesianScalarElimination
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Algebra
open Grad.NonlinearRange Grad.NonlinearDivision Grad.ActualMeanInverse Grad.CircularHighWeak
open Grad.NonlinearQuotientBounds (coordinateJet_value)

def fixedProductLinear {input output : ℕ} (coefficient : SmoothOperatorJet input output) :
    ClosedJet input →ₗ[ℂ] ClosedJet output where
  toFun := apProductJet coefficient
  map_add' first second := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    simp only [apProductJet_value, closedJet_value_add, ContinuousMap.add_apply, map_add]
  map_smul' scalar field := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    simp only [apProductJet_value, closedJet_value_smul, ContinuousMap.smul_apply, map_smul, RingHom.id_apply]

def vectorRadialLinear : ClosedJet 2 →ₗ[ℂ] ClosedJet 1 :=
  (fixedProductLinear radialRowJet).comp (valueMapJetLinear 2 3 planarInclusionMap)

def vectorRadialJet (field : ClosedJet 2) : ClosedJet 1 := vectorRadialLinear field

def vectorTangentLinear : ClosedJet 2 →ₗ[ℂ] ClosedJet 1 :=
  (fixedProductLinear tangentRowJet).comp (valueMapJetLinear 2 3 planarInclusionMap)

def vectorTangentJet (field : ClosedJet 2) : ClosedJet 1 := vectorTangentLinear field

theorem vectorRadialJet_actual (field : ClosedJet 2) :
    vectorRadialJet field = apProductJet radialRowJet (valueMapJet planarInclusionMap field) := rfl

theorem vectorTangentJet_actual (field : ClosedJet 2) :
    vectorTangentJet field = apProductJet tangentRowJet (valueMapJet planarInclusionMap field) := rfl

theorem vectorRadialJet_value (field : ClosedJet 2) (point : ClosedDisk) :
    (vectorRadialJet field).value point 0 =
      (point.val 0 : ℂ) * field.value point 0 + (point.val 1 : ℂ) * field.value point 1 := by
  rw [vectorRadialJet_actual, apProductJet_value, radialRowJet_value, valueMapJet_value]
  simp [planarInclusionMap]

theorem vectorTangentJet_value (field : ClosedJet 2) (point : ClosedDisk) :
    (vectorTangentJet field).value point 0 =
      -(point.val 1 : ℂ) * field.value point 0 + (point.val 0 : ℂ) * field.value point 1 := by
  rw [vectorTangentJet_actual, apProductJet_value, tangentRowJet_value, valueMapJet_value]
  simp [storedTangentDot, planarInclusionMap]

theorem vectorRadialJet_quarter (field : ClosedJet 2) :
    vectorRadialJet (valueMapJet quarterValueMap field) = -vectorTangentJet field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  have coordinateZero : coordinate = 0 := Subsingleton.elim _ _
  subst coordinate
  simp only [closedJet_value_neg, ContinuousMap.neg_apply, PiLp.neg_apply]
  change (vectorRadialJet (valueMapJet quarterValueMap field)).value point 0 = -(vectorTangentJet field).value point 0
  rw [vectorRadialJet_value, vectorTangentJet_value, valueMapJet_value]
  simp [quarterValueMap, quarterValueLinear]

theorem vectorTangentJet_quarter (field : ClosedJet 2) :
    vectorTangentJet (valueMapJet quarterValueMap field) = vectorRadialJet field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  have coordinateZero : coordinate = 0 := Subsingleton.elim _ _
  subst coordinate
  change (vectorTangentJet (valueMapJet quarterValueMap field)).value point 0 = (vectorRadialJet field).value point 0
  rw [vectorRadialJet_value, vectorTangentJet_value, valueMapJet_value]
  simp [quarterValueMap, quarterValueLinear]
  ring

theorem rotationJet_radial (field : ClosedJet 2) :
    rotationJet (vectorRadialJet field) = vectorTangentJet field + vectorRadialJet (rotationJet field) := by
  have law := rotationJet_radialRow (valueMapJet planarInclusionMap field)
  rw [rotationJet_valueMap] at law
  exact law

theorem scalarRotation_neg (field : ClosedJet 1) : rotationJet (-field) = -rotationJet field :=
  map_neg rotationJetLinear field

theorem rotationJet_tangent (field : ClosedJet 2) :
    rotationJet (vectorTangentJet field) = vectorTangentJet (rotationJet field) - vectorRadialJet field := by
  have law := rotationJet_radial (valueMapJet quarterValueMap field)
  rw [vectorRadialJet_quarter, scalarRotation_neg, vectorTangentJet_quarter,
    rotationJet_valueMap, vectorRadialJet_quarter] at law
  apply neg_injective
  rw [law]
  abel

theorem vectorRadialJet_rotationPlusQuarter (field : ClosedJet 2) :
    vectorRadialJet (rotationJet field + valueMapJet quarterValueMap field) =
      rotationJet (vectorRadialJet field) - (2 : ℂ) • vectorTangentJet field := by
  change vectorRadialLinear (rotationJet field + valueMapJet quarterValueMap field) = _
  rw [map_add]
  change vectorRadialJet (rotationJet field) + vectorRadialJet (valueMapJet quarterValueMap field) = _
  rw [vectorRadialJet_quarter, rotationJet_radial]
  module

theorem vectorTangentJet_rotationPlusQuarter (field : ClosedJet 2) :
    vectorTangentJet (rotationJet field + valueMapJet quarterValueMap field) =
      rotationJet (vectorTangentJet field) + (2 : ℂ) • vectorRadialJet field := by
  change vectorTangentLinear (rotationJet field + valueMapJet quarterValueMap field) = _
  rw [map_add]
  change vectorTangentJet (rotationJet field) + vectorTangentJet (valueMapJet quarterValueMap field) = _
  rw [vectorTangentJet_quarter, rotationJet_tangent]
  module

theorem vectorRadialJet_gradient (field : ClosedJet 1) : vectorRadialJet (gradientJet field) = eulerJet field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  have coordinateZero : coordinate = 0 := Subsingleton.elim _ _
  subst coordinate
  change (vectorRadialJet (gradientJet field)).value point 0 = (eulerJet field).value point 0
  rw [vectorRadialJet_value, gradientJet_value]
  simp [eulerJet, closedJet_value_add, coordinateJet_value, Complex.real_smul,
    partialJet, Grad.NonlinearQuotientBounds.partialJet]

theorem vectorTangentJet_gradient (field : ClosedJet 1) : vectorTangentJet (gradientJet field) = rotationJet field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  have coordinateZero : coordinate = 0 := Subsingleton.elim _ _
  subst coordinate
  change (vectorTangentJet (gradientJet field)).value point 0 = (rotationJet field).value point 0
  rw [vectorTangentJet_value, gradientJet_value]
  simp [rotationJet, sub_eq_add_neg, closedJet_value_add, closedJet_value_neg,
    coordinateJet_value, Complex.real_smul, partialJet, Grad.NonlinearQuotientBounds.partialJet]
  ring

end Grad.CartesianScalarElimination
