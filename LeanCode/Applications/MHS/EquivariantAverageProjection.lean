import EquivariantAverage

noncomputable section

namespace Grad.Constraints

open Grad.ClosedJets

theorem equivariantAverageJet_eq (field : ClosedJet 2) :
    equivariantAverageJet field = valueMapJet positiveHelicity (angularClosedJet 1 field) +
      valueMapJet negativeHelicity (angularClosedJet (-1) field) := rfl

theorem equivariantAverageJet_idempotent (field : ClosedJet 2) :
    equivariantAverageJet (equivariantAverageJet field) = equivariantAverageJet field := by
  simp only [equivariantAverageJet_eq, angularClosedJet_add, angularClosedJet_valueMap,
    angularClosedJet_projection, valueMapJet_add,
    valueMapJet_comp, positiveHelicity_idempotent, negativeHelicity_idempotent,
    positiveHelicity_negative, negativeHelicity_positive, valueMapJet_zero]
  norm_num

def reflectedVectorLinear : ClosedJet 2 →ₗ[ℂ] ClosedJet 2 :=
  (valueMapJetLinear 2 2 reflectionValueMap).comp
    (orthogonalJetLinear 2 cartesianReflectionEquiv)

def reflectedVectorJet (field : ClosedJet 2) : ClosedJet 2 := reflectedVectorLinear field

theorem reflectedVectorJet_eq (field : ClosedJet 2) :
    reflectedVectorJet field = valueMapJet reflectionValueMap
      (orthogonalJet cartesianReflectionEquiv field) := rfl

theorem reflectedVectorJet_involutive (field : ClosedJet 2) :
    reflectedVectorJet (reflectedVectorJet field) = field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [reflectedVectorJet_eq, valueMapJet_value]
  change reflectionValueMap
    ((reflectedVectorJet field).value (Grad.GaugeCoefficients.Radial.orthogonalClosedPoint
      cartesianReflectionEquiv point)) = field.value point
  rw [reflectedVectorJet_eq, valueMapJet_value]
  change reflectionValueMap (reflectionValueMap (field.value
    (Grad.GaugeCoefficients.Radial.orthogonalClosedPoint cartesianReflectionEquiv
      (Grad.GaugeCoefficients.Radial.orthogonalClosedPoint cartesianReflectionEquiv point)))) = _
  rw [reflectionValueMap_square]
  congr 1
  apply Subtype.ext
  exact cartesianReflection_involutive point.val

theorem reflectedVectorJet_average (field : ClosedJet 2) :
    reflectedVectorJet (equivariantAverageJet field) =
      equivariantAverageJet (reflectedVectorJet field) := by
  simp only [reflectedVectorJet_eq, equivariantAverageJet_eq]
  have orthogonalAdd (first second : ClosedJet 2) :
      orthogonalJet cartesianReflectionEquiv (first + second) =
        orthogonalJet cartesianReflectionEquiv first + orthogonalJet cartesianReflectionEquiv second :=
    (orthogonalJetLinear 2 cartesianReflectionEquiv).map_add first second
  simp only [orthogonalAdd, ← valueMapJet_orthogonal, angularClosedJet_valueMap,
    valueMapJet_add, valueMapJet_comp, angularClosedJet_reflection,
    reflectionValue_positive, reflectionValue_negative]
  norm_num
  exact add_comm _ _

/-- N3 tangential projection, defined everywhere in Cartesian coordinates. -/
def tangentialJetLinear : ClosedJet 2 →ₗ[ℂ] ClosedJet 2 :=
  (1 / 2 : ℂ) • ((LinearMap.id - reflectedVectorLinear).comp equivariantAverageLinear)

def tangentialJet (field : ClosedJet 2) : ClosedJet 2 := tangentialJetLinear field

theorem tangentialJet_eq (field : ClosedJet 2) :
    tangentialJet field = (1 / 2 : ℂ) •
      (equivariantAverageJet field - reflectedVectorJet (equivariantAverageJet field)) := rfl

theorem equivariantAverageJet_smul (scalar : ℂ) (field : ClosedJet 2) :
    equivariantAverageJet (scalar • field) = scalar • equivariantAverageJet field :=
  equivariantAverageLinear.map_smul scalar field

theorem equivariantAverageJet_sub (first second : ClosedJet 2) :
    equivariantAverageJet (first - second) =
      equivariantAverageJet first - equivariantAverageJet second :=
  equivariantAverageLinear.map_sub first second

theorem reflectedVectorJet_smul (scalar : ℂ) (field : ClosedJet 2) :
    reflectedVectorJet (scalar • field) = scalar • reflectedVectorJet field :=
  reflectedVectorLinear.map_smul scalar field

theorem reflectedVectorJet_sub (first second : ClosedJet 2) :
    reflectedVectorJet (first - second) = reflectedVectorJet first - reflectedVectorJet second :=
  reflectedVectorLinear.map_sub first second

theorem tangentialJet_idempotent (field : ClosedJet 2) :
    tangentialJet (tangentialJet field) = tangentialJet field := by
  simp only [tangentialJet_eq, equivariantAverageJet_smul, equivariantAverageJet_sub,
    equivariantAverageJet_idempotent, ← reflectedVectorJet_average,
    equivariantAverageJet_idempotent, reflectedVectorJet_smul, reflectedVectorJet_sub,
    reflectedVectorJet_involutive]
  module

end Grad.Constraints
