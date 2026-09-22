import GaugeValueAlgebra

noncomputable section

set_option maxHeartbeats 800000

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints

/-- Planar component of a three-component Cartesian value. -/
def planarPartMap : ComplexEuclidean 3 →L[ℂ] ComplexEuclidean 2 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun value => WithLp.toLp 2 ![value 0, value 1]
      map_add' := by
        intro first second
        apply PiLp.ext
        intro coordinate
        fin_cases coordinate <;> simp
      map_smul' := by
        intro scalar value
        apply PiLp.ext
        intro coordinate
        fin_cases coordinate <;> simp }

/-- Toroidal component of a three-component Cartesian value. -/
def toroidalPartMap : ComplexEuclidean 3 →L[ℂ] ComplexEuclidean 1 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun value => WithLp.toLp 2 ![value 2]
      map_add' := by
        intro first second
        apply PiLp.ext
        intro coordinate
        fin_cases coordinate
        simp
      map_smul' := by
        intro scalar value
        apply PiLp.ext
        intro coordinate
        fin_cases coordinate
        simp }

/-- Planar inclusion into the three-component Cartesian value space. -/
def planarInclusionMap : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun value => WithLp.toLp 2 ![value 0, value 1, 0]
      map_add' := by
        intro first second
        apply PiLp.ext
        intro coordinate
        fin_cases coordinate <;> simp
      map_smul' := by
        intro scalar value
        apply PiLp.ext
        intro coordinate
        fin_cases coordinate <;> simp }

/-- Toroidal inclusion into the three-component Cartesian value space. -/
def toroidalInclusionMap : ComplexEuclidean 1 →L[ℂ] ComplexEuclidean 3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun value => WithLp.toLp 2 ![0, 0, value 0]
      map_add' := by
        intro first second
        apply PiLp.ext
        intro coordinate
        fin_cases coordinate <;> simp
      map_smul' := by
        intro scalar value
        apply PiLp.ext
        intro coordinate
        fin_cases coordinate <;> simp }

theorem planarPart_planarInclusion :
    planarPartMap.comp planarInclusionMap = ContinuousLinearMap.id ℂ (ComplexEuclidean 2) := by
  apply ContinuousLinearMap.ext
  intro value
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [planarPartMap, planarInclusionMap, LinearMap.toContinuousLinearMap]

theorem toroidalPart_toroidalInclusion :
    toroidalPartMap.comp toroidalInclusionMap = ContinuousLinearMap.id ℂ (ComplexEuclidean 1) := by
  apply ContinuousLinearMap.ext
  intro value
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  simp [toroidalPartMap, toroidalInclusionMap, LinearMap.toContinuousLinearMap]

theorem planarPart_toroidalInclusion :
    planarPartMap.comp toroidalInclusionMap = 0 := by
  apply ContinuousLinearMap.ext
  intro value
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [planarPartMap, toroidalInclusionMap, LinearMap.toContinuousLinearMap]

theorem toroidalPart_planarInclusion :
    toroidalPartMap.comp planarInclusionMap = 0 := by
  apply ContinuousLinearMap.ext
  intro value
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  simp [toroidalPartMap, planarInclusionMap, LinearMap.toContinuousLinearMap]

theorem splitting_reconstruction :
    planarInclusionMap.comp planarPartMap + toroidalInclusionMap.comp toroidalPartMap =
      ContinuousLinearMap.id ℂ (ComplexEuclidean 3) := by
  apply ContinuousLinearMap.ext
  intro value
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [planarPartMap, planarInclusionMap, toroidalPartMap, toroidalInclusionMap,
      LinearMap.toContinuousLinearMap]

theorem valueMapJet_id {dimension : ℕ} (field : ClosedJet dimension) :
    valueMapJet (ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)) field = field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simp only [valueMapJet_value, ContinuousLinearMap.id_apply]

theorem valueMapCore_comp {firstDimension secondDimension thirdDimension : ℕ}
    (parameters : PhaseParameters)
    (first : ComplexEuclidean firstDimension →L[ℂ] ComplexEuclidean secondDimension)
    (second : ComplexEuclidean secondDimension →L[ℂ] ComplexEuclidean thirdDimension)
    (field : ACore parameters firstDimension) :
    valueMapCore second parameters (valueMapCore first parameters field) =
      valueMapCore (second.comp first) parameters field := by
  apply Subtype.ext
  funext cell
  exact valueMapJet_comp first second (field.1 cell)

theorem valueMapCore_id {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) :
    valueMapCore (ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)) parameters field = field := by
  apply Subtype.ext
  funext cell
  exact valueMapJet_id (field.1 cell)

theorem valueMapCore_zero_map {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters sourceDimension) :
    valueMapCore (0 : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
      parameters field = 0 := by
  apply Subtype.ext
  funext cell
  exact valueMapJet_zero (field.1 cell)

/-- Planar part on original all-grade coefficient fields. -/
def planarPartCore (parameters : PhaseParameters) :
    ACore parameters 3 →ₗ[ℂ] ACore parameters 2 :=
  valueMapCore planarPartMap parameters

/-- Toroidal part on original all-grade coefficient fields. -/
def toroidalPartCore (parameters : PhaseParameters) :
    ACore parameters 3 →ₗ[ℂ] ACore parameters 1 :=
  valueMapCore toroidalPartMap parameters

/-- Planar inclusion on original all-grade coefficient fields. -/
def planarInclusionCore (parameters : PhaseParameters) :
    ACore parameters 2 →ₗ[ℂ] ACore parameters 3 :=
  valueMapCore planarInclusionMap parameters

/-- Toroidal inclusion on original all-grade coefficient fields. -/
def toroidalInclusionCore (parameters : PhaseParameters) :
    ACore parameters 1 →ₗ[ℂ] ACore parameters 3 :=
  valueMapCore toroidalInclusionMap parameters

theorem planarPartCore_planarInclusionCore (parameters : PhaseParameters)
    (field : ACore parameters 2) :
    planarPartCore parameters (planarInclusionCore parameters field) = field := by
  unfold planarPartCore planarInclusionCore
  rw [valueMapCore_comp, planarPart_planarInclusion, valueMapCore_id]

theorem toroidalPartCore_toroidalInclusionCore (parameters : PhaseParameters)
    (field : ACore parameters 1) :
    toroidalPartCore parameters (toroidalInclusionCore parameters field) = field := by
  unfold toroidalPartCore toroidalInclusionCore
  rw [valueMapCore_comp, toroidalPart_toroidalInclusion, valueMapCore_id]

theorem planarPartCore_toroidalInclusionCore (parameters : PhaseParameters)
    (field : ACore parameters 1) :
    planarPartCore parameters (toroidalInclusionCore parameters field) = 0 := by
  unfold planarPartCore toroidalInclusionCore
  rw [valueMapCore_comp, planarPart_toroidalInclusion, valueMapCore_zero_map]

theorem toroidalPartCore_planarInclusionCore (parameters : PhaseParameters)
    (field : ACore parameters 2) :
    toroidalPartCore parameters (planarInclusionCore parameters field) = 0 := by
  unfold toroidalPartCore planarInclusionCore
  rw [valueMapCore_comp, toroidalPart_planarInclusion, valueMapCore_zero_map]

theorem valueMapJet_add_map {sourceDimension targetDimension : ℕ}
    (first second : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : ClosedJet sourceDimension) :
    valueMapJet (first + second) field = valueMapJet first field + valueMapJet second field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simp only [valueMapJet_value, add_apply, closedJet_value_add,
    ContinuousMap.add_apply]

theorem valueMapCore_add_map {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters)
    (first second : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : ACore parameters sourceDimension) :
    valueMapCore (first + second) parameters field =
      valueMapCore first parameters field + valueMapCore second parameters field := by
  apply Subtype.ext
  funext cell
  exact valueMapJet_add_map first second (field.1 cell)

theorem splittingCore_reconstruction (parameters : PhaseParameters)
    (field : ACore parameters 3) :
    planarInclusionCore parameters (planarPartCore parameters field) +
      toroidalInclusionCore parameters (toroidalPartCore parameters field) = field := by
  unfold planarInclusionCore planarPartCore toroidalInclusionCore toroidalPartCore
  rw [valueMapCore_comp, valueMapCore_comp, ← valueMapCore_add_map,
    splitting_reconstruction, valueMapCore_id]

end Grad.Constraints.Gauges
