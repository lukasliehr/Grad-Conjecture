import GC13Angular

noncomputable section

set_option maxHeartbeats 5000000

open Set
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open scoped BigOperators ContDiff Topology

namespace Grad.GaugeCoefficients.Radial

open Grad.GaugeCoefficients.Algebra

def radialLinearMap (time : ℝ) : SpatialPlane →L[ℝ] SpatialPlane :=
  unitClamp time • ContinuousLinearMap.id ℝ SpatialPlane

@[simp] theorem radialLinearMap_apply (time : ℝ) (point : SpatialPlane) :
    radialLinearMap time point = unitClamp time • point := by
  rfl

theorem radialLinearMap_maps_openUnitDisk (time : ℝ) :
    MapsTo (radialLinearMap time) openUnitDisk openUnitDisk := by
  intro point inside
  change ‖point‖ < 1 at inside
  change ‖unitClamp time • point‖ < 1
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (unitClamp_nonnegative time)]
  calc
    unitClamp time * ‖point‖ ≤ 1 * ‖point‖ :=
      mul_le_mul_of_nonneg_right (unitClamp_le_one time) (norm_nonneg point)
    _ < 1 := by simpa using inside

theorem continuous_radialPoint (time : ℝ) :
    Continuous (radialPoint time) := by
  exact (((continuous_const : Continuous fun _ : ClosedDisk => unitClamp time).smul
    continuous_subtype_val).subtype_mk _)

def radialJetValue {inputDimension outputDimension : ℕ}
    (time : ℝ) (field : SmoothOperatorJet inputDimension outputDimension) :
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) where
  toFun point := field.value (radialPoint time point)
  continuous_toFun := field.value.continuous.comp (continuous_radialPoint time)

theorem closedDiskLift_radialJetValue_eqOn
    {inputDimension outputDimension : ℕ}
    (time : ℝ) (field : SmoothOperatorJet inputDimension outputDimension) :
    Set.EqOn (closedDiskLift (radialJetValue time field))
      (fun point => closedDiskLift field.value (radialLinearMap time point))
      openUnitDisk := by
  intro point inside
  have pointClosed : point ∈ closedUnitDisk :=
    openDiskMembershipClosed point inside
  have imageInside : radialLinearMap time point ∈ openUnitDisk :=
    radialLinearMap_maps_openUnitDisk time inside
  have imageClosed : radialLinearMap time point ∈ closedUnitDisk :=
    openDiskMembershipClosed _ imageInside
  simp only [closedDiskLift, pointClosed, imageClosed, dite_true]
  rfl

def radialDerivativeExtension {inputDimension outputDimension : ℕ}
    (time : ℝ) (field : SmoothOperatorJet inputDimension outputDimension)
    (index : CartesianMultiIndex) :
    ContinuousMap ClosedDisk (OperatorValue inputDimension outputDimension) where
  toFun point := ((unitClamp time ^ cartesianOrder index : ℝ) : ℂ) •
    smoothOperatorDerivative field index (radialPoint time point)
  continuous_toFun :=
    (continuous_const : Continuous fun _ : ClosedDisk =>
      ((unitClamp time ^ cartesianOrder index : ℝ) : ℂ)).smul
      ((smoothOperatorDerivative field index).continuous.comp
        (continuous_radialPoint time))

theorem radial_iteratedFDeriv
    {inputDimension outputDimension rank : ℕ}
    (time : ℝ) (field : SmoothOperatorJet inputDimension outputDimension)
    (point : SpatialPlane) (inside : point ∈ openUnitDisk) :
    iteratedFDeriv ℝ rank
        (closedDiskLift (radialJetValue time field)) point =
      (iteratedFDeriv ℝ rank (closedDiskLift field.value)
          (radialLinearMap time point)).compContinuousLinearMap
        (fun _ => radialLinearMap time) := by
  have imageInside : radialLinearMap time point ∈ openUnitDisk :=
    radialLinearMap_maps_openUnitDisk time inside
  have preimageOpen : IsOpen (radialLinearMap time ⁻¹' openUnitDisk) :=
    openUnitDisk_isOpen.preimage (radialLinearMap time).continuous
  have preimageInside : point ∈ radialLinearMap time ⁻¹' openUnitDisk :=
    imageInside
  have agreement := iteratedFDerivWithin_congr (𝕜 := ℝ)
    (closedDiskLift_radialJetValue_eqOn time field) inside rank
  repeat rw [iteratedFDerivWithin_of_isOpen rank openUnitDisk_isOpen inside] at agreement
  have chain := (radialLinearMap time).iteratedFDerivWithin_comp_right
    field.smoothInterior openUnitDisk_isOpen.uniqueDiffOn
      preimageOpen.uniqueDiffOn imageInside
        (show (rank : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
  rw [iteratedFDerivWithin_of_isOpen rank preimageOpen preimageInside,
    iteratedFDerivWithin_of_isOpen rank openUnitDisk_isOpen imageInside] at chain
  exact agreement.trans chain

theorem radial_cartesianMultiDerivative
    {inputDimension outputDimension : ℕ}
    (time : ℝ) (field : SmoothOperatorJet inputDimension outputDimension)
    (index : CartesianMultiIndex) (point : SpatialPlane)
    (inside : point ∈ openUnitDisk) :
    cartesianMultiDerivative index
        (closedDiskLift (radialJetValue time field)) point =
      ((unitClamp time ^ cartesianOrder index : ℝ) : ℂ) •
        cartesianMultiDerivative index (closedDiskLift field.value)
          (radialLinearMap time point) := by
  unfold cartesianMultiDerivative cartesianDerivative
  rw [radial_iteratedFDeriv time field point inside,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change (iteratedFDeriv ℝ (cartesianOrder index) (closedDiskLift field.value)
      (radialLinearMap time point))
        (fun position => unitClamp time •
          spatialBasis (cartesianMultiIndexWord index position)) = _
  rw [ContinuousMultilinearMap.map_smul_univ]
  rw [show (∏ _position : Fin (cartesianOrder index), unitClamp time) =
      unitClamp time ^ cartesianOrder index by simp]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ)
    (unitClamp time ^ cartesianOrder index)
    ((iteratedFDeriv ℝ (cartesianOrder index) (closedDiskLift field.value)
      (radialLinearMap time point))
        (fun position => spatialBasis (cartesianMultiIndexWord index position)))

theorem radialDerivativeExtension_spec
    {inputDimension outputDimension : ℕ}
    (time : ℝ) (field : SmoothOperatorJet inputDimension outputDimension)
    (index : CartesianMultiIndex) :
    IsOperatorDerivativeExtension (radialJetValue time field) index
      (radialDerivativeExtension time field index) := by
  intro point inside
  rw [radial_cartesianMultiDerivative time field index point.val inside]
  have fieldSpec : smoothOperatorDerivative field index (radialPoint time point) =
      cartesianMultiDerivative index (closedDiskLift field.value)
        (radialPoint time point).val := by
    exact Classical.choose_spec (field.derivativeExists index)
      (radialPoint time point)
        (radialLinearMap_maps_openUnitDisk time inside)
  change ((radialDerivativeExtension time field index).toFun point) = _
  dsimp only [radialDerivativeExtension]
  rw [fieldSpec]
  rfl

def radialSmoothOperatorJet {inputDimension outputDimension : ℕ}
    (time : ℝ) (field : SmoothOperatorJet inputDimension outputDimension) :
    SmoothOperatorJet inputDimension outputDimension where
  value := radialJetValue time field
  smoothInterior := by
    have composed := field.smoothInterior.comp
      (radialLinearMap time).contDiff.contDiffOn
        (radialLinearMap_maps_openUnitDisk time)
    exact composed.congr fun point inside => by
      simpa [Function.comp_def] using
        closedDiskLift_radialJetValue_eqOn time field inside
  derivativeExists := fun index =>
    ⟨radialDerivativeExtension time field index,
      radialDerivativeExtension_spec time field index⟩

theorem radialSmoothOperatorJet_derivative
    {inputDimension outputDimension : ℕ}
    (time : ℝ) (field : SmoothOperatorJet inputDimension outputDimension)
    (index : CartesianMultiIndex) :
    smoothOperatorDerivative (radialSmoothOperatorJet time field) index =
      radialDerivativeExtension time field index := by
  exact smoothOperatorDerivative_eq_of_spec _ _ _
    (radialDerivativeExtension_spec time field index)

@[simp] theorem radialSmoothOperatorJet_derivative_apply
    {inputDimension outputDimension : ℕ}
    (time : ℝ) (field : SmoothOperatorJet inputDimension outputDimension)
    (index : CartesianMultiIndex) (point : ClosedDisk) :
    smoothOperatorDerivative (radialSmoothOperatorJet time field) index point =
      ((unitClamp time ^ cartesianOrder index : ℝ) : ℂ) •
        smoothOperatorDerivative field index (radialPoint time point) := by
  rw [radialSmoothOperatorJet_derivative]
  change ((radialDerivativeExtension time field index).toFun point) = _
  rfl

end Grad.GaugeCoefficients.Radial
