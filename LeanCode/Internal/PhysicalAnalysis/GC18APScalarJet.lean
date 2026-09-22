import GC18APProduct
import GC18APKernel

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators ContDiff Topology

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Radial
open Grad.AnalyticWeights.Higher

def apGlobalOperatorValue {input output : ℕ} (function : SpatialPlane → OperatorValue input output)
    (smooth : ContDiff ℝ ∞ function) : C(ClosedDisk, OperatorValue input output) :=
  ⟨fun point => function point.val, smooth.continuous.comp continuous_subtype_val⟩

theorem apGlobalOperatorValue_eventually {input output : ℕ} (function : SpatialPlane → OperatorValue input output)
    (smooth : ContDiff ℝ ∞ function) (point : SpatialPlane) (inside : point ∈ openUnitDisk) :
    closedDiskLift (apGlobalOperatorValue function smooth) =ᶠ[𝓝 point] function := by
  filter_upwards [openUnitDisk_isOpen.mem_nhds inside] with other membership
  simp only [closedDiskLift, openDiskMembershipClosed other membership, dite_true]
  rfl

def apGlobalOperatorDerivative {input output : ℕ} (function : SpatialPlane → OperatorValue input output)
    (smooth : ContDiff ℝ ∞ function) (index : CartesianMultiIndex) : C(ClosedDisk, OperatorValue input output) where
  toFun point := cartesianMultiDerivative index function point.val
  continuous_toFun := by
    have tensors : Continuous (fun point : ClosedDisk => iteratedFDeriv ℝ (cartesianOrder index) function point.val) :=
      (smooth.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (cartesianOrder index : ℕ∞) ≤ ⊤))).comp continuous_subtype_val
    dsimp [cartesianMultiDerivative, cartesianDerivative]
    fun_prop

def apGlobalOperatorJet {input output : ℕ} (function : SpatialPlane → OperatorValue input output)
    (smooth : ContDiff ℝ ∞ function) : SmoothOperatorJet input output where
  value := apGlobalOperatorValue function smooth
  smoothInterior := by
    intro point inside
    exact (smooth.contDiffAt.congr_of_eventuallyEq (apGlobalOperatorValue_eventually function smooth point inside)).contDiffWithinAt
  derivativeExists index := ⟨apGlobalOperatorDerivative function smooth index, by
    intro point inside
    have equality := (apGlobalOperatorValue_eventually function smooth point.val inside).iteratedFDeriv ℝ (cartesianOrder index)
    exact congrArg (fun mapping => mapping (fun position => spatialBasis (cartesianMultiIndexWord index position)))
      equality.eq_of_nhds.symm⟩

theorem apGlobalOperatorJet_derivative {input output : ℕ} (function : SpatialPlane → OperatorValue input output)
    (smooth : ContDiff ℝ ∞ function) (index : CartesianMultiIndex) (point : ClosedDisk) :
    smoothOperatorDerivative (apGlobalOperatorJet function smooth) index point = cartesianMultiDerivative index function point.val := by
  have specification : IsOperatorDerivativeExtension (apGlobalOperatorValue function smooth) index
      (apGlobalOperatorDerivative function smooth index) := by
    intro point inside
    have equality := (apGlobalOperatorValue_eventually function smooth point.val inside).iteratedFDeriv ℝ (cartesianOrder index)
    exact congrArg (fun mapping => mapping (fun position => spatialBasis (cartesianMultiIndexWord index position)))
      equality.eq_of_nhds.symm
  rw [smoothOperatorDerivative_eq_of_spec _ _ _ specification]
  rfl

def apScalarOperatorJet (dimension : ℕ) (scalar : SpatialPlane → ℝ) (smooth : ContDiff ℝ ∞ scalar) :
    SmoothOperatorJet dimension dimension :=
  apGlobalOperatorJet (fun point => scalar point • ContinuousLinearMap.id ℂ (PhysicalValue dimension))
    (smooth.smul contDiff_const)

theorem apScalarOperatorJet_derivative (dimension : ℕ) (scalar : SpatialPlane → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (index : CartesianMultiIndex) (point : ClosedDisk) :
    smoothOperatorDerivative (apScalarOperatorJet dimension scalar smooth) index point =
      orderedDerivative (cartesianOrder index) (cartesianMultiIndexWord index) scalar point.val •
        ContinuousLinearMap.id ℂ (PhysicalValue dimension) := by
  rw [apScalarOperatorJet, apGlobalOperatorJet_derivative]
  let mapping : ℝ →L[ℝ] OperatorValue dimension dimension :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (ContinuousLinearMap.id ℂ (PhysicalValue dimension))
  change iteratedFDeriv ℝ (cartesianOrder index) (mapping ∘ scalar) point.val
    (fun position => spatialBasis (cartesianMultiIndexWord index position)) = _
  rw [mapping.iteratedFDeriv_comp_left smooth.contDiffAt (by exact_mod_cast (le_top : (cartesianOrder index : ℕ∞) ≤ ⊤))]
  rfl

theorem apScalarWeightedJet_eq_product {dimension : ℕ} (scalar : SpatialPlane → ℝ)
    (smooth : ContDiff ℝ ∞ scalar) (field : ClosedJet dimension) :
    smoothScalarWeightedJet scalar smooth field = apProductJet (apScalarOperatorJet dimension scalar smooth) field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [apProductJet_value]
  rfl

theorem apScalarWeightedJet_derivative {dimension grade : ℕ} (scalar : SpatialPlane → ℝ)
    (smooth : ContDiff ℝ ∞ scalar) (field : ClosedJet dimension) (index : DerivativeIndex grade) (point : ClosedDisk) :
    closedMultiDerivative (smoothScalarWeightedJet scalar smooth field) (derivativeMultiIndex index) point =
      ∑ split : DerivativeSplit index, (splitMultiplicity index split : ℂ) •
        (orderedDerivative (derivativeOrder (lowerDerivativeIndex index split))
          (cartesianMultiIndexWord (derivativeMultiIndex (lowerDerivativeIndex index split))) scalar point.val •
          closedMultiDerivative field (derivativeMultiIndex (upperDerivativeIndex index split)) point) := by
  rw [apScalarWeightedJet_eq_product, apProductJet_derivative]
  apply Finset.sum_congr rfl
  intro split _
  rw [apScalarOperatorJet_derivative, smul_apply, ContinuousLinearMap.id_apply]
  rfl

end Grad.GaugeCoefficients.Physical.RadialLedger
