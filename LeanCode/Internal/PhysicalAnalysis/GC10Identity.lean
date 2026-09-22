import GC10Fourier

noncomputable section

set_option maxHeartbeats 3000000

open Set
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open Grad.GaugeCoefficients.Envelope
open scoped BigOperators ContDiff ENNReal Topology

namespace Grad.GaugeCoefficients.Algebra

def identitySmoothValue (dimension : ℕ) :
    ContinuousMap ClosedDisk (OperatorValue dimension dimension) :=
  ContinuousMap.const ClosedDisk (ContinuousLinearMap.id ℂ (PhysicalValue dimension))

theorem closedDiskLift_identitySmoothValue_eventually
    (dimension : ℕ) (point : SpatialPlane) (inside : point ∈ openUnitDisk) :
    closedDiskLift (identitySmoothValue dimension) =ᶠ[𝓝 point]
      fun _ : SpatialPlane => ContinuousLinearMap.id ℂ (PhysicalValue dimension) := by
  filter_upwards [openUnitDisk_isOpen.mem_nhds inside] with candidate candidateInside
  unfold closedDiskLift
  rw [dif_pos (openDiskMembershipClosed candidate candidateInside)]
  rfl

def identitySmoothDerivative (dimension : ℕ) (index : CartesianMultiIndex) :
    ContinuousMap ClosedDisk (OperatorValue dimension dimension) :=
  if cartesianOrder index = 0 then identitySmoothValue dimension else 0

def identitySmoothOperatorJet (dimension : ℕ) :
    SmoothOperatorJet dimension dimension where
  value := identitySmoothValue dimension
  smoothInterior := by
    intro point inside
    exact (contDiffAt_const.congr_of_eventuallyEq
      (closedDiskLift_identitySmoothValue_eventually dimension point inside)).contDiffWithinAt
  derivativeExists := by
    intro index
    refine ⟨identitySmoothDerivative dimension index, ?_⟩
    intro point inside
    have localEquality :=
      closedDiskLift_identitySmoothValue_eventually dimension point.val inside
    unfold identitySmoothDerivative
    by_cases orderZero : cartesianOrder index = 0
    · rw [if_pos orderZero]
      rcases index with ⟨first, second⟩
      change first + second = 0 at orderZero
      have firstZero : first = 0 := by omega
      have secondZero : second = 0 := by omega
      subst first
      subst second
      change identitySmoothValue dimension point =
        closedDiskLift (identitySmoothValue dimension) point.val
      unfold identitySmoothValue closedDiskLift
      rw [dif_pos (openDiskMembershipClosed point.val inside)]
    · rw [if_neg orderZero]
      unfold cartesianMultiDerivative cartesianDerivative
      have derivativeEquality :=
        (localEquality.iteratedFDeriv ℝ (cartesianOrder index)).eq_of_nhds
      rw [derivativeEquality]
      rw [iteratedFDeriv_const_of_ne orderZero
        (ContinuousLinearMap.id ℂ (PhysicalValue dimension))]
      rfl

theorem identitySmoothOperatorJet_zero_derivative (dimension : ℕ) :
    smoothOperatorDerivative (identitySmoothOperatorJet dimension) (0, 0) =
      identitySmoothValue dimension := by
  apply continuousMap_eq_of_openDisk
  intro point inside
  change (Classical.choose
    ((identitySmoothOperatorJet dimension).derivativeExists (0, 0))) point = _
  calc
    (Classical.choose
        ((identitySmoothOperatorJet dimension).derivativeExists (0, 0))) point =
      cartesianMultiDerivative (0, 0)
        (closedDiskLift (identitySmoothValue dimension)) point.val :=
      Classical.choose_spec
        ((identitySmoothOperatorJet dimension).derivativeExists (0, 0)) point inside
    _ = identitySmoothValue dimension point := by
      change closedDiskLift (identitySmoothValue dimension) point.val =
        identitySmoothValue dimension point
      unfold identitySmoothValue closedDiskLift
      rw [dif_pos (openDiskMembershipClosed point.val inside)]

theorem coefficientScale_cell_zero_grade_zero
    (L sigma gamma ell : ℝ) (point : ClosedDisk) :
    coefficientScale L sigma gamma ell 0 0 zeroDerivativeIndex point = 1 := by
  simp [coefficientScale, originalEnvelope, scaledCellWeight, derivativeOrder,
    zeroDerivativeIndex]

theorem identityWeightedSingle_apply
    (L sigma gamma ell : ℝ) (dimension : ℕ) (cell : ℤ) :
    weightedSingle L sigma gamma ell 0 0 (identitySmoothOperatorJet dimension)
        (cell, zeroDerivativeIndex) =
      if cell = 0 then identitySmoothValue dimension else 0 := by
  rw [weightedSingle_apply]
  by_cases same : cell = 0
  · subst cell
    rw [if_pos rfl]
    apply ContinuousMap.ext
    intro point
    change (coefficientScale L sigma gamma ell 0 0 zeroDerivativeIndex point : ℂ) •
      smoothOperatorDerivative (identitySmoothOperatorJet dimension) (0, 0) point =
        identitySmoothValue dimension point
    rw [identitySmoothOperatorJet_zero_derivative,
      coefficientScale_cell_zero_grade_zero]
    exact one_smul ℂ _
  · simp only [if_neg same]

def identityCoefficient (L sigma gamma ell : ℝ) (dimension : ℕ) :
    Coefficient L sigma gamma ell 0 dimension dimension :=
  coreInclusion L sigma gamma ell 0 dimension dimension
    ⟨weightedSingle L sigma gamma ell 0 0 (identitySmoothOperatorJet dimension),
      Submodule.subset_span (Set.mem_range.mpr
        ⟨(0, identitySmoothOperatorJet dimension), rfl⟩)⟩

theorem identityCoefficient_weightedDerivative
    (L sigma gamma ell : ℝ) (dimension : ℕ) (cell : ℤ) :
    weightedDerivative (identityCoefficient L sigma gamma ell dimension)
        cell zeroDerivativeIndex =
      if cell = 0 then identitySmoothValue dimension else 0 :=
  identityWeightedSingle_apply L sigma gamma ell dimension cell

theorem identityCoefficient_value
    (L sigma gamma ell : ℝ) (dimension : ℕ) (cell : ℤ) (point : ClosedDisk) :
    coefficientValue (identityCoefficient L sigma gamma ell dimension) cell point =
      if cell = 0 then ContinuousLinearMap.id ℂ (PhysicalValue dimension) else 0 := by
  unfold coefficientValue
  change ((coefficientScale L sigma gamma ell 0 cell zeroDerivativeIndex point : ℂ)⁻¹) •
      weightedDerivative (identityCoefficient L sigma gamma ell dimension)
        cell zeroDerivativeIndex point = _
  have weightedValue := congrArg (fun value :
      ContinuousMap ClosedDisk (OperatorValue dimension dimension) => value point)
    (identityCoefficient_weightedDerivative L sigma gamma ell dimension cell)
  rw [weightedValue]
  by_cases same : cell = 0
  · subst cell
    rw [if_pos rfl]
    change ((coefficientScale L sigma gamma ell 0 0 zeroDerivativeIndex point : ℂ)⁻¹) •
      identitySmoothValue dimension point = ContinuousLinearMap.id ℂ (PhysicalValue dimension)
    rw [coefficientScale_cell_zero_grade_zero]
    norm_num [identitySmoothValue]
  · simp only [if_neg same]
    change ((coefficientScale L sigma gamma ell 0 cell zeroDerivativeIndex point : ℂ)⁻¹) •
      (0 : OperatorValue dimension dimension) = 0
    apply ContinuousLinearMap.ext
    intro value
    simp

theorem derivativeIndex_zero_eq (index : DerivativeIndex 0) :
    index = zeroDerivativeIndex := by
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    omega
  · apply Fin.ext
    omega

theorem derivativeIndex_zero_univ :
    (Finset.univ : Finset (DerivativeIndex 0)) = {zeroDerivativeIndex} := by
  ext index
  simp only [Finset.mem_univ, Finset.mem_singleton]
  exact ⟨fun _ => derivativeIndex_zero_eq index, fun _ => trivial⟩

theorem identitySmoothValue_norm (dimension : ℕ) (positive : 0 < dimension) :
    ‖identitySmoothValue dimension‖ = 1 := by
  let : Nonempty (Fin dimension) := ⟨⟨0, positive⟩⟩
  let : Nonempty ClosedDisk :=
    ⟨⟨(0 : SpatialPlane), by simp [closedUnitDisk]⟩⟩
  rw [ContinuousMap.norm_eq_iSup_norm]
  simp only [identitySmoothValue, ContinuousMap.const_apply,
    ContinuousLinearMap.norm_id]
  rw [ciSup_const]

theorem identityCoefficient_norm
    (L sigma gamma ell : ℝ) (dimension : ℕ) (positive : 0 < dimension) :
    ‖identityCoefficient L sigma gamma ell dimension‖ = 1 := by
  rw [coefficient_norm_formula]
  calc
    (∑' cell : ℤ, ∑ index : DerivativeIndex 0,
        ‖weightedDerivative (identityCoefficient L sigma gamma ell dimension) cell index‖) =
        ∑' cell : ℤ,
          ‖weightedDerivative (identityCoefficient L sigma gamma ell dimension)
            cell zeroDerivativeIndex‖ := by
      apply tsum_congr
      intro cell
      rw [derivativeIndex_zero_univ]
      simp only [Finset.sum_singleton]
    _ = ∑' cell : ℤ, if cell = 0 then 1 else 0 := by
      apply tsum_congr
      intro cell
      rw [identityCoefficient_weightedDerivative]
      by_cases same : cell = 0
      · simp only [if_pos same]
        exact identitySmoothValue_norm dimension positive
      · simp only [if_neg same]
        show ‖(0 : ContinuousMap ClosedDisk (OperatorValue dimension dimension))‖ = 0
        exact @norm_zero
          (ContinuousMap ClosedDisk (OperatorValue dimension dimension)) inferInstance
    _ = 1 := by
      rw [tsum_eq_single 0]
      · simp
      · intro cell different
        simp only [if_neg different]

theorem identityCoefficient_fourier
    (L sigma gamma ell : ℝ) (dimension : ℕ) (angle : ℝ) (point : ClosedDisk) :
    fourierEvaluation (identityCoefficient L sigma gamma ell dimension) angle point =
      ContinuousLinearMap.id ℂ (PhysicalValue dimension) := by
  change (∑' cell : ℤ, fourierPhase cell angle •
      coefficientValue (identityCoefficient L sigma gamma ell dimension) cell point) = _
  rw [tsum_eq_single 0]
  · rw [identityCoefficient_value]
    apply ContinuousLinearMap.ext
    intro value
    simp [fourierPhase]
  · intro cell different
    rw [identityCoefficient_value, if_neg different]
    apply ContinuousLinearMap.ext
    intro value
    simp

theorem identityCoefficient_goal (L sigma gamma ell : ℝ) :
    IdentityGoal L sigma gamma ell (identityCoefficient L sigma gamma ell) := by
  constructor
  · exact identityCoefficient_norm L sigma gamma ell
  · exact identityCoefficient_fourier L sigma gamma ell

end Grad.GaugeCoefficients.Algebra
