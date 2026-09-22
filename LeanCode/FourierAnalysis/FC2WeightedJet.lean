import FC2Phase
import SP1Bilinear

noncomputable section

open Set
open scoped BigOperators ContDiff Topology

namespace Grad.CartesianState

open Grad.ClosedJets
open Grad.RepresentedKernel.SpatialProduct

def smoothScalarWeightedValue {dimension : ℕ} (scalar : SpatialPlane → ℝ)
    (scalarContinuous : Continuous scalar) (field : ClosedJet dimension) :
    ContinuousMap ClosedDisk (ComplexEuclidean dimension) where
  toFun point := scalar point.val • field.value point
  continuous_toFun :=
    (scalarContinuous.comp continuous_subtype_val).smul field.value.continuous

theorem closedDiskLift_smoothScalarWeightedValue {dimension : ℕ}
    (scalar : SpatialPlane → ℝ) (scalarContinuous : Continuous scalar)
    (field : ClosedJet dimension) :
    closedDiskLift (smoothScalarWeightedValue scalar scalarContinuous field) =
      fun point => scalar point • closedDiskLift field.value point := by
  funext point
  by_cases membership : point ∈ closedUnitDisk <;>
    simp [closedDiskLift, smoothScalarWeightedValue, membership]

def smoothScalarDerivativeFactor (scalar : SpatialPlane → ℝ)
    (scalarSmooth : ContDiff ℝ ∞ scalar) (order : ℕ) (word : CartesianWord order)
    (selected : Finset (Fin order)) : ContinuousMap ClosedDisk ℝ where
  toFun point := selectedDerivative (fun position => spatialBasis (word position))
    selected scalar point.val
  continuous_toFun := by
    change Continuous ((fun source : SpatialPlane =>
      selectedDerivative (fun position => spatialBasis (word position))
        selected scalar source) ∘ Subtype.val)
    apply Continuous.comp _ continuous_subtype_val
    rw [continuous_iff_continuousAt]
    intro point
    exact (differentiable_selected scalarSmooth.contDiffAt
      (fun position => spatialBasis (word position)) selected).continuousAt

def smoothScalarDerivativeExtension {dimension : ℕ}
    (scalar : SpatialPlane → ℝ) (scalarSmooth : ContDiff ℝ ∞ scalar)
    (field : ClosedJet dimension) (order : ℕ) (word : CartesianWord order) :
    ContinuousMap ClosedDisk (ComplexEuclidean dimension) where
  toFun point := ∑ selected : Finset (Fin order),
    smoothScalarDerivativeFactor scalar scalarSmooth order word selected point •
      closedDerivative field selectedᶜ.card (subword word selectedᶜ) point
  continuous_toFun := by
    apply continuous_finsetSum
    intro selected _
    exact (smoothScalarDerivativeFactor scalar scalarSmooth order word selected).continuous.smul
      (closedDerivative field selectedᶜ.card (subword word selectedᶜ)).continuous

theorem smoothScalarDerivativeExtension_spec {dimension : ℕ}
    (scalar : SpatialPlane → ℝ) (scalarSmooth : ContDiff ℝ ∞ scalar)
    (field : ClosedJet dimension) (order : ℕ) (word : CartesianWord order) :
    IsCartesianExtension (smoothScalarWeightedValue scalar scalarSmooth.continuous field) order word
      (smoothScalarDerivativeExtension scalar scalarSmooth field order word) := by
  intro point membership
  rw [closedDiskLift_smoothScalarWeightedValue]
  have productRule := bilinear ℝ (ComplexEuclidean dimension) (ComplexEuclidean dimension)
    (ContinuousLinearMap.lsmul ℝ ℝ) openUnitDisk openUnitDisk_isOpen scalar
      (closedDiskLift field.value) scalarSmooth.contDiffOn field.smoothInterior order
      (fun position => spatialBasis (word position)) point.val membership
  have productRule' :
      iteratedFDeriv ℝ order
          (fun source => scalar source • closedDiskLift field.value source) point.val
          (fun position => spatialBasis (word position)) =
        ∑ selected : Finset (Fin order),
          selectedDerivative (fun position => spatialBasis (word position))
              selected scalar point.val •
            selectedDerivative (fun position => spatialBasis (word position))
              selectedᶜ (closedDiskLift field.value) point.val := by
    simpa using productRule
  rw [cartesianDerivative, productRule']
  change
    (∑ selected : Finset (Fin order),
      selectedDerivative (fun position => spatialBasis (word position)) selected scalar point.val •
        closedDerivative field selectedᶜ.card (subword word selectedᶜ) point) = _
  apply Finset.sum_congr rfl
  intro selected _
  congr 1
  rw [closedDerivative_spec field selectedᶜ.card (subword word selectedᶜ) point membership]
  rfl

def smoothScalarWeightedJet {dimension : ℕ} (scalar : SpatialPlane → ℝ)
    (scalarSmooth : ContDiff ℝ ∞ scalar) (field : ClosedJet dimension) : ClosedJet dimension where
  value := smoothScalarWeightedValue scalar scalarSmooth.continuous field
  smoothInterior := by
    rw [closedDiskLift_smoothScalarWeightedValue]
    exact scalarSmooth.contDiffOn.smul field.smoothInterior
  derivativeExists order word :=
    ⟨smoothScalarDerivativeExtension scalar scalarSmooth field order word,
      smoothScalarDerivativeExtension_spec scalar scalarSmooth field order word⟩

def phaseWeightedJet {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field : ClosedJet dimension) : ClosedJet dimension :=
  smoothScalarWeightedJet (cartesianWeight parameters cell)
    (cartesianWeight_contDiff parameters cell) field

theorem phaseWeightedJet_value {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field : ClosedJet dimension) (point : ClosedDisk) :
    (phaseWeightedJet parameters cell field).value point =
      cartesianWeight parameters cell point.val • field.value point := rfl

theorem phaseWeightedJet_derivative {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field : ClosedJet dimension) (order : ℕ) (word : CartesianWord order) :
    closedDerivative (phaseWeightedJet parameters cell field) order word =
      smoothScalarDerivativeExtension (cartesianWeight parameters cell)
        (cartesianWeight_contDiff parameters cell) field order word := by
  symm
  apply cartesianExtension_unique
  exact smoothScalarDerivativeExtension_spec (cartesianWeight parameters cell)
    (cartesianWeight_contDiff parameters cell) field order word

theorem phaseWeightedJet_spec {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field : ClosedJet dimension) :
    IsPhaseWeighted parameters cell (phaseWeightedJet parameters cell field) field :=
  fun point => phaseWeightedJet_value parameters cell field point

theorem phaseWeightedJet_unique {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field candidate : ClosedJet dimension) (specification :
      IsPhaseWeighted parameters cell candidate field) :
    candidate = phaseWeightedJet parameters cell field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  exact specification point

theorem phaseWeightedJet_add {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (first second : ClosedJet dimension) :
    phaseWeightedJet parameters cell (closedJetAdd first second) =
      closedJetAdd (phaseWeightedJet parameters cell first)
        (phaseWeightedJet parameters cell second) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change cartesianWeight parameters cell point.val •
      (first.value point + second.value point) =
    cartesianWeight parameters cell point.val • first.value point +
      cartesianWeight parameters cell point.val • second.value point
  exact smul_add _ _ _

theorem phaseWeightedJet_complex_smul {dimension : ℕ} (parameters : PhaseParameters)
    (cell : ℤ) (scalar : ℂ) (field : ClosedJet dimension) :
    phaseWeightedJet parameters cell (closedJetSmul scalar field) =
      closedJetSmul scalar (phaseWeightedJet parameters cell field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change cartesianWeight parameters cell point.val • (scalar • field.value point) =
    scalar • (cartesianWeight parameters cell point.val • field.value point)
  exact smul_comm _ _ _

def cartesianInverseWeight (parameters : PhaseParameters) (cell : ℤ)
    (point : SpatialPlane) : ℝ :=
  Grad.AnalyticWeights.Calculus.inverseWeight parameters.sigma0 parameters.gamma 1 cell point

theorem cartesianInverseWeight_contDiff (parameters : PhaseParameters) (cell : ℤ) :
    ContDiff ℝ ∞ (cartesianInverseWeight parameters cell) := by
  exact (Grad.AnalyticWeights.Calculus.smoothGoal parameters.sigma0 parameters.gamma 1 cell).2.2

theorem cartesianWeight_mul_inverse (parameters : PhaseParameters) (cell : ℤ)
    (point : SpatialPlane) :
    cartesianWeight parameters cell point * cartesianInverseWeight parameters cell point = 1 := by
  exact (Grad.AnalyticWeights.Calculus.formulaGoal parameters.sigma0 parameters.gamma 1 cell point).2.2.2.2

def phaseInverseWeightedJet {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field : ClosedJet dimension) : ClosedJet dimension :=
  smoothScalarWeightedJet (cartesianInverseWeight parameters cell)
    (cartesianInverseWeight_contDiff parameters cell) field

theorem phaseWeightedJet_inverse_left {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field : ClosedJet dimension) :
    phaseWeightedJet parameters cell (phaseInverseWeightedJet parameters cell field) = field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change cartesianWeight parameters cell point.val •
      (cartesianInverseWeight parameters cell point.val • field.value point) = field.value point
  rw [smul_smul, cartesianWeight_mul_inverse]
  exact one_smul ℝ (field.value point)

theorem phaseWeightedJet_inverse_right {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field : ClosedJet dimension) :
    phaseInverseWeightedJet parameters cell (phaseWeightedJet parameters cell field) = field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change cartesianInverseWeight parameters cell point.val •
      (cartesianWeight parameters cell point.val • field.value point) = field.value point
  rw [smul_smul, mul_comm, cartesianWeight_mul_inverse]
  exact one_smul ℝ (field.value point)

end Grad.CartesianState
