import NGP01CoordinateBound

noncomputable section

set_option maxHeartbeats 800000

open Filter Set
open scoped ContDiff Topology

namespace Grad.CartesianState

open Grad.ClosedJets

local instance ngp01MixedCellPeriodPositive : Fact (0 < 2 * Real.pi) :=
  ⟨by positivity⟩

/-- Public quantitative bookkeeping for separating an arbitrary physical
coordinate word into its planar subword and number of cell derivatives. -/
structure EvaluationDerivativeIndex where
  planarOrder : ℕ
  planarWord : CartesianWord planarOrder
  cellOrder : ℕ

def evaluationDerivativeIndexZero : EvaluationDerivativeIndex where
  planarOrder := 0
  planarWord := emptyCartesianWord
  cellOrder := 0

def evaluationDerivativeIndexPrepend (coordinate : Fin 3)
    (index : EvaluationDerivativeIndex) : EvaluationDerivativeIndex :=
  if coordinate = 0 then
    { planarOrder := index.planarOrder + 1
      planarWord := Fin.cons 0 index.planarWord
      cellOrder := index.cellOrder }
  else if coordinate = 1 then
    { planarOrder := index.planarOrder + 1
      planarWord := Fin.cons 1 index.planarWord
      cellOrder := index.cellOrder }
  else
    { planarOrder := index.planarOrder
      planarWord := index.planarWord
      cellOrder := index.cellOrder + 1 }

def evaluationDerivativeIndexOfList (directions : List (Fin 3))
    (index : EvaluationDerivativeIndex := evaluationDerivativeIndexZero) :
    EvaluationDerivativeIndex :=
  directions.foldr evaluationDerivativeIndexPrepend index

theorem evaluationDerivativeIndexPrepend_total (coordinate : Fin 3)
    (index : EvaluationDerivativeIndex) :
    (evaluationDerivativeIndexPrepend coordinate index).planarOrder +
        (evaluationDerivativeIndexPrepend coordinate index).cellOrder =
      index.planarOrder + index.cellOrder + 1 := by
  fin_cases coordinate <;> simp [evaluationDerivativeIndexPrepend] <;> omega

theorem evaluationDerivativeIndexOfList_total (directions : List (Fin 3))
    (index : EvaluationDerivativeIndex) :
    (evaluationDerivativeIndexOfList directions index).planarOrder +
        (evaluationDerivativeIndexOfList directions index).cellOrder =
      index.planarOrder + index.cellOrder + directions.length := by
  induction directions with
  | nil => simp [evaluationDerivativeIndexOfList]
  | cons coordinate rest inductionHypothesis =>
    change
      (evaluationDerivativeIndexPrepend coordinate
          (evaluationDerivativeIndexOfList rest index)).planarOrder +
          (evaluationDerivativeIndexPrepend coordinate
            (evaluationDerivativeIndexOfList rest index)).cellOrder = _
    rw [evaluationDerivativeIndexPrepend_total, inductionHypothesis]
    simp only [List.length_cons]
    omega

def evaluationIndexSeries {dimension : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension)
    (index : EvaluationDerivativeIndex) :
    SpatialCell → ComplexEuclidean dimension :=
  ordinaryAmbientDerivativeSeries coefficients index.planarWord index.cellOrder

theorem evaluationIndexSeries_fderiv_basis
    {dimension : ℕ} (coefficients : OrdinaryCoefficientCore dimension)
    (index : EvaluationDerivativeIndex) (coordinate : Fin 3)
    (point : SpatialCell) (membership : point ∈ openUnitCylinder) :
    fderiv ℝ (evaluationIndexSeries coefficients index) point
        (spatialCellBasis coordinate) =
      evaluationIndexSeries coefficients
        (evaluationDerivativeIndexPrepend coordinate index) point := by
  fin_cases coordinate
  · simpa [evaluationIndexSeries, evaluationDerivativeIndexPrepend,
      fp17PlanarCoordinate] using
        (ordinaryAmbientDerivativeSeries_fderiv_planarBasis coefficients
          index.planarWord index.cellOrder point membership (0 : Fin 2))
  · simpa [evaluationIndexSeries, evaluationDerivativeIndexPrepend,
      fp17PlanarCoordinate] using
        (ordinaryAmbientDerivativeSeries_fderiv_planarBasis coefficients
          index.planarWord index.cellOrder point membership (1 : Fin 2))
  · simpa [evaluationIndexSeries, evaluationDerivativeIndexPrepend] using
        (ordinaryAmbientDerivativeSeries_fderiv_cellBasis coefficients
          index.planarWord index.cellOrder point membership)

def evaluationDirectionDerivative {dimension : ℕ} (coordinate : Fin 3)
    (function : SpatialCell → ComplexEuclidean dimension) :
    SpatialCell → ComplexEuclidean dimension :=
  fun point => fderiv ℝ function point (spatialCellBasis coordinate)

def evaluationListDerivative {dimension : ℕ} (directions : List (Fin 3))
    (function : SpatialCell → ComplexEuclidean dimension) :
    SpatialCell → ComplexEuclidean dimension :=
  directions.foldr evaluationDirectionDerivative function

theorem evaluationListDerivative_indexSeries
    {dimension : ℕ} (coefficients : OrdinaryCoefficientCore dimension)
    (directions : List (Fin 3)) (index : EvaluationDerivativeIndex) :
    Set.EqOn
      (evaluationListDerivative directions (evaluationIndexSeries coefficients index))
      (evaluationIndexSeries coefficients
        (evaluationDerivativeIndexOfList directions index))
      openUnitCylinder := by
  induction directions with
  | nil =>
    intro point membership
    rfl
  | cons coordinate rest inductionHypothesis =>
    intro point membership
    have localEquality :
        evaluationListDerivative rest (evaluationIndexSeries coefficients index) =ᶠ[𝓝 point]
          evaluationIndexSeries coefficients
            (evaluationDerivativeIndexOfList rest index) :=
      Filter.eventually_of_mem (openUnitCylinder_isOpen.mem_nhds membership)
        inductionHypothesis
    change fderiv ℝ
        (evaluationListDerivative rest (evaluationIndexSeries coefficients index)) point
          (spatialCellBasis coordinate) = _
    rw [localEquality.fderiv_eq]
    exact evaluationIndexSeries_fderiv_basis coefficients
      (evaluationDerivativeIndexOfList rest index) coordinate point membership

theorem evaluationListDerivative_ofFn
    {dimension order : ℕ} (word : MixedCartesianWord order)
    (function : SpatialCell → ComplexEuclidean dimension)
    (smooth : ContDiffOn ℝ ∞ function openUnitCylinder) :
    Set.EqOn (evaluationListDerivative (List.ofFn word) function)
      (fun point => mixedCartesianDerivative order word function point)
      openUnitCylinder := by
  induction order with
  | zero =>
    intro point membership
    rfl
  | succ order inductionHypothesis =>
    intro point membership
    rw [List.ofFn_succ]
    have congruence :
        evaluationDirectionDerivative (word 0)
            (evaluationListDerivative (List.ofFn (Fin.tail word)) function) point =
          evaluationDirectionDerivative (word 0)
            (fun candidate => mixedCartesianDerivative order (Fin.tail word)
              function candidate) point := by
      have localEquality :
          evaluationListDerivative (List.ofFn (Fin.tail word)) function =ᶠ[𝓝 point]
            (fun candidate => mixedCartesianDerivative order (Fin.tail word)
              function candidate) :=
        Filter.eventually_of_mem (openUnitCylinder_isOpen.mem_nhds membership)
          (inductionHypothesis (Fin.tail word))
      exact congrArg
        (fun derivative : SpatialCell →L[ℝ] ComplexEuclidean dimension =>
          derivative (spatialCellBasis (word 0))) localEquality.fderiv_eq
    refine congruence.trans ?_
    change fderiv ℝ
        (fun candidate => iteratedFDeriv ℝ order function candidate
          (fun position => spatialCellBasis (Fin.tail word position))) point
          (spatialCellBasis (word 0)) = _
    have derivativeDifferentiable :=
      (smooth.contDiffAt
        (openUnitCylinder_isOpen.mem_nhds membership)).differentiableAt_iteratedFDeriv
          (ENat.natCast_lt_of_coe_top_le_withTop le_rfl order)
    exact (derivativeDifferentiable.iteratedFDeriv_succ_apply_left'
      (m := fun position => spatialCellBasis (word position))).symm

theorem mixedCartesianDerivative_reconstruction_eq_evaluationIndex
    {dimension order : ℕ} (coefficients : OrdinaryCoefficientCore dimension)
    (word : MixedCartesianWord order) (point : SpatialCell)
    (membership : point ∈ openUnitCylinder) :
    mixedCartesianDerivative order word
        (diskCellLift (ordinaryReconstructedValue coefficients)) point =
      evaluationIndexSeries coefficients
        (evaluationDerivativeIndexOfList (List.ofFn word)) point := by
  have withinEquality := iteratedFDerivWithin_congr (𝕜 := ℝ)
    (diskCellLift_ordinaryReconstructedValue_eq_series coefficients)
      membership order
  rw [iteratedFDerivWithin_of_isOpen order openUnitCylinder_isOpen membership,
    iteratedFDerivWithin_of_isOpen order openUnitCylinder_isOpen membership]
      at withinEquality
  have actualToSeries :
      mixedCartesianDerivative order word
          (diskCellLift (ordinaryReconstructedValue coefficients)) point =
        mixedCartesianDerivative order word
          (evaluationIndexSeries coefficients evaluationDerivativeIndexZero) point :=
    congrArg (fun derivative =>
      derivative (fun position => spatialCellBasis (word position)))
        withinEquality
  have listToMixed := evaluationListDerivative_ofFn word
    (evaluationIndexSeries coefficients evaluationDerivativeIndexZero)
    (ordinaryAmbientDerivativeSeries_contDiffOn coefficients
      emptyCartesianWord 0) membership
  have listToIndex := evaluationListDerivative_indexSeries coefficients
    (List.ofFn word) evaluationDerivativeIndexZero membership
  exact actualToSeries.trans (listToMixed.symm.trans listToIndex)

/-- The derivative extension used by the quantitative proof. -/
def evaluationMixedDerivativeExtension
    {dimension order : ℕ} (coefficients : OrdinaryCoefficientCore dimension)
    (word : MixedCartesianWord order) :
    C(DiskCellDomain, ComplexEuclidean dimension) :=
  let index := evaluationDerivativeIndexOfList (List.ofFn word)
  ordinaryDerivativeExtension coefficients index.planarWord index.cellOrder

theorem evaluationMixedDerivativeExtension_spec
    {dimension order : ℕ} (coefficients : OrdinaryCoefficientCore dimension)
    (word : MixedCartesianWord order) :
    IsMixedCartesianExtension (ordinaryReconstructedValue coefficients)
      order word (evaluationMixedDerivativeExtension coefficients word) := by
  intro point membership
  let index := evaluationDerivativeIndexOfList (List.ofFn word)
  have lifted := diskCellLift_ordinaryDerivativeExtension coefficients
    index.planarWord index.cellOrder point membership
  change diskCellLift
      (ordinaryDerivativeExtension coefficients index.planarWord index.cellOrder)
        point = evaluationIndexSeries coefficients index point at lifted
  rw [diskCellLift, dif_pos
    (openCylinderMembershipClosed point membership)] at lifted
  exact lifted.trans
    (mixedCartesianDerivative_reconstruction_eq_evaluationIndex coefficients
      word point membership).symm

theorem evaluationMixedDerivativeExtension_eq_closed
    {dimension order : ℕ} (coefficients : OrdinaryCoefficientCore dimension)
    (word : MixedCartesianWord order) :
    evaluationMixedDerivativeExtension coefficients word =
      closedMixedDerivative (ordinaryReconstructedClosedJet coefficients)
        order word := by
  exact mixedCartesianExtension_unique
    (ordinaryReconstructedClosedJet coefficients) order word
      (evaluationMixedDerivativeExtension coefficients word)
      (evaluationMixedDerivativeExtension_spec coefficients word)

/-- Every arbitrary physical coordinate word of total order at most `j` is
bounded by the literal original `A^(j+3)` norm. -/
theorem originalGrade_mixedCoordinateDerivative_bound
    {dimension order j : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters dimension (j + 3))
    (word : MixedCartesianWord order) (orderLe : order ≤ j) :
    ‖closedMixedDerivative (weightedSmoothEquiv parameters field.toCore)
        order word‖ ≤
      m15EvaluationConstant * ‖field‖ := by
  let coefficients := weightedCoefficientCoreEquiv parameters field.toCore
  let index := evaluationDerivativeIndexOfList (List.ofFn word)
  have totalIdentity : index.planarOrder + index.cellOrder = order := by
    change
      (evaluationDerivativeIndexOfList (List.ofFn word)
          evaluationDerivativeIndexZero).planarOrder +
        (evaluationDerivativeIndexOfList (List.ofFn word)
          evaluationDerivativeIndexZero).cellOrder = order
    rw [evaluationDerivativeIndexOfList_total]
    simp [evaluationDerivativeIndexZero]
  have totalLe : index.planarOrder + index.cellOrder ≤ j :=
    totalIdentity.trans_le orderLe
  change ‖closedMixedDerivative
      (ordinaryReconstructedClosedJet coefficients) order word‖ ≤ _
  rw [← evaluationMixedDerivativeExtension_eq_closed coefficients word]
  change ‖ordinaryDerivativeExtension coefficients index.planarWord
    index.cellOrder‖ ≤ _
  exact originalGrade_coordinateDerivative_bound parameters field
    index.planarWord index.cellOrder totalLe

end Grad.CartesianState
