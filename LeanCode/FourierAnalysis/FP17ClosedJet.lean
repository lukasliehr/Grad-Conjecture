import FP17SmoothReconstruction

noncomputable section

set_option maxHeartbeats 500000

open Filter Set
open scoped ContDiff Topology

namespace Grad.CartesianState

open Grad.ClosedJets
open Grad.RepresentedKernel.SpatialProduct

private structure OrdinaryDerivativeIndex where
  planarOrder : ℕ
  planarWord : CartesianWord planarOrder
  cellOrder : ℕ

private def ordinaryDerivativeIndexZero : OrdinaryDerivativeIndex where
  planarOrder := 0
  planarWord := emptyCartesianWord
  cellOrder := 0

private def ordinaryDerivativeIndexPrepend (coordinate : Fin 3)
    (index : OrdinaryDerivativeIndex) : OrdinaryDerivativeIndex :=
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

private def ordinaryDerivativeIndexOfList (directions : List (Fin 3))
    (index : OrdinaryDerivativeIndex := ordinaryDerivativeIndexZero) :
    OrdinaryDerivativeIndex :=
  directions.foldr ordinaryDerivativeIndexPrepend index

private def ordinaryIndexSeries {dimension : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension)
    (index : OrdinaryDerivativeIndex) :
    SpatialCell → ComplexEuclidean dimension :=
  ordinaryAmbientDerivativeSeries coefficients index.planarWord index.cellOrder

private def ordinaryIndexExtension {dimension : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension)
    (index : OrdinaryDerivativeIndex) :
    C(DiskCellDomain, ComplexEuclidean dimension) :=
  ordinaryDerivativeExtension coefficients index.planarWord index.cellOrder

private theorem ordinaryIndexSeries_fderiv_basis
    {dimension : ℕ} (coefficients : OrdinaryCoefficientCore dimension)
    (index : OrdinaryDerivativeIndex) (coordinate : Fin 3)
    (point : SpatialCell) (membership : point ∈ openUnitCylinder) :
    fderiv ℝ (ordinaryIndexSeries coefficients index) point
        (spatialCellBasis coordinate) =
      ordinaryIndexSeries coefficients
        (ordinaryDerivativeIndexPrepend coordinate index) point := by
  fin_cases coordinate
  · simpa [ordinaryIndexSeries, ordinaryDerivativeIndexPrepend,
      fp17PlanarCoordinate] using
        (ordinaryAmbientDerivativeSeries_fderiv_planarBasis coefficients
          index.planarWord index.cellOrder point membership (0 : Fin 2))
  · simpa [ordinaryIndexSeries, ordinaryDerivativeIndexPrepend,
      fp17PlanarCoordinate] using
        (ordinaryAmbientDerivativeSeries_fderiv_planarBasis coefficients
          index.planarWord index.cellOrder point membership (1 : Fin 2))
  · simpa [ordinaryIndexSeries, ordinaryDerivativeIndexPrepend] using
        (ordinaryAmbientDerivativeSeries_fderiv_cellBasis coefficients
          index.planarWord index.cellOrder point membership)

private def mixedDirectionDerivative {dimension : ℕ} (coordinate : Fin 3)
    (function : SpatialCell → ComplexEuclidean dimension) :
    SpatialCell → ComplexEuclidean dimension :=
  fun point => fderiv ℝ function point (spatialCellBasis coordinate)

private def mixedListDerivative {dimension : ℕ} (directions : List (Fin 3))
    (function : SpatialCell → ComplexEuclidean dimension) :
    SpatialCell → ComplexEuclidean dimension :=
  directions.foldr mixedDirectionDerivative function

private theorem mixedListDerivative_indexSeries
    {dimension : ℕ} (coefficients : OrdinaryCoefficientCore dimension)
    (directions : List (Fin 3)) (index : OrdinaryDerivativeIndex) :
    Set.EqOn
      (mixedListDerivative directions (ordinaryIndexSeries coefficients index))
      (ordinaryIndexSeries coefficients
        (ordinaryDerivativeIndexOfList directions index))
      openUnitCylinder := by
  induction directions with
  | nil =>
      intro point membership
      rfl
  | cons coordinate rest inductionHypothesis =>
      intro point membership
      have localEquality :
          mixedListDerivative rest (ordinaryIndexSeries coefficients index) =ᶠ[𝓝 point]
            ordinaryIndexSeries coefficients
              (ordinaryDerivativeIndexOfList rest index) :=
        Filter.eventually_of_mem (openUnitCylinder_isOpen.mem_nhds membership)
          inductionHypothesis
      change fderiv ℝ
          (mixedListDerivative rest (ordinaryIndexSeries coefficients index)) point
            (spatialCellBasis coordinate) = _
      rw [localEquality.fderiv_eq]
      exact ordinaryIndexSeries_fderiv_basis coefficients
        (ordinaryDerivativeIndexOfList rest index) coordinate point membership

private theorem mixedListDerivative_ofFn
    {dimension order : ℕ} (word : MixedCartesianWord order)
    (function : SpatialCell → ComplexEuclidean dimension)
    (smooth : ContDiffOn ℝ ∞ function openUnitCylinder) :
    Set.EqOn (mixedListDerivative (List.ofFn word) function)
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
          mixedDirectionDerivative (word 0)
              (mixedListDerivative (List.ofFn (Fin.tail word)) function) point =
            mixedDirectionDerivative (word 0)
              (fun candidate => mixedCartesianDerivative order (Fin.tail word)
                function candidate) point := by
        have localEquality :
            mixedListDerivative (List.ofFn (Fin.tail word)) function =ᶠ[𝓝 point]
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

/-- On the actual open cylinder, the lift of the uniformly reconstructed
continuous field is the zero-index ambient Fourier series. -/
theorem diskCellLift_ordinaryReconstructedValue_eq_series
    {dimension : ℕ} (coefficients : OrdinaryCoefficientCore dimension) :
    Set.EqOn (diskCellLift (ordinaryReconstructedValue coefficients))
      (ordinaryIndexSeries coefficients ordinaryDerivativeIndexZero)
      openUnitCylinder := by
  intro point membership
  have extensionIdentity := diskCellLift_ordinaryDerivativeExtension
    coefficients emptyCartesianWord 0 point membership
  rw [ordinaryDerivativeExtension_zero_zero] at extensionIdentity
  simpa [ordinaryIndexSeries, ordinaryDerivativeIndexZero,
    ordinaryAmbientDerivativeSeries] using
    extensionIdentity

/-- The actual lifted reconstruction is smooth, not merely its separate
formal derivative series. -/
theorem diskCellLift_ordinaryReconstructedValue_contDiffOn
    {dimension : ℕ} (coefficients : OrdinaryCoefficientCore dimension) :
    ContDiffOn ℝ ∞ (diskCellLift (ordinaryReconstructedValue coefficients))
      openUnitCylinder := by
  have seriesSmooth := ordinaryAmbientDerivativeSeries_contDiffOn coefficients
    emptyCartesianWord 0
  exact seriesSmooth.congr
    (diskCellLift_ordinaryReconstructedValue_eq_series coefficients)

/-- Every actual mixed Cartesian derivative of the lifted reconstruction is
the indexed planar-word/cell-order Fourier series obtained by processing the
literal requested word. -/
theorem mixedCartesianDerivative_ordinaryReconstructedValue
    {dimension order : ℕ} (coefficients : OrdinaryCoefficientCore dimension)
    (word : MixedCartesianWord order) (point : SpatialCell)
    (membership : point ∈ openUnitCylinder) :
    mixedCartesianDerivative order word
        (diskCellLift (ordinaryReconstructedValue coefficients)) point =
      ordinaryIndexSeries coefficients
        (ordinaryDerivativeIndexOfList (List.ofFn word)) point := by
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
          (ordinaryIndexSeries coefficients ordinaryDerivativeIndexZero) point :=
    congrArg (fun derivative =>
      derivative (fun position => spatialCellBasis (word position)))
        withinEquality
  have listToMixed := mixedListDerivative_ofFn word
    (ordinaryIndexSeries coefficients ordinaryDerivativeIndexZero)
    (ordinaryAmbientDerivativeSeries_contDiffOn coefficients
      emptyCartesianWord 0) membership
  have listToIndex := mixedListDerivative_indexSeries coefficients
    (List.ofFn word) ordinaryDerivativeIndexZero membership
  exact actualToSeries.trans (listToMixed.symm.trans listToIndex)

private theorem ordinaryIndexExtension_apply_open
    {dimension : ℕ} (coefficients : OrdinaryCoefficientCore dimension)
    (index : OrdinaryDerivativeIndex) (point : SpatialCell)
    (membership : point ∈ openUnitCylinder) :
    ordinaryIndexExtension coefficients index
        (diskCellPoint point
          (openCylinderMembershipClosed point membership)) =
      ordinaryIndexSeries coefficients index point := by
  have lifted := diskCellLift_ordinaryDerivativeExtension coefficients
    index.planarWord index.cellOrder point membership
  change diskCellLift (ordinaryIndexExtension coefficients index) point =
    ordinaryIndexSeries coefficients index point at lifted
  rw [diskCellLift, dif_pos
    (openCylinderMembershipClosed point membership)] at lifted
  exact lifted

/-- The exact continuous extension selected for an arbitrary requested mixed
word. -/
def ordinaryMixedDerivativeExtension
    {dimension order : ℕ} (coefficients : OrdinaryCoefficientCore dimension)
    (word : MixedCartesianWord order) :
    C(DiskCellDomain, ComplexEuclidean dimension) :=
  ordinaryIndexExtension coefficients
    (ordinaryDerivativeIndexOfList (List.ofFn word))

theorem ordinaryMixedDerivativeExtension_spec
    {dimension order : ℕ} (coefficients : OrdinaryCoefficientCore dimension)
    (word : MixedCartesianWord order) :
    IsMixedCartesianExtension (ordinaryReconstructedValue coefficients)
      order word (ordinaryMixedDerivativeExtension coefficients word) := by
  intro point membership
  rw [ordinaryMixedDerivativeExtension,
    ordinaryIndexExtension_apply_open coefficients _ point membership]
  exact (mixedCartesianDerivative_ordinaryReconstructedValue coefficients word
    point membership).symm

/-- The uniformly reconstructed value together with all its exact mixed
derivative extensions, packaged as the actual ordinary smooth closed-jet
space used downstream. -/
def ordinaryReconstructedClosedJet {dimension : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension) :
    DiskCellClosedJet dimension where
  value := ordinaryReconstructedValue coefficients
  smoothInterior :=
    diskCellLift_ordinaryReconstructedValue_contDiffOn coefficients
  derivativeExists := fun _order word =>
    ⟨ordinaryMixedDerivativeExtension coefficients word,
      ordinaryMixedDerivativeExtension_spec coefficients word⟩

@[simp] theorem ordinaryReconstructedClosedJet_value
    {dimension : ℕ} (coefficients : OrdinaryCoefficientCore dimension) :
    (ordinaryReconstructedClosedJet coefficients).value =
      ordinaryReconstructedValue coefficients := rfl

end Grad.CartesianState
