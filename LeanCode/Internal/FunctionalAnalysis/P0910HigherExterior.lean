import P0910HigherCollar

noncomputable section

open Filter Set
open scoped BigOperators ContDiff Topology

namespace Grad.DiskExtension.Operator

open Grad.ClosedJets
open Grad.DiskExtension.Seeley

local instance p0910HigherExteriorClosedDiskCompactSpace : CompactSpace ClosedDisk := by
  rw [← isCompact_iff_compactSpace, closedUnitDisk_eq_closedBall]
  exact isCompact_closedBall (0 : SpatialPlane) 1

theorem iteratedFDeriv_reflectedSpatialCell (order index : ℕ)
    (point : SpatialCell) (nonzero : planarPart point ≠ 0) :
    iteratedFDeriv ℝ order (reflectedSpatialCell index) point =
      (1 + node index) • iteratedFDeriv ℝ order normalizedSpatialCell point -
        node index • iteratedFDeriv ℝ order id point := by
  have nonzeroNeighborhood : ∀ᶠ candidate in 𝓝 point,
      planarPart candidate ≠ 0 :=
    continuous_planarPart.continuousAt.eventually
      (isOpen_compl_singleton.mem_nhds nonzero)
  have localEquality : collarInterpolation (-node index) =ᶠ[𝓝 point]
      reflectedSpatialCell index := by
    filter_upwards [nonzeroNeighborhood] with candidate candidateNonzero
    exact collarInterpolation_neg_node index candidate candidateNonzero
  rw [← (localEquality.iteratedFDeriv ℝ order).eq_of_nhds,
    iteratedFDeriv_collarInterpolation order (-node index) point nonzero]
  module

noncomputable def reflectionJetBound (order : ℕ) (point : SpatialCell) : ℝ :=
  2 * (‖iteratedFDeriv ℝ order normalizedSpatialCell point‖ + 1) +
    (‖iteratedFDeriv ℝ order (id : SpatialCell → SpatialCell) point‖ + 1)

theorem reflectionJetBound_nonnegative (order : ℕ) (point : SpatialCell) :
    0 ≤ reflectionJetBound order point := by
  unfold reflectionJetBound
  positivity

theorem eventually_reflectedSpatialCell_iteratedFDeriv_norm_le_boundary
    (order : ℕ) (point : SpatialCell) (boundary : ‖planarPart point‖ = 1) :
    ∀ᶠ candidate in 𝓝 point, ∀ index,
      ‖iteratedFDeriv ℝ order (reflectedSpatialCell index) candidate‖ ≤
        reflectionJetBound order point * node index := by
  have nonzero : planarPart point ≠ 0 := by
    intro equality
    rw [equality, norm_zero] at boundary
    norm_num at boundary
  have normalizedContinuous :=
    (normalizedSpatialCell_contDiffAt point nonzero).continuousAt_iteratedFDeriv
      (show (order : WithTop ℕ∞) ≤ ∞ by
        exact WithTop.coe_le_coe.mpr
          (show (order : ℕ∞) ≤ ⊤ from le_top))
  have normalizedBound : ∀ᶠ candidate in 𝓝 point,
      ‖iteratedFDeriv ℝ order normalizedSpatialCell candidate‖ <
        ‖iteratedFDeriv ℝ order normalizedSpatialCell point‖ + 1 :=
    normalizedContinuous.norm.eventually
      (Iio_mem_nhds (lt_add_one _))
  have nonzeroNeighborhood : ∀ᶠ candidate in 𝓝 point,
      planarPart candidate ≠ 0 :=
    continuous_planarPart.continuousAt.eventually
      (isOpen_compl_singleton.mem_nhds nonzero)
  have identityContinuous : ContinuousAt (fun candidate : SpatialCell =>
      iteratedFDeriv ℝ order (id : SpatialCell → SpatialCell) candidate) point :=
    (contDiff_id.continuous_iteratedFDeriv'
      (𝕜 := ℝ) (m := order)).continuousAt
  have identityBound : ∀ᶠ candidate in 𝓝 point,
      ‖iteratedFDeriv ℝ order (id : SpatialCell → SpatialCell) candidate‖ <
        ‖iteratedFDeriv ℝ order id point‖ + 1 :=
    identityContinuous.norm.eventually (Iio_mem_nhds (lt_add_one _))
  filter_upwards [normalizedBound, identityBound, nonzeroNeighborhood] with candidate
    candidateBound candidateIdentityBound candidateNonzero index
  rw [iteratedFDeriv_reflectedSpatialCell order index candidate candidateNonzero]
  have nodeOne : 1 ≤ node index := node_one_le index
  calc
    ‖(1 + node index) • iteratedFDeriv ℝ order normalizedSpatialCell candidate -
        node index • iteratedFDeriv ℝ order id candidate‖ ≤
        ‖(1 + node index) • iteratedFDeriv ℝ order normalizedSpatialCell candidate‖ +
          ‖node index • iteratedFDeriv ℝ order id candidate‖ := norm_sub_le _ _
    _ = (1 + node index) *
          ‖iteratedFDeriv ℝ order normalizedSpatialCell candidate‖ +
        node index * ‖iteratedFDeriv ℝ order id candidate‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos (by positivity : 0 < 1 + node index),
            abs_of_pos (node_positive index)]
    _ ≤ (2 * (‖iteratedFDeriv ℝ order normalizedSpatialCell point‖ + 1) +
          (‖iteratedFDeriv ℝ order id point‖ + 1)) * node index := by
      nlinarith [norm_nonneg
          (iteratedFDeriv ℝ order normalizedSpatialCell candidate),
        norm_nonneg
          (iteratedFDeriv ℝ order (id : SpatialCell → SpatialCell) candidate),
        norm_nonneg
          (iteratedFDeriv ℝ order (id : SpatialCell → SpatialCell) point)]
    _ = reflectionJetBound order point * node index := rfl

noncomputable def closedHigherDerivativeBound {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (order : ℕ) : ℝ :=
  ∑ word : MixedCartesianWord order,
    ‖spatialCellWordCoefficient word‖ *
      ‖closedMixedDerivative field order word‖

theorem closedHigherDerivativeBound_nonnegative {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (order : ℕ) :
    0 ≤ closedHigherDerivativeBound field order := by
  unfold closedHigherDerivativeBound
  positivity

theorem closedHigherDerivative_norm_le_bound {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (order : ℕ) (point : SpatialCell) :
    ‖closedHigherDerivative (order := order) field point‖ ≤
      closedHigherDerivativeBound field order := by
  rw [closedHigherDerivative, closedHigherDerivativeBound]
  calc
    ‖∑ word : MixedCartesianWord order,
        (spatialCellWordCoefficient word).smulRight
          (closedMixedDerivative field order word (retractedDiskCell point))‖ ≤
      ∑ word : MixedCartesianWord order,
        ‖(spatialCellWordCoefficient word).smulRight
          (closedMixedDerivative field order word (retractedDiskCell point))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ word : MixedCartesianWord order,
        ‖spatialCellWordCoefficient word‖ *
          ‖closedMixedDerivative field order word‖ := by
      apply Finset.sum_le_sum
      intro word _
      rw [ContinuousMultilinearMap.norm_smulRight]
      exact mul_le_mul_of_nonneg_left
        ((closedMixedDerivative field order word).norm_coe_le_norm _)
        (norm_nonneg _)

noncomputable def reflectedCompositeTaylorSeries {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : ℕ) (point : SpatialCell) :
    FormalMultilinearSeries ℝ SpatialCell (ComplexEuclidean dimension) :=
  (closedTaylorSeries field (reflectedSpatialCell index point)).taylorComp
    (ftaylorSeries ℝ (reflectedSpatialCell index) point)

noncomputable def reflectedCompositeJetBound {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) : ℝ :=
  ∑ partition : OrderedFinpartition order,
    closedHigherDerivativeBound field partition.length *
      ∏ position : Fin partition.length,
        reflectionJetBound (partition.partSize position) point

theorem reflectedCompositeJetBound_nonnegative {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) :
    0 ≤ reflectedCompositeJetBound field order point := by
  unfold reflectedCompositeJetBound
  apply Finset.sum_nonneg
  intro partition _
  exact mul_nonneg (closedHigherDerivativeBound_nonnegative field _)
    (Finset.prod_nonneg fun position _ =>
      reflectionJetBound_nonnegative (partition.partSize position) point)

theorem eventually_reflectedCompositeTaylorSeries_norm_le_boundary
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) (boundary : ‖planarPart point‖ = 1) :
    ∀ᶠ candidate in 𝓝 point, ∀ index,
      ‖reflectedCompositeTaylorSeries field index candidate order‖ ≤
        reflectedCompositeJetBound field order point * node index ^ order := by
  let Position := Σ partition : OrderedFinpartition order, Fin partition.length
  have allReflectionBounds : ∀ᶠ candidate in 𝓝 point,
      ∀ slot : Position, ∀ index,
        ‖iteratedFDeriv ℝ (slot.1.partSize slot.2)
          (reflectedSpatialCell index) candidate‖ ≤
          reflectionJetBound (slot.1.partSize slot.2) point * node index := by
    rw [Filter.eventually_all]
    intro slot
    exact eventually_reflectedSpatialCell_iteratedFDeriv_norm_le_boundary
      (slot.1.partSize slot.2) point boundary
  filter_upwards [allReflectionBounds] with candidate reflectionBounds index
  rw [reflectedCompositeTaylorSeries, FormalMultilinearSeries.taylorComp]
  calc
    ‖∑ partition : OrderedFinpartition order,
        (closedTaylorSeries field (reflectedSpatialCell index candidate)).compAlongOrderedFinpartition
            (ftaylorSeries ℝ (reflectedSpatialCell index) candidate) partition‖ ≤
      ∑ partition : OrderedFinpartition order,
        ‖(closedTaylorSeries field (reflectedSpatialCell index candidate)).compAlongOrderedFinpartition
            (ftaylorSeries ℝ (reflectedSpatialCell index) candidate) partition‖ :=
      norm_sum_le _ _
    _ ≤ ∑ partition : OrderedFinpartition order,
        (closedHigherDerivativeBound field partition.length *
          ∏ position : Fin partition.length,
            reflectionJetBound (partition.partSize position) point) *
          node index ^ order := by
      apply Finset.sum_le_sum
      intro partition _
      calc
        ‖(closedTaylorSeries field (reflectedSpatialCell index candidate)).compAlongOrderedFinpartition
              (ftaylorSeries ℝ (reflectedSpatialCell index) candidate) partition‖ ≤
          ‖closedTaylorSeries field (reflectedSpatialCell index candidate)
              partition.length‖ *
            ∏ position : Fin partition.length,
              ‖ftaylorSeries ℝ (reflectedSpatialCell index) candidate
                (partition.partSize position)‖ :=
          partition.norm_compAlongOrderedFinpartition_le _ _
        _ ≤ closedHigherDerivativeBound field partition.length *
            ∏ position : Fin partition.length,
              (reflectionJetBound (partition.partSize position) point *
                node index) := by
          apply mul_le_mul
          · exact closedHigherDerivative_norm_le_bound field partition.length _
          · apply Finset.prod_le_prod
            · intro position _
              positivity
            · intro position _
              exact reflectionBounds ⟨partition, position⟩ index
          · positivity
          · exact closedHigherDerivativeBound_nonnegative field partition.length
        _ = (closedHigherDerivativeBound field partition.length *
              ∏ position : Fin partition.length,
                reflectionJetBound (partition.partSize position) point) *
            node index ^ partition.length := by
          rw [Finset.prod_mul_distrib]
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          ring
        _ ≤ (closedHigherDerivativeBound field partition.length *
              ∏ position : Fin partition.length,
                reflectionJetBound (partition.partSize position) point) *
            node index ^ order := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (node_one_le index)
              (OrderedFinpartition.length_le partition))
            (mul_nonneg (closedHigherDerivativeBound_nonnegative field _)
              (Finset.prod_nonneg fun position _ =>
                reflectionJetBound_nonnegative
                  (partition.partSize position) point))
    _ = reflectedCompositeJetBound field order point * node index ^ order := by
      rw [reflectedCompositeJetBound, Finset.sum_mul]

def radialOffset (point : SpatialCell) : ℝ :=
  ‖planarPart point‖ - 1

def exteriorCutoffScale (index : ℕ) (point : SpatialCell) : ℝ :=
  node index • radialOffset point

theorem radialOffset_contDiffAt (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) :
    ContDiffAt ℝ ∞ radialOffset point :=
  (contDiffAt_norm_planarPart point nonzero).sub contDiffAt_const

theorem exteriorCutoffScale_contDiffOn_planarNonzeroRegion (index : ℕ) :
    ContDiffOn ℝ ∞ (exteriorCutoffScale index) planarNonzeroRegion := by
  intro point nonzero
  exact ((radialOffset_contDiffAt point nonzero).const_smul
    (node index)).contDiffWithinAt

noncomputable def radialJetEnvelope (order : ℕ) (point : SpatialCell) : ℝ :=
  1 + ∑ position : Fin order,
    (‖iteratedFDeriv ℝ (position.val + 1) radialOffset point‖ + 1)

theorem radialJetEnvelope_one_le (order : ℕ) (point : SpatialCell) :
    1 ≤ radialJetEnvelope order point := by
  unfold radialJetEnvelope
  have sumNonnegative : 0 ≤ ∑ position : Fin order,
      (‖iteratedFDeriv ℝ (position.val + 1) radialOffset point‖ + 1) := by
    positivity
  linarith

theorem radialJet_le_envelope {order derivativeOrder : ℕ}
    (point : SpatialCell) (positive : 1 ≤ derivativeOrder)
    (upper : derivativeOrder ≤ order) :
    ‖iteratedFDeriv ℝ derivativeOrder radialOffset point‖ + 1 ≤
      radialJetEnvelope order point := by
  let position : Fin order :=
    ⟨derivativeOrder - 1, by omega⟩
  have positionMembership : position ∈ (Finset.univ : Finset (Fin order)) :=
    Finset.mem_univ position
  have termBound :
      ‖iteratedFDeriv ℝ (position.val + 1) radialOffset point‖ + 1 ≤
        ∑ other : Fin order,
          (‖iteratedFDeriv ℝ (other.val + 1) radialOffset point‖ + 1) :=
    Finset.single_le_sum
      (s := Finset.univ)
      (f := fun other : Fin order =>
        ‖iteratedFDeriv ℝ (other.val + 1) radialOffset point‖ + 1)
      (fun other _ => by positivity) positionMembership
  have orderEquality : position.val + 1 = derivativeOrder := by
    dsimp only [position]
    omega
  rw [orderEquality] at termBound
  unfold radialJetEnvelope
  linarith

theorem eventually_radialOffset_jets_le_envelope_boundary
    (order : ℕ) (point : SpatialCell) (boundary : ‖planarPart point‖ = 1) :
    ∀ᶠ candidate in 𝓝 point, ∀ position : Fin order,
      ‖iteratedFDeriv ℝ (position.val + 1) radialOffset candidate‖ ≤
        radialJetEnvelope order point := by
  have nonzero : planarPart point ≠ 0 := by
    intro equality
    rw [equality, norm_zero] at boundary
    norm_num at boundary
  rw [Filter.eventually_all]
  intro position
  have derivativeContinuous :=
    (radialOffset_contDiffAt point nonzero).continuousAt_iteratedFDeriv
      (show (position.val + 1 : WithTop ℕ∞) ≤ ∞ by
        exact WithTop.coe_le_coe.mpr
          (show (position.val + 1 : ℕ∞) ≤ ⊤ from le_top))
  filter_upwards [derivativeContinuous.norm.eventually
    (Iio_mem_nhds (lt_add_one
      ‖iteratedFDeriv ℝ (position.val + 1) radialOffset point‖))] with
    candidate candidateBound
  exact (le_of_lt candidateBound).trans
    (radialJet_le_envelope point (by omega)
      (Nat.succ_le_of_lt position.isLt))

noncomputable def plateauJetEnvelope (order : ℕ) : ℝ :=
  ∑ derivativeOrder ∈ Finset.range (order + 1),
    Classical.choose (plateauCutoff_iteratedDeriv_bound derivativeOrder)

theorem plateauJetEnvelope_nonnegative (order : ℕ) :
    0 ≤ plateauJetEnvelope order := by
  unfold plateauJetEnvelope
  apply Finset.sum_nonneg
  intro derivativeOrder membership
  exact (Classical.choose_spec
    (plateauCutoff_iteratedDeriv_bound derivativeOrder)).1

theorem plateauCutoff_iteratedFDeriv_norm_le_envelope
    (order derivativeOrder : ℕ) (upper : derivativeOrder ≤ order) (scale : ℝ) :
    ‖iteratedFDeriv ℝ derivativeOrder plateauCutoff scale‖ ≤
      plateauJetEnvelope order := by
  have derivativeBound :=
    (Classical.choose_spec
      (plateauCutoff_iteratedDeriv_bound derivativeOrder)).2 scale
  have chosenNonnegative :=
    (Classical.choose_spec
      (plateauCutoff_iteratedDeriv_bound derivativeOrder)).1
  have chosenLe : Classical.choose
      (plateauCutoff_iteratedDeriv_bound derivativeOrder) ≤
      plateauJetEnvelope order := by
    unfold plateauJetEnvelope
    exact Finset.single_le_sum
      (fun index membership =>
        (Classical.choose_spec
          (plateauCutoff_iteratedDeriv_bound index)).1)
      (Finset.mem_range.mpr (by omega))
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact derivativeBound.trans chosenLe

noncomputable def cutoffCompositeJetBound (order : ℕ)
    (point : SpatialCell) : ℝ :=
  order.factorial * plateauJetEnvelope order *
    radialJetEnvelope order point ^ order

theorem cutoffCompositeJetBound_nonnegative (order : ℕ)
    (point : SpatialCell) : 0 ≤ cutoffCompositeJetBound order point := by
  unfold cutoffCompositeJetBound
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (plateauJetEnvelope_nonnegative order))
    (pow_nonneg (zero_le_one.trans (radialJetEnvelope_one_le order point)) _)

theorem eventually_cutoffComposite_iteratedFDeriv_norm_le_boundary
    (order : ℕ) (point : SpatialCell) (boundary : ‖planarPart point‖ = 1) :
    ∀ᶠ candidate in 𝓝 point, ∀ index,
      ‖iteratedFDeriv ℝ order
        (plateauCutoff ∘ exteriorCutoffScale index) candidate‖ ≤
        cutoffCompositeJetBound order point * node index ^ order := by
  have nonzero : planarPart point ≠ 0 := by
    intro equality
    rw [equality, norm_zero] at boundary
    norm_num at boundary
  have nonzeroNeighborhood : ∀ᶠ candidate in 𝓝 point,
      candidate ∈ planarNonzeroRegion :=
    continuous_planarPart.continuousAt.eventually
      (isOpen_compl_singleton.mem_nhds nonzero)
  filter_upwards [eventually_radialOffset_jets_le_envelope_boundary
    order point boundary, nonzeroNeighborhood] with candidate radialBounds
      candidateNonzero index
  have outerBounds : ∀ derivativeOrder, derivativeOrder ≤ order →
      ‖iteratedFDerivWithin ℝ derivativeOrder plateauCutoff Set.univ
        (exteriorCutoffScale index candidate)‖ ≤ plateauJetEnvelope order := by
    intro derivativeOrder upper
    rw [iteratedFDerivWithin_univ]
    exact plateauCutoff_iteratedFDeriv_norm_le_envelope
      order derivativeOrder upper _
  have innerBounds : ∀ derivativeOrder, 1 ≤ derivativeOrder →
      derivativeOrder ≤ order →
      ‖iteratedFDerivWithin ℝ derivativeOrder (exteriorCutoffScale index)
        planarNonzeroRegion candidate‖ ≤
        (radialJetEnvelope order point * node index) ^ derivativeOrder := by
    intro derivativeOrder positive upper
    rw [iteratedFDerivWithin_of_isOpen derivativeOrder
      planarNonzeroRegion_isOpen candidateNonzero]
    change ‖iteratedFDeriv ℝ derivativeOrder
      (fun point => node index • radialOffset point) candidate‖ ≤ _
    have radialSmooth : ContDiffAt ℝ derivativeOrder radialOffset candidate :=
      (radialOffset_contDiffAt candidate candidateNonzero).of_le
        (WithTop.coe_le_coe.mpr
          (show (derivativeOrder : ℕ∞) ≤ ⊤ from le_top))
    rw [iteratedFDeriv_const_smul_apply' radialSmooth, norm_smul,
      Real.norm_eq_abs, abs_of_pos (node_positive index)]
    have derivativeBound :
        ‖iteratedFDeriv ℝ derivativeOrder radialOffset candidate‖ ≤
          radialJetEnvelope order point := by
      let position : Fin order := ⟨derivativeOrder - 1, by omega⟩
      have positionBound := radialBounds position
      have equality : position.val + 1 = derivativeOrder := by
        dsimp only [position]
        omega
      rw [← equality]
      exact positionBound
    have baseOne : 1 ≤ radialJetEnvelope order point * node index := by
      simpa only [one_mul] using
        mul_le_mul (radialJetEnvelope_one_le order point)
          (node_one_le index) zero_le_one
          (zero_le_one.trans (radialJetEnvelope_one_le order point))
    calc
      node index * ‖iteratedFDeriv ℝ derivativeOrder radialOffset candidate‖ ≤
          node index * radialJetEnvelope order point :=
        mul_le_mul_of_nonneg_left derivativeBound (node_positive index).le
      _ = radialJetEnvelope order point * node index := mul_comm _ _
      _ ≤ (radialJetEnvelope order point * node index) ^ derivativeOrder := by
        simpa only [pow_one] using
          pow_le_pow_right₀ baseOne positive
  have compositionBound := norm_iteratedFDerivWithin_comp_le
    (𝕜 := ℝ) (n := order) (N := ∞)
    (s := planarNonzeroRegion) (t := Set.univ)
    plateauCutoff_smooth.contDiffOn
    (exteriorCutoffScale_contDiffOn_planarNonzeroRegion index)
    (show (order : WithTop ℕ∞) ≤ ∞ by
      exact WithTop.coe_le_coe.mpr
        (show (order : ℕ∞) ≤ ⊤ from le_top))
    uniqueDiffOn_univ planarNonzeroRegion_isOpen.uniqueDiffOn
    (mapsTo_univ _ _) candidateNonzero
    (C := plateauJetEnvelope order)
    (D := radialJetEnvelope order point * node index)
    outerBounds innerBounds
  have withinEquality := iteratedFDerivWithin_of_isOpen
    (𝕜 := ℝ) (f := plateauCutoff ∘ exteriorCutoffScale index)
    order planarNonzeroRegion_isOpen candidateNonzero
  have ambientCompositionBound :
      ‖iteratedFDeriv ℝ order
        (plateauCutoff ∘ exteriorCutoffScale index) candidate‖ ≤
        order.factorial * plateauJetEnvelope order *
          (radialJetEnvelope order point * node index) ^ order := by
    rw [← withinEquality]
    exact compositionBound
  calc
    ‖iteratedFDeriv ℝ order
        (plateauCutoff ∘ exteriorCutoffScale index) candidate‖ ≤
      order.factorial * plateauJetEnvelope order *
        (radialJetEnvelope order point * node index) ^ order :=
      ambientCompositionBound
    _ = cutoffCompositeJetBound order point * node index ^ order := by
      rw [mul_pow]
      unfold cutoffCompositeJetBound
      ring

noncomputable def exteriorScalarJetBound (order : ℕ)
    (point : SpatialCell) : ℝ :=
  ‖Complex.ofRealCLM‖ * cutoffCompositeJetBound order point

theorem exteriorScalarJetBound_nonnegative (order : ℕ)
    (point : SpatialCell) : 0 ≤ exteriorScalarJetBound order point := by
  unfold exteriorScalarJetBound
  exact mul_nonneg (norm_nonneg _)
    (cutoffCompositeJetBound_nonnegative order point)

theorem eventually_exteriorScalar_iteratedFDeriv_norm_le_boundary
    (order : ℕ) (point : SpatialCell) (boundary : ‖planarPart point‖ = 1) :
    ∀ᶠ candidate in 𝓝 point, ∀ index,
      ‖iteratedFDeriv ℝ order (exteriorScalar index) candidate‖ ≤
        exteriorScalarJetBound order point *
          (|coefficient index| * node index ^ order) := by
  have nonzero : planarPart point ≠ 0 := by
    intro equality
    rw [equality, norm_zero] at boundary
    norm_num at boundary
  have nonzeroNeighborhood : ∀ᶠ candidate in 𝓝 point,
      candidate ∈ planarNonzeroRegion :=
    continuous_planarPart.continuousAt.eventually
      (isOpen_compl_singleton.mem_nhds nonzero)
  filter_upwards [eventually_cutoffComposite_iteratedFDeriv_norm_le_boundary
    order point boundary, nonzeroNeighborhood] with candidate cutoffBound
      candidateNonzero index
  have scaleSmooth : ContDiffAt ℝ ∞ (exteriorCutoffScale index) candidate :=
    ((radialOffset_contDiffAt candidate candidateNonzero).const_smul
      (node index))
  have cutoffSmooth : ContDiffAt ℝ ∞
      (plateauCutoff ∘ exteriorCutoffScale index) candidate :=
    plateauCutoff_smooth.contDiffAt.comp candidate scaleSmooth
  have realSmooth : ContDiffAt ℝ ∞
      (fun candidate => coefficient index •
        (plateauCutoff ∘ exteriorCutoffScale index) candidate) candidate :=
    cutoffSmooth.const_smul (coefficient index)
  have functionEquality : exteriorScalar index =
      Complex.ofRealCLM ∘ (fun candidate => coefficient index •
        (plateauCutoff ∘ exteriorCutoffScale index) candidate) := by
    funext other
    simp [exteriorScalar, exteriorCutoffScale, radialOffset,
      Function.comp_apply]
  rw [functionEquality]
  have linearBound := Complex.ofRealCLM.norm_iteratedFDeriv_comp_left
    realSmooth
    (show (order : WithTop ℕ∞) ≤ ∞ by
      exact WithTop.coe_le_coe.mpr
        (show (order : ℕ∞) ≤ ⊤ from le_top))
  calc
    ‖iteratedFDeriv ℝ order
        (Complex.ofRealCLM ∘ fun candidate => coefficient index •
          (plateauCutoff ∘ exteriorCutoffScale index) candidate) candidate‖ ≤
      ‖Complex.ofRealCLM‖ *
        ‖iteratedFDeriv ℝ order (fun candidate => coefficient index •
          (plateauCutoff ∘ exteriorCutoffScale index) candidate) candidate‖ :=
      linearBound
    _ = ‖Complex.ofRealCLM‖ *
        (|coefficient index| *
          ‖iteratedFDeriv ℝ order
            (plateauCutoff ∘ exteriorCutoffScale index) candidate‖) := by
      rw [iteratedFDeriv_const_smul_apply'
        (cutoffSmooth.of_le
          (WithTop.coe_le_coe.mpr
            (show (order : ℕ∞) ≤ ⊤ from le_top))), norm_smul,
        Real.norm_eq_abs]
    _ ≤ ‖Complex.ofRealCLM‖ *
        (|coefficient index| *
          (cutoffCompositeJetBound order point * node index ^ order)) := by
      gcongr
      exact cutoffBound index
    _ = exteriorScalarJetBound order point *
        (|coefficient index| * node index ^ order) := by
      unfold exteriorScalarJetBound
      ring

def openExteriorActiveRegion (index : ℕ) : Set SpatialCell :=
  {point | 1 < ‖planarPart point‖ ∧
    node index * (‖planarPart point‖ - 1) < 1}

theorem openExteriorActiveRegion_isOpen (index : ℕ) :
    IsOpen (openExteriorActiveRegion index) := by
  exact (isOpen_lt continuous_const
      (continuous_norm.comp continuous_planarPart)).inter
    (isOpen_lt
      (((continuous_norm.comp continuous_planarPart).sub
        continuous_const).const_mul (node index)) continuous_const)

theorem openExteriorActiveRegion_subset_closedExteriorActiveRegion (index : ℕ) :
    openExteriorActiveRegion index ⊆ closedExteriorActiveRegion index := by
  intro point membership
  exact ⟨membership.1.le, membership.2.le⟩

theorem reflectedCompositeTaylorSeries_eq_iteratedFDeriv_of_mem_openActive
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (index order : ℕ)
    (point : SpatialCell) (membership : point ∈ openExteriorActiveRegion index) :
    reflectedCompositeTaylorSeries field index point order =
      iteratedFDeriv ℝ order
        (diskCellLift field.value ∘ reflectedSpatialCell index) point := by
  have restrictedTaylor :=
    (diskCellLift_comp_reflectedSpatialCell_hasFTaylorSeriesUpToOn_active
      field index).mono
      (openExteriorActiveRegion_subset_closedExteriorActiveRegion index)
  have coefficientEquality :=
    restrictedTaylor.eq_iteratedFDerivWithin_of_uniqueDiffOn
      (m := order)
      (WithTop.coe_le_coe.mpr
        (show (order : ℕ∞) ≤ ⊤ from le_top))
      (openExteriorActiveRegion_isOpen index).uniqueDiffOn membership
  rw [iteratedFDerivWithin_of_isOpen order
    (openExteriorActiveRegion_isOpen index) membership] at coefficientEquality
  simpa only [reflectedCompositeTaylorSeries] using coefficientEquality

noncomputable def exteriorSummandJetBound {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) : ℝ :=
  ∑ derivativeOrder ∈ Finset.range (order + 1),
    (order.choose derivativeOrder : ℝ) *
      exteriorScalarJetBound derivativeOrder point *
      reflectedCompositeJetBound field (order - derivativeOrder) point

theorem exteriorSummandJetBound_nonnegative {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) :
    0 ≤ exteriorSummandJetBound field order point := by
  unfold exteriorSummandJetBound
  apply Finset.sum_nonneg
  intro derivativeOrder _
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _)
      (exteriorScalarJetBound_nonnegative derivativeOrder point))
    (reflectedCompositeJetBound_nonnegative field _ point)

theorem eventually_exteriorSummand_iteratedFDeriv_norm_le_boundary
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) (boundary : ‖planarPart point‖ = 1) :
    ∀ᶠ candidate in 𝓝 point, ∀ index,
      1 < ‖planarPart candidate‖ →
      ‖iteratedFDeriv ℝ order (exteriorSummandCellLift field index) candidate‖ ≤
        exteriorSummandJetBound field order point *
          (|coefficient index| * node index ^ order) := by
  have scalarBounds : ∀ᶠ candidate in 𝓝 point,
      ∀ position : Fin (order + 1), ∀ index,
        ‖iteratedFDeriv ℝ position.val (exteriorScalar index) candidate‖ ≤
          exteriorScalarJetBound position.val point *
            (|coefficient index| * node index ^ position.val) := by
    rw [Filter.eventually_all]
    intro position
    exact eventually_exteriorScalar_iteratedFDeriv_norm_le_boundary
      position.val point boundary
  have compositeBounds : ∀ᶠ candidate in 𝓝 point,
      ∀ position : Fin (order + 1), ∀ index,
        ‖reflectedCompositeTaylorSeries field index candidate
          (order - position.val)‖ ≤
          reflectedCompositeJetBound field (order - position.val) point *
            node index ^ (order - position.val) := by
    rw [Filter.eventually_all]
    intro position
    exact eventually_reflectedCompositeTaylorSeries_norm_le_boundary
      field (order - position.val) point boundary
  have nonzero : planarPart point ≠ 0 := by
    intro equality
    rw [equality, norm_zero] at boundary
    norm_num at boundary
  have nonzeroNeighborhood : ∀ᶠ candidate in 𝓝 point,
      candidate ∈ planarNonzeroRegion :=
    continuous_planarPart.continuousAt.eventually
      (isOpen_compl_singleton.mem_nhds nonzero)
  filter_upwards [scalarBounds, compositeBounds, nonzeroNeighborhood] with
    candidate candidateScalarBounds candidateCompositeBounds candidateNonzero
      index outside
  by_cases active : node index * (‖planarPart candidate‖ - 1) < 1
  · have activeMembership : candidate ∈ openExteriorActiveRegion index :=
      ⟨outside, active⟩
    have scalarSmooth : ContDiffOn ℝ ∞ (exteriorScalar index)
        (openExteriorActiveRegion index) := by
      intro other otherMembership
      exact (exteriorScalar_contDiffAt index other
        (closedExteriorActiveRegion_planarPart_ne_zero index
          ⟨otherMembership.1.le, otherMembership.2.le⟩)).contDiffWithinAt
    have compositeSmooth : ContDiffOn ℝ ∞
        (diskCellLift field.value ∘ reflectedSpatialCell index)
        (openExteriorActiveRegion index) :=
      ((diskCellLift_comp_reflectedSpatialCell_hasFTaylorSeriesUpToOn_active
        field index).contDiffOn).mono
          (openExteriorActiveRegion_subset_closedExteriorActiveRegion index)
    have productBound := norm_iteratedFDerivWithin_smul_le
      (𝕜 := ℝ) (N := ∞) (n := order)
      scalarSmooth compositeSmooth
      (openExteriorActiveRegion_isOpen index).uniqueDiffOn activeMembership
      (show (order : WithTop ℕ∞) ≤ ∞ by
        exact WithTop.coe_le_coe.mpr
          (show (order : ℕ∞) ≤ ⊤ from le_top))
    have withinProductEquality := iteratedFDerivWithin_of_isOpen
      (𝕜 := ℝ)
      (f := fun candidate => exteriorScalar index candidate •
        (diskCellLift field.value ∘ reflectedSpatialCell index) candidate)
      order (openExteriorActiveRegion_isOpen index) activeMembership
    rw [withinProductEquality] at productBound
    have scalarWithinEquality (derivativeOrder : ℕ) :=
      iteratedFDerivWithin_of_isOpen
        (𝕜 := ℝ) (f := exteriorScalar index) derivativeOrder
        (openExteriorActiveRegion_isOpen index) activeMembership
    have compositeWithinEquality (derivativeOrder : ℕ) :=
      iteratedFDerivWithin_of_isOpen
        (𝕜 := ℝ)
        (f := diskCellLift field.value ∘ reflectedSpatialCell index)
        derivativeOrder (openExteriorActiveRegion_isOpen index) activeMembership
    simp_rw [scalarWithinEquality, compositeWithinEquality] at productBound
    rw [show exteriorSummandCellLift field index = fun candidate =>
        exteriorScalar index candidate •
          (diskCellLift field.value ∘ reflectedSpatialCell index) candidate by
      funext other
      exact exteriorSummandCellLift_formula field index other]
    calc
      ‖iteratedFDeriv ℝ order (fun candidate => exteriorScalar index candidate •
          (diskCellLift field.value ∘ reflectedSpatialCell index) candidate) candidate‖ ≤
        ∑ derivativeOrder ∈ Finset.range (order + 1),
          (order.choose derivativeOrder : ℝ) *
            ‖iteratedFDeriv ℝ derivativeOrder (exteriorScalar index) candidate‖ *
            ‖iteratedFDeriv ℝ (order - derivativeOrder)
              (diskCellLift field.value ∘ reflectedSpatialCell index) candidate‖ :=
        productBound
      _ ≤ ∑ derivativeOrder ∈ Finset.range (order + 1),
          ((order.choose derivativeOrder : ℝ) *
            exteriorScalarJetBound derivativeOrder point *
            reflectedCompositeJetBound field (order - derivativeOrder) point) *
          (|coefficient index| * node index ^ order) := by
        apply Finset.sum_le_sum
        intro derivativeOrder membership
        have upper : derivativeOrder ≤ order := by
          exact Nat.le_of_lt_succ (Finset.mem_range.mp membership)
        let position : Fin (order + 1) := ⟨derivativeOrder, by omega⟩
        have scalarBound := candidateScalarBounds position index
        have compositeBound := candidateCompositeBounds position index
        rw [reflectedCompositeTaylorSeries_eq_iteratedFDeriv_of_mem_openActive
          field index (order - derivativeOrder) candidate activeMembership]
          at compositeBound
        calc
          (order.choose derivativeOrder : ℝ) *
              ‖iteratedFDeriv ℝ derivativeOrder (exteriorScalar index) candidate‖ *
              ‖iteratedFDeriv ℝ (order - derivativeOrder)
                (diskCellLift field.value ∘ reflectedSpatialCell index) candidate‖ ≤
            (order.choose derivativeOrder : ℝ) *
              (exteriorScalarJetBound derivativeOrder point *
                (|coefficient index| * node index ^ derivativeOrder)) *
              (reflectedCompositeJetBound field (order - derivativeOrder) point *
                node index ^ (order - derivativeOrder)) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left scalarBound (Nat.cast_nonneg _)
            · exact compositeBound
            · exact norm_nonneg _
            · exact mul_nonneg (Nat.cast_nonneg _)
                (mul_nonneg
                  (exteriorScalarJetBound_nonnegative derivativeOrder point)
                  (mul_nonneg (abs_nonneg _)
                    (pow_nonneg (node_positive index).le _)))
          _ = ((order.choose derivativeOrder : ℝ) *
                exteriorScalarJetBound derivativeOrder point *
                reflectedCompositeJetBound field (order - derivativeOrder) point) *
              (|coefficient index| * node index ^ order) := by
            have powerEquality : node index ^ derivativeOrder *
                node index ^ (order - derivativeOrder) = node index ^ order := by
              rw [← pow_add, Nat.add_sub_of_le upper]
            rw [← powerEquality]
            ring
      _ = exteriorSummandJetBound field order point *
          (|coefficient index| * node index ^ order) := by
        rw [exteriorSummandJetBound, Finset.sum_mul]
  · have scaleAbove : cutoffSupportWidth <
        node index * (‖planarPart candidate‖ - 1) := by
      have oneLe : 1 ≤ node index * (‖planarPart candidate‖ - 1) :=
        le_of_not_gt active
      norm_num [cutoffSupportWidth, collarWidth] at oneLe ⊢
      linarith
    have scaleContinuous : ContinuousAt (fun other : SpatialCell =>
        node index * (‖planarPart other‖ - 1)) candidate :=
      ((continuous_norm.comp continuous_planarPart).continuousAt.sub
        continuousAt_const).const_mul _
    have eventuallyInactive : ∀ᶠ other in 𝓝 candidate,
        cutoffSupportWidth ≤ node index * (‖planarPart other‖ - 1) :=
      (scaleContinuous.eventually (Ioi_mem_nhds scaleAbove)).mono
        fun _ inequality => inequality.le
    have summandZero : exteriorSummandCellLift field index =ᶠ[𝓝 candidate]
        fun _ => (0 : ComplexEuclidean dimension) := by
      filter_upwards [eventuallyInactive] with other inactive
      simp [exteriorSummandCellLift_formula, plateauCutoff_zero _ inactive]
    have derivativeZero :=
      (summandZero.iteratedFDeriv ℝ order).eq_of_nhds
    rw [derivativeZero]
    have constantDerivativeZero :
        iteratedFDeriv ℝ order
          (fun _ : SpatialCell => (0 : ComplexEuclidean dimension)) candidate = 0 := by
      rcases eq_or_ne order 0 with rfl | positive
      · rfl
      · rw [iteratedFDeriv_const_of_ne positive
          (0 : ComplexEuclidean dimension)]
        simp
    rw [constantDerivativeZero, norm_zero]
    exact mul_nonneg (exteriorSummandJetBound_nonnegative field order point)
      (mul_nonneg (abs_nonneg _) (pow_nonneg (node_positive index).le _))

theorem exteriorSummandJetMajorant_summable
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) :
    Summable (fun index => exteriorSummandJetBound field order point *
      (|coefficient index| * node index ^ order)) := by
  exact (coefficient_absolute_moment_summable order).mul_left
    (exteriorSummandJetBound field order point)

theorem exteriorScalar_contDiffOn_planarNonzeroRegion (index : ℕ) :
    ContDiffOn ℝ ∞ (exteriorScalar index) planarNonzeroRegion := by
  intro point nonzero
  exact (exteriorScalar_contDiffAt index point nonzero).contDiffWithinAt

theorem exteriorScalar_hasFTaylorSeriesUpToOn_planarNonzeroRegion (index : ℕ) :
    HasFTaylorSeriesUpToOn (𝕜 := ℝ) ∞ (exteriorScalar index)
      (ftaylorSeries ℝ (exteriorScalar index)) planarNonzeroRegion := by
  have withinTaylor :=
    (exteriorScalar_contDiffOn_planarNonzeroRegion index).ftaylorSeriesWithin
      planarNonzeroRegion_isOpen.uniqueDiffOn
  apply withinTaylor.congr_series
  intro order _ point membership
  exact iteratedFDerivWithin_of_isOpen order planarNonzeroRegion_isOpen
    membership

theorem exteriorScalar_hasFTaylorSeriesUpToOn_active (index : ℕ) :
    HasFTaylorSeriesUpToOn (𝕜 := ℝ) ∞ (exteriorScalar index)
      (ftaylorSeries ℝ (exteriorScalar index))
      (closedExteriorActiveRegion index) :=
  (exteriorScalar_hasFTaylorSeriesUpToOn_planarNonzeroRegion index).mono
    (closedExteriorActiveRegion_subset_planarNonzeroRegion index)

def complexScalarProduct {dimension : ℕ}
    (pair : ℂ × ComplexEuclidean dimension) : ComplexEuclidean dimension :=
  pair.1 • pair.2

theorem complexScalarProduct_contDiff {dimension : ℕ} :
    ContDiff ℝ ∞ (complexScalarProduct (dimension := dimension)) := by
  fun_prop

noncomputable def exteriorSummandInputTaylorSeries {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : ℕ) (point : SpatialCell) :
    FormalMultilinearSeries ℝ SpatialCell
      (ℂ × ComplexEuclidean dimension) :=
  fun order =>
    (ftaylorSeries ℝ (exteriorScalar index) point order).prod
      (reflectedCompositeTaylorSeries field index point order)

noncomputable def exteriorSummandTaylorSeries {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : ℕ) (point : SpatialCell) :
    FormalMultilinearSeries ℝ SpatialCell (ComplexEuclidean dimension) :=
  (ftaylorSeries ℝ (complexScalarProduct (dimension := dimension))
      (exteriorScalar index point,
        diskCellLift field.value (reflectedSpatialCell index point))).taylorComp
    (exteriorSummandInputTaylorSeries field index point)

theorem exteriorSummandCellLift_hasFTaylorSeriesUpToOn_active
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (index : ℕ) :
    HasFTaylorSeriesUpToOn (𝕜 := ℝ) ∞
      (exteriorSummandCellLift field index)
      (exteriorSummandTaylorSeries field index)
      (closedExteriorActiveRegion index) := by
  have inputTaylor :=
    (exteriorScalar_hasFTaylorSeriesUpToOn_active index).prodMk
      (diskCellLift_comp_reflectedSpatialCell_hasFTaylorSeriesUpToOn_active
        field index)
  have actionTaylor : HasFTaylorSeriesUpToOn (𝕜 := ℝ) ∞
      (complexScalarProduct (dimension := dimension))
      (ftaylorSeries ℝ (complexScalarProduct (dimension := dimension)))
      Set.univ :=
    ((complexScalarProduct_contDiff (dimension := dimension)).ftaylorSeries).hasFTaylorSeriesUpToOn
      Set.univ
  have composed := actionTaylor.comp inputTaylor (mapsTo_univ _ _)
  apply composed.congr
  intro point _
  rw [exteriorSummandCellLift_formula]
  rfl

end Grad.DiskExtension.Operator
