import AXF28CartesianEquivalence

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.FlatSourceProjection

open Grad.CartesianState Grad.Constraints Grad.QuotientProjection
open Grad.AxisSplit Grad.AxisJet Grad.AxisCore Grad.RealFixedRanges Grad.ChartAxisProjections

variable {parameters : PhaseParameters}

def vectorFlatProjection (field : ACore parameters 2) : ACore parameters 2 :=
  let v := field - radialSourceCore parameters field
  let v0 := v - fixedValueCorrection v
  v0 - (1 / 2 : ℂ) • curlInsertion (cartesianCurlTrace v0)

/-- BS6 for arbitrary actual Cartesian vector/scalar inputs, not a model. -/
theorem cartesianFlatProjection_literal (source : CartesianSourceCore parameters) :
    cartesianFlatProjection source =
      (vectorFlatProjection source.1,
        source.2.1 - angularCore parameters 0 source.2.1,
        source.2.2 - angularCore parameters 0 source.2.2 -
          (radialFirstInsertion 0 (traceFirst 0 (source.2.2 - angularCore parameters 0 source.2.2)) +
            radialFirstInsertion 1 (traceFirst 1 (source.2.2 - angularCore parameters 0 source.2.2)))) := by
  apply Prod.ext
  · change cartesianSourceVector (flatSourceProjection (cartesianToSpin source)) = _
    rw [cartesianSourceVector_flatSourceProjection]
    simp only [cartesianValueReduced, cartesianSourceVector_cartesianToSpin, vectorFlatProjection]
  · apply Prod.ext
    · exact flatSourceProjection_third (cartesianToSpin source)
    · exact flatSourceProjection_fourth (cartesianToSpin source)

def CartesianCoreIsFlat (source : CartesianSourceCore parameters) : Prop :=
  radialSourceCore parameters source.1 = 0 ∧ traceZero source.1 = 0 ∧
    cartesianCurlTrace source.1 = 0 ∧ angularCore parameters 0 source.2.1 = 0 ∧
    angularCore parameters 0 source.2.2 = 0 ∧
    ∀ direction, traceFirst direction source.2.2 = 0

theorem cartesianCoreIsFlat_iff (source : CartesianSourceCore parameters) :
    CartesianCoreIsFlat source ↔ IsFlat (cartesianToSpin source) := by
  rw [isFlat_iff_cartesian]
  unfold CartesianIsFlat
  rw [cartesianSourceVector_cartesianToSpin]
  rfl

theorem cartesianFlatProjection_fixes (source : CartesianSourceCore parameters)
    (flat : CartesianCoreIsFlat source) : cartesianFlatProjection source = source := by
  change spinCartesianEquiv (flatSourceProjection (cartesianToSpin source)) = source
  rw [flatSourceProjection_fixes _ ((cartesianCoreIsFlat_iff source).mp flat)]
  exact spinCartesianEquiv.apply_symm_apply source

theorem cartesianFlatProjection_flat (source : CartesianSourceCore parameters) :
    CartesianCoreIsFlat (cartesianFlatProjection source) := by
  rw [cartesianCoreIsFlat_iff]
  change IsFlat (spinCartesianEquiv.symm
    (spinCartesianEquiv (flatSourceProjection (cartesianToSpin source))))
  rw [LinearEquiv.symm_apply_apply]
  exact flatSourceProjection_flat _

theorem cartesianFlatProjection_range (source : CartesianSourceCore parameters) :
    source ∈ LinearMap.range (cartesianFlatProjection (parameters := parameters)) ↔
      CartesianCoreIsFlat source := by
  constructor
  · rintro ⟨other, rfl⟩
    exact cartesianFlatProjection_flat other
  · intro flat
    exact ⟨source, cartesianFlatProjection_fixes source flat⟩

theorem flatSmoothEmbedding_cartesian_norm (parameters : PhaseParameters)
    (cellLength : ℝ) (positive : 0 < cellLength) (grade : ℕ) (large : 3 ≤ grade)
    (source : LinearMap.ker (realExtraction parameters cellLength)) :
    ‖flatSmoothEmbedding parameters cellLength positive grade large source‖ =
      cartesianSourceNorm grade (spinCartesianEquiv source.val.val) := by
  rw [spinCartesianEquiv_norm]
  exact flatSmoothEmbedding_original_norm parameters cellLength positive grade large source

theorem originalRealFlatCore_cartesian (parameters : PhaseParameters)
    (cellLength : ℝ) (positive : 0 < cellLength)
    (source : LinearMap.ker (realExtraction parameters cellLength)) :
    CartesianCoreIsFlat (spinCartesianEquiv source.val.val) := by
  rw [cartesianCoreIsFlat_iff]
  change IsFlat (spinCartesianEquiv.symm (spinCartesianEquiv source.val.val))
  rw [LinearEquiv.symm_apply_apply]
  exact (source_isFlat_iff_kernel cellLength positive source.val).mpr source.property

end Grad.FlatSourceProjection
