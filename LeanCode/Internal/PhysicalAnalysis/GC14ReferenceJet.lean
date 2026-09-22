import GC14StateDerivativeCoefficients

noncomputable section

set_option maxHeartbeats 800000

open Set
open scoped ContDiff Topology

namespace Grad.GaugeCoefficients.Physical.Frame

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Envelope

def globalClosedValue {dimension : ℕ} (function : SpatialPlane → ComplexEuclidean dimension)
    (smooth : ContDiff ℝ ∞ function) : C(ClosedDisk, ComplexEuclidean dimension) where
  toFun point := function point.val
  continuous_toFun := smooth.continuous.comp continuous_subtype_val

theorem closedDiskLift_globalClosedValue_eventually {dimension : ℕ}
    (function : SpatialPlane → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ function)
    (point : SpatialPlane) (inside : point ∈ openUnitDisk) :
    closedDiskLift (globalClosedValue function smooth) =ᶠ[𝓝 point] function := by
  filter_upwards [openUnitDisk_isOpen.mem_nhds inside] with candidate candidateInside
  unfold closedDiskLift
  rw [dif_pos (openDiskMembershipClosed candidate candidateInside)]
  rfl

def globalClosedDerivative {dimension : ℕ} (function : SpatialPlane → ComplexEuclidean dimension)
    (smooth : ContDiff ℝ ∞ function) (order : ℕ) (word : CartesianWord order) :
    C(ClosedDisk, ComplexEuclidean dimension) where
  toFun point := cartesianDerivative order word function point.val
  continuous_toFun := by
    let evaluate : (SpatialPlane [×order]→L[ℝ] ComplexEuclidean dimension) →L[ℝ]
        ComplexEuclidean dimension :=
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin order => SpatialPlane)
        (ComplexEuclidean dimension) (fun position => spatialBasis (word position))
    have derivativeContinuous : Continuous (iteratedFDeriv ℝ order function) := by
      apply continuous_iff_continuousAt.2
      intro point
      exact (smooth.contDiffAt.iteratedFDeriv_right
        (m := ∞) (i := order) (by norm_cast)).continuousAt
    exact (evaluate.continuous.comp derivativeContinuous).comp continuous_subtype_val

theorem globalClosedDerivative_spec {dimension : ℕ}
    (function : SpatialPlane → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ function)
    (order : ℕ) (word : CartesianWord order) :
    IsCartesianExtension (globalClosedValue function smooth) order word
      (globalClosedDerivative function smooth order word) := by
  intro point inside
  have equality := ((closedDiskLift_globalClosedValue_eventually function smooth
    point.val inside).iteratedFDeriv ℝ order).self_of_nhds
  change iteratedFDeriv ℝ order function point.val _ = iteratedFDeriv ℝ order
    (closedDiskLift (globalClosedValue function smooth)) point.val _
  rw [equality]

def globalClosedJet {dimension : ℕ} (function : SpatialPlane → ComplexEuclidean dimension)
    (smooth : ContDiff ℝ ∞ function) : ClosedJet dimension where
  value := globalClosedValue function smooth
  smoothInterior := by
    intro point inside
    exact (smooth.contDiffAt.congr_of_eventuallyEq
      (closedDiskLift_globalClosedValue_eventually function smooth point inside)).contDiffWithinAt
  derivativeExists order word := ⟨globalClosedDerivative function smooth order word,
    globalClosedDerivative_spec function smooth order word⟩

theorem globalClosedJet_derivative {dimension : ℕ}
    (function : SpatialPlane → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ function)
    (order : ℕ) (word : CartesianWord order) (point : ClosedDisk) :
    closedDerivative (globalClosedJet function smooth) order word point =
      cartesianDerivative order word function point.val := by
  have equality := cartesianExtension_unique (globalClosedJet function smooth) order word
    (globalClosedDerivative function smooth order word) (globalClosedDerivative_spec function smooth order word)
  exact (congrArg (fun derivative : C(ClosedDisk, ComplexEuclidean dimension) => derivative point) equality).symm

def referenceStateLinear : SpatialPlane →L[ℝ] ComplexEuclidean 3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun point => WithLp.toLp 2 ![(point 0 : ℂ), 0, (point 1 : ℂ)]
      map_add' := by
        intro first second
        apply PiLp.ext
        intro coordinate
        fin_cases coordinate <;> simp
      map_smul' := by
        intro scalar point
        apply PiLp.ext
        intro coordinate
        fin_cases coordinate <;> simp }

def referenceStateJet : ClosedJet 3 := globalClosedJet referenceStateLinear referenceStateLinear.contDiff

@[simp] theorem referenceStateJet_value (point : ClosedDisk) :
    referenceStateJet.value point = referenceStateValue point := rfl
theorem referenceStateLinear_iteratedFDeriv_zero (rank : ℕ) (high : 2 ≤ rank)
    (point : SpatialPlane) : iteratedFDeriv ℝ rank referenceStateLinear point = 0 := by
  rcases rank with _ | rank
  · omega
  rcases rank with _ | rank
  · omega
  apply ContinuousMultilinearMap.ext
  intro directions
  rw [iteratedFDeriv_succ_apply_right]
  simp only [referenceStateLinear.fderiv, iteratedFDeriv_succ_const]
  rfl

theorem referenceStateJet_cartesianDerivative (index : CartesianMultiIndex) (point : ClosedDisk) :
    closedMultiDerivative referenceStateJet index point = referenceStateMultiDerivative 0 index point := by
  rw [closedMultiDerivative]
  unfold referenceStateJet
  rw [globalClosedJet_derivative]
  by_cases zeroIndex : index = (0, 0)
  · subst index
    rfl
  by_cases firstIndex : index = (1, 0)
  · subst index
    change cartesianDerivative 1 (cartesianMultiIndexWord (1, 0)) referenceStateLinear point.val = _
    unfold cartesianDerivative
    rw [iteratedFDeriv_one_apply, referenceStateLinear.fderiv]
    rfl
  by_cases secondIndex : index = (0, 1)
  · subst index
    change cartesianDerivative 1 (cartesianMultiIndexWord (0, 1)) referenceStateLinear point.val = _
    unfold cartesianDerivative
    rw [iteratedFDeriv_one_apply, referenceStateLinear.fderiv]
    rfl
  have high : 2 ≤ cartesianOrder index := by
    rcases index with ⟨first, second⟩
    simp only [Prod.mk.injEq] at zeroIndex firstIndex secondIndex
    change 2 ≤ first + second
    omega
  unfold cartesianDerivative
  rw [referenceStateLinear_iteratedFDeriv_zero _ high]
  simp [referenceStateMultiDerivative, zeroIndex, firstIndex, secondIndex]

end Grad.GaugeCoefficients.Physical.Frame
