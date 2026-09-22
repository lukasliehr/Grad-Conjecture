import FP17CoefficientCore
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

noncomputable section

open Set MeasureTheory Metric
open scoped BigOperators ENNReal Interval Topology

namespace Grad.CartesianState

open Grad.ClosedJets

/-- The averaging disk of radius `1/4` used in the direct proof of the disk
supremum estimate. -/
def diskAverageSet : Set SpatialPlane := closedBall 0 (1 / 4 : ℝ)

theorem diskAverageSet_subset_openUnitDisk : diskAverageSet ⊆ openUnitDisk := by
  intro point membership
  rw [diskAverageSet, mem_closedBall, dist_zero_right] at membership
  change ‖point‖ < 1
  linarith

theorem measurableSet_diskAverageSet : MeasurableSet diskAverageSet :=
  measurableSet_closedBall

theorem volume_diskAverageSet : volume diskAverageSet = ENNReal.ofReal (Real.pi / 16) := by
  rw [diskAverageSet, EuclideanSpace.volume_closedBall_fin_two]
  rw [← ENNReal.ofReal_pow (by positivity : 0 ≤ (1 / 4 : ℝ))]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (1 / 4 : ℝ) ^ 2)]
  congr 1
  ring

theorem volumeReal_diskAverageSet : volume.real diskAverageSet = Real.pi / 16 := by
  rw [Measure.real_def, volume_diskAverageSet, ENNReal.toReal_ofReal]
  positivity

/-- Exactly the six unordered Cartesian multi-indices of order at most two. -/
def diskSupMultiIndex (slot : Fin 6) : CartesianMultiIndex :=
  match slot.1 with
  | 0 => (0, 0)
  | 1 => (1, 0)
  | 2 => (0, 1)
  | 3 => (2, 0)
  | 4 => (1, 1)
  | _ => (0, 2)

theorem diskSupMultiIndex_order_le_two (slot : Fin 6) :
    cartesianOrder (diskSupMultiIndex slot) ≤ 2 := by
  fin_cases slot <;> norm_num [diskSupMultiIndex, cartesianOrder]

/-- The literal six-term derivative energy from the paper's estimate M4. -/
def diskSupEnergy {dimension : ℕ} (field : ClosedJet dimension) : ℝ :=
  ∑ slot : Fin 6, ‖closedDerivativeL2 (diskSupMultiIndex slot) field‖ ^ 2

theorem diskSupEnergy_nonneg {dimension : ℕ} (field : ClosedJet dimension) :
    0 ≤ diskSupEnergy field := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The exact numerical constant in the direct averaged-Taylor disk estimate. -/
def diskSupConstant : ℝ := 16 * Real.sqrt 6 / Real.sqrt Real.pi

theorem diskSupConstant_pos : 0 < diskSupConstant := by
  unfold diskSupConstant
  positivity

theorem sqrt_pi_div_sixteen :
    Real.sqrt (Real.pi / 16) = Real.sqrt Real.pi / 4 := by
  rw [Real.sqrt_div (Real.pi_nonneg)]
  rw [show Real.sqrt (16 : ℝ) = 4 by
    exact (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2 (by norm_num)]

theorem spatialPlane_decompose (point : SpatialPlane) :
    point = point 0 • spatialBasis 0 + point 1 • spatialBasis 1 := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [spatialBasis]

theorem spatialCoordinate_abs_le_norm (point : SpatialPlane) (coordinate : Fin 2) :
    |point coordinate| ≤ ‖point‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le point coordinate

theorem diskDifference_norm_le_five_fourths
    {point base : SpatialPlane} (pointMembership : point ∈ closedUnitDisk)
    (baseMembership : base ∈ diskAverageSet) :
    ‖point - base‖ ≤ 5 / 4 := by
  have pointBound : ‖point‖ ≤ 1 := pointMembership
  have baseBound : ‖base‖ ≤ 1 / 4 := by
    simpa [diskAverageSet, dist_zero_right] using baseMembership
  calc
    ‖point - base‖ ≤ ‖point‖ + ‖base‖ := norm_sub_le point base
    _ ≤ 5 / 4 := by linarith

theorem openDisk_segment {point base : SpatialPlane}
    (pointMembership : point ∈ openUnitDisk)
    (baseMembership : base ∈ openUnitDisk) {t : ℝ} (tMembership : t ∈ Icc 0 1) :
    base + t • (point - base) ∈ openUnitDisk := by
  rcases tMembership with ⟨tNonnegative, tAtMostOne⟩
  have oneMinusNonnegative : 0 ≤ 1 - t := by linarith
  change ‖point‖ < 1 at pointMembership
  change ‖base‖ < 1 at baseMembership
  have identity : base + t • (point - base) =
      (1 - t) • base + t • point := by module
  rw [openUnitDisk, identity]
  calc
    ‖(1 - t) • base + t • point‖ ≤
        ‖(1 - t) • base‖ + ‖t • point‖ := norm_add_le _ _
    _ = (1 - t) * ‖base‖ + t * ‖point‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg oneMinusNonnegative, abs_of_nonneg tNonnegative]
    _ < (1 - t) * 1 + t * 1 := by
      by_cases endpoint : t = 1
      · subst t
        simpa using pointMembership
      · have oneMinusPositive : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne tAtMostOne endpoint)
        have strictBase : (1 - t) * ‖base‖ < (1 - t) * 1 :=
          mul_lt_mul_of_pos_left baseMembership oneMinusPositive
        have weakPoint : t * ‖point‖ ≤ t * 1 :=
          mul_le_mul_of_nonneg_left pointMembership.le tNonnegative
        linarith
    _ = 1 := by ring

/-- Second-order Taylor's formula along the segment joining two interior disk
points.  This is the analytic identity averaged in the proof of A08. -/
theorem closedJet_secondOrderTaylor {dimension : ℕ}
    (field : ClosedJet dimension) {point base : SpatialPlane}
    (pointMembership : point ∈ openUnitDisk)
    (baseMembership : base ∈ openUnitDisk) :
    closedDiskLift field.value point =
      ∑ k ∈ Finset.range 2, (Nat.factorial k : ℝ)⁻¹ •
        iteratedFDeriv ℝ k (closedDiskLift field.value) base
          (fun _ ↦ point - base) +
      (1 : ℝ) • ∫ t in 0..1, (1 - t) •
        iteratedFDeriv ℝ 2 (closedDiskLift field.value)
          (base + t • (point - base)) (fun _ ↦ point - base) := by
  have smoothAlong : ∀ (t : ℝ) (membership : t ∈ Icc 0 1),
      ContDiffAt ℝ 2 (closedDiskLift field.value)
        (base + t • (point - base)) := by
    intro t membership
    have inside := openDisk_segment pointMembership baseMembership membership
    exact ((field.smoothInterior _ inside).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
      (openUnitDisk_isOpen.mem_nhds inside)
  have taylor := map_add_eq_sum_add_integral_iteratedFDeriv
    (n := 1) smoothAlong
  simpa [Nat.factorial] using taylor

theorem closedMultiDerivative_eq_iteratedFDeriv {dimension : ℕ}
    (field : ClosedJet dimension) {point : SpatialPlane}
    (membership : point ∈ openUnitDisk) (index : CartesianMultiIndex) :
    closedMultiDerivative field index
        ⟨point, openDiskMembershipClosed point membership⟩ =
      iteratedFDeriv ℝ (cartesianOrder index) (closedDiskLift field.value) point
        (fun position ↦ spatialBasis (cartesianMultiIndexWord index position)) := by
  exact closedDerivative_spec field (cartesianOrder index)
    (cartesianMultiIndexWord index)
    ⟨point, openDiskMembershipClosed point membership⟩ membership

theorem firstIteratedFDeriv_norm_le {dimension : ℕ}
    (field : ClosedJet dimension) {point : SpatialPlane}
    (membership : point ∈ openUnitDisk) (direction : SpatialPlane) :
    ‖iteratedFDeriv ℝ 1 (closedDiskLift field.value) point
        (fun _ ↦ direction)‖ ≤
      ‖direction‖ *
        (‖closedMultiDerivative field (1, 0)
            ⟨point, openDiskMembershipClosed point membership⟩‖ +
          ‖closedMultiDerivative field (0, 1)
            ⟨point, openDiskMembershipClosed point membership⟩‖) := by
  have firstIdentity := closedMultiDerivative_eq_iteratedFDeriv
    field membership (1, 0)
  have secondIdentity := closedMultiDerivative_eq_iteratedFDeriv
    field membership (0, 1)
  change closedMultiDerivative field (1, 0)
      ⟨point, openDiskMembershipClosed point membership⟩ =
    (iteratedFDeriv ℝ 1 (closedDiskLift field.value) point)
      (fun position : Fin 1 ↦
        spatialBasis (cartesianMultiIndexWord (1, 0) position)) at firstIdentity
  change closedMultiDerivative field (0, 1)
      ⟨point, openDiskMembershipClosed point membership⟩ =
    (iteratedFDeriv ℝ 1 (closedDiskLift field.value) point)
      (fun position : Fin 1 ↦
        spatialBasis (cartesianMultiIndexWord (0, 1) position)) at secondIdentity
  rw [iteratedFDeriv_one_apply] at firstIdentity secondIdentity
  have firstIdentity' :
      closedMultiDerivative field (1, 0)
          ⟨point, openDiskMembershipClosed point membership⟩ =
        fderiv ℝ (closedDiskLift field.value) point (spatialBasis 0) := by
    simpa [cartesianOrder, cartesianMultiIndexWord, iteratedFDeriv_one_apply]
      using firstIdentity
  have secondIdentity' :
      closedMultiDerivative field (0, 1)
          ⟨point, openDiskMembershipClosed point membership⟩ =
        fderiv ℝ (closedDiskLift field.value) point (spatialBasis 1) := by
    simpa [cartesianOrder, cartesianMultiIndexWord, iteratedFDeriv_one_apply]
      using secondIdentity
  have directionIdentity := spatialPlane_decompose direction
  calc
    ‖iteratedFDeriv ℝ 1 (closedDiskLift field.value) point
        (fun _ ↦ direction)‖ =
      ‖fderiv ℝ (closedDiskLift field.value) point direction‖ := by
        rw [iteratedFDeriv_one_apply]
    _ = ‖direction 0 • fderiv ℝ (closedDiskLift field.value) point (spatialBasis 0) +
        direction 1 • fderiv ℝ (closedDiskLift field.value) point (spatialBasis 1)‖ := by
      conv_lhs => rw [directionIdentity, map_add, map_smul, map_smul]
    _ ≤ |direction 0| *
          ‖fderiv ℝ (closedDiskLift field.value) point (spatialBasis 0)‖ +
        |direction 1| *
          ‖fderiv ℝ (closedDiskLift field.value) point (spatialBasis 1)‖ := by
      simpa [norm_smul, Real.norm_eq_abs] using norm_add_le
        (direction 0 • fderiv ℝ (closedDiskLift field.value) point (spatialBasis 0))
        (direction 1 • fderiv ℝ (closedDiskLift field.value) point (spatialBasis 1))
    _ ≤ ‖direction‖ *
        (‖fderiv ℝ (closedDiskLift field.value) point (spatialBasis 0)‖ +
          ‖fderiv ℝ (closedDiskLift field.value) point (spatialBasis 1)‖) := by
      have firstCoordinate := spatialCoordinate_abs_le_norm direction 0
      have secondCoordinate := spatialCoordinate_abs_le_norm direction 1
      nlinarith [norm_nonneg
        (fderiv ℝ (closedDiskLift field.value) point (spatialBasis 0)),
        norm_nonneg
        (fderiv ℝ (closedDiskLift field.value) point (spatialBasis 1))]
    _ = _ := by rw [← firstIdentity', ← secondIdentity']

/-- An ordered coordinate value of the Hessian. -/
def orderedSecondDerivative {dimension : ℕ} (field : ClosedJet dimension)
    (point : SpatialPlane) (word : Fin 2 → Fin 2) : ComplexEuclidean dimension :=
  iteratedFDeriv ℝ 2 (closedDiskLift field.value) point
    (fun position ↦ spatialBasis (word position))

theorem orderedSecondDerivative_norm_le_six_sum {dimension : ℕ}
    (field : ClosedJet dimension) {point : SpatialPlane}
    (membership : point ∈ openUnitDisk) (word : Fin 2 → Fin 2) :
    ‖orderedSecondDerivative field point word‖ ≤
      ∑ slot : Fin 6,
        ‖closedMultiDerivative field (diskSupMultiIndex slot)
          ⟨point, openDiskMembershipClosed point membership⟩‖ := by
  classical
  have smoothAt : ContDiffAt ℝ 2 (closedDiskLift field.value) point :=
    ((field.smoothInterior point membership).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
      (openUnitDisk_isOpen.mem_nhds membership)
  have symmetric := smoothAt.isSymmSndFDerivAt (by simp)
  have index20 := closedMultiDerivative_eq_iteratedFDeriv field membership (2, 0)
  have index11 := closedMultiDerivative_eq_iteratedFDeriv field membership (1, 1)
  have index02 := closedMultiDerivative_eq_iteratedFDeriv field membership (0, 2)
  have componentNonnegative : ∀ slot : Fin 6,
      0 ≤ ‖closedMultiDerivative field (diskSupMultiIndex slot)
        ⟨point, openDiskMembershipClosed point membership⟩‖ :=
    fun _ ↦ norm_nonneg _
  generalize hFirst : word 0 = first
  generalize hSecond : word 1 = second
  fin_cases first <;> fin_cases second
  · have wordIdentity : word = ![0, 0] := by
      funext position
      fin_cases position <;> assumption
    subst word
    rw [show orderedSecondDerivative field point ![0, 0] =
        closedMultiDerivative field (2, 0)
          ⟨point, openDiskMembershipClosed point membership⟩ by
      unfold orderedSecondDerivative
      calc
        _ = iteratedFDeriv ℝ 2 (closedDiskLift field.value) point
            (fun position ↦ spatialBasis
              (cartesianMultiIndexWord (2, 0) position)) := by
          congr 1
          funext position
          fin_cases position <;> rfl
        _ = _ := index20.symm]
    simpa [diskSupMultiIndex] using
      (Finset.single_le_sum (s := Finset.univ)
        (fun slot _ ↦ componentNonnegative slot) (Finset.mem_univ (3 : Fin 6)))
  · have wordIdentity : word = ![0, 1] := by
      funext position
      fin_cases position <;> assumption
    subst word
    rw [show orderedSecondDerivative field point ![0, 1] =
        closedMultiDerivative field (1, 1)
          ⟨point, openDiskMembershipClosed point membership⟩ by
      unfold orderedSecondDerivative
      calc
        _ = iteratedFDeriv ℝ 2 (closedDiskLift field.value) point
            (fun position ↦ spatialBasis
              (cartesianMultiIndexWord (1, 1) position)) := by
          congr 1
          funext position
          fin_cases position <;> rfl
        _ = _ := index11.symm]
    simpa [diskSupMultiIndex] using
      (Finset.single_le_sum (s := Finset.univ)
        (fun slot _ ↦ componentNonnegative slot) (Finset.mem_univ (4 : Fin 6)))
  · have wordIdentity : word = ![1, 0] := by
      funext position
      fin_cases position <;> assumption
    subst word
    have swapped : orderedSecondDerivative field point ![1, 0] =
        orderedSecondDerivative field point ![0, 1] := by
      unfold orderedSecondDerivative
      have symmetryValue := symmetric.iteratedFDeriv_cons
        (v := spatialBasis 1) (w := spatialBasis 0)
      convert symmetryValue using 1 <;>
        congr 1 <;> funext position <;> fin_cases position <;> rfl
    rw [swapped]
    rw [show orderedSecondDerivative field point ![0, 1] =
        closedMultiDerivative field (1, 1)
          ⟨point, openDiskMembershipClosed point membership⟩ by
      unfold orderedSecondDerivative
      calc
        _ = iteratedFDeriv ℝ 2 (closedDiskLift field.value) point
            (fun position ↦ spatialBasis
              (cartesianMultiIndexWord (1, 1) position)) := by
          congr 1
          funext position
          fin_cases position <;> rfl
        _ = _ := index11.symm]
    simpa [diskSupMultiIndex] using
      (Finset.single_le_sum (s := Finset.univ)
        (fun slot _ ↦ componentNonnegative slot) (Finset.mem_univ (4 : Fin 6)))
  · have wordIdentity : word = ![1, 1] := by
      funext position
      fin_cases position <;> assumption
    subst word
    rw [show orderedSecondDerivative field point ![1, 1] =
        closedMultiDerivative field (0, 2)
          ⟨point, openDiskMembershipClosed point membership⟩ by
      unfold orderedSecondDerivative
      calc
        _ = iteratedFDeriv ℝ 2 (closedDiskLift field.value) point
            (fun position ↦ spatialBasis
              (cartesianMultiIndexWord (0, 2) position)) := by
          congr 1
          funext position
          fin_cases position <;> rfl
        _ = _ := index02.symm]
    simpa [diskSupMultiIndex] using
      (Finset.single_le_sum (s := Finset.univ)
        (fun slot _ ↦ componentNonnegative slot) (Finset.mem_univ (5 : Fin 6)))

theorem orderedSecondDerivative_zero_zero {dimension : ℕ}
    (field : ClosedJet dimension) {point : SpatialPlane}
    (membership : point ∈ openUnitDisk) :
    orderedSecondDerivative field point ![0, 0] =
      closedMultiDerivative field (2, 0)
        ⟨point, openDiskMembershipClosed point membership⟩ := by
  have identity := closedMultiDerivative_eq_iteratedFDeriv field membership (2, 0)
  unfold orderedSecondDerivative
  calc
    _ = iteratedFDeriv ℝ 2 (closedDiskLift field.value) point
        (fun position ↦ spatialBasis
          (cartesianMultiIndexWord (2, 0) position)) := by
      congr 1
      funext position
      fin_cases position <;> rfl
    _ = _ := identity.symm

theorem orderedSecondDerivative_zero_one {dimension : ℕ}
    (field : ClosedJet dimension) {point : SpatialPlane}
    (membership : point ∈ openUnitDisk) :
    orderedSecondDerivative field point ![0, 1] =
      closedMultiDerivative field (1, 1)
        ⟨point, openDiskMembershipClosed point membership⟩ := by
  have identity := closedMultiDerivative_eq_iteratedFDeriv field membership (1, 1)
  unfold orderedSecondDerivative
  calc
    _ = iteratedFDeriv ℝ 2 (closedDiskLift field.value) point
        (fun position ↦ spatialBasis
          (cartesianMultiIndexWord (1, 1) position)) := by
      congr 1
      funext position
      fin_cases position <;> rfl
    _ = _ := identity.symm

theorem orderedSecondDerivative_one_one {dimension : ℕ}
    (field : ClosedJet dimension) {point : SpatialPlane}
    (membership : point ∈ openUnitDisk) :
    orderedSecondDerivative field point ![1, 1] =
      closedMultiDerivative field (0, 2)
        ⟨point, openDiskMembershipClosed point membership⟩ := by
  have identity := closedMultiDerivative_eq_iteratedFDeriv field membership (0, 2)
  unfold orderedSecondDerivative
  calc
    _ = iteratedFDeriv ℝ 2 (closedDiskLift field.value) point
        (fun position ↦ spatialBasis
          (cartesianMultiIndexWord (0, 2) position)) := by
      congr 1
      funext position
      fin_cases position <;> rfl
    _ = _ := identity.symm

theorem orderedSecondDerivative_one_zero {dimension : ℕ}
    (field : ClosedJet dimension) {point : SpatialPlane}
    (membership : point ∈ openUnitDisk) :
    orderedSecondDerivative field point ![1, 0] =
      closedMultiDerivative field (1, 1)
        ⟨point, openDiskMembershipClosed point membership⟩ := by
  have smoothAt : ContDiffAt ℝ 2 (closedDiskLift field.value) point :=
    ((field.smoothInterior point membership).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
      (openUnitDisk_isOpen.mem_nhds membership)
  have symmetryValue := (smoothAt.isSymmSndFDerivAt (by simp)).iteratedFDeriv_cons
    (v := spatialBasis 1) (w := spatialBasis 0)
  calc
    orderedSecondDerivative field point ![1, 0] =
        orderedSecondDerivative field point ![0, 1] := by
      unfold orderedSecondDerivative
      convert symmetryValue using 1 <;>
        congr 1 <;> funext position <;> fin_cases position <;> rfl
    _ = _ := orderedSecondDerivative_zero_one field membership

/-- Sharp coordinate Hessian estimate: the mixed derivative appears exactly
twice, while the pure second derivatives appear once. -/
theorem secondIteratedFDeriv_norm_le_sharp {dimension : ℕ}
    (field : ClosedJet dimension) {point : SpatialPlane}
    (membership : point ∈ openUnitDisk) (direction : SpatialPlane) :
    ‖iteratedFDeriv ℝ 2 (closedDiskLift field.value) point
        (fun _ ↦ direction)‖ ≤
      ‖direction‖ ^ 2 *
        (‖closedMultiDerivative field (2, 0)
            ⟨point, openDiskMembershipClosed point membership⟩‖ +
          2 * ‖closedMultiDerivative field (1, 1)
            ⟨point, openDiskMembershipClosed point membership⟩‖ +
          ‖closedMultiDerivative field (0, 2)
            ⟨point, openDiskMembershipClosed point membership⟩‖) := by
  classical
  let derivative := iteratedFDeriv ℝ 2 (closedDiskLift field.value) point
  have directionAsSum : direction =
      ∑ coordinate : Fin 2, direction coordinate • spatialBasis coordinate := by
    simpa only [Fin.sum_univ_two] using spatialPlane_decompose direction
  have inputsAsSums : (fun _ : Fin 2 ↦ direction) =
      fun _ : Fin 2 ↦
        ∑ coordinate : Fin 2, direction coordinate • spatialBasis coordinate := by
    funext position
    exact directionAsSum
  have expansion :
      derivative (fun _ : Fin 2 ↦ direction) =
        ∑ word : Fin 2 → Fin 2,
          (∏ position : Fin 2, direction (word position)) •
            orderedSecondDerivative field point word := by
    dsimp only [derivative]
    rw [inputsAsSums, ContinuousMultilinearMap.map_sum]
    apply Finset.sum_congr rfl
    intro word _
    rw [ContinuousMultilinearMap.map_smul_univ]
    rfl
  have coefficientBound : ∀ word : Fin 2 → Fin 2,
      (∏ position : Fin 2, |direction (word position)|) ≤ ‖direction‖ ^ 2 := by
    intro word
    rw [Fin.prod_univ_two]
    rw [pow_two]
    exact mul_le_mul (spatialCoordinate_abs_le_norm direction (word 0))
      (spatialCoordinate_abs_le_norm direction (word 1))
      (abs_nonneg _) (norm_nonneg _)
  rw [show iteratedFDeriv ℝ 2 (closedDiskLift field.value) point = derivative from rfl,
    expansion]
  calc
    ‖∑ word : Fin 2 → Fin 2,
        (∏ position : Fin 2, direction (word position)) •
          orderedSecondDerivative field point word‖ ≤
      ∑ word : Fin 2 → Fin 2,
        ‖(∏ position : Fin 2, direction (word position)) •
          orderedSecondDerivative field point word‖ := norm_sum_le _ _
    _ = ∑ word : Fin 2 → Fin 2,
        (∏ position : Fin 2, |direction (word position)|) *
          ‖orderedSecondDerivative field point word‖ := by
      apply Finset.sum_congr rfl
      intro word _
      rw [norm_smul, Real.norm_eq_abs, Finset.abs_prod]
    _ ≤ ∑ word : Fin 2 → Fin 2,
        ‖direction‖ ^ 2 * ‖orderedSecondDerivative field point word‖ := by
      exact Finset.sum_le_sum fun word _ ↦
        mul_le_mul_of_nonneg_right (coefficientBound word) (norm_nonneg _)
    _ = ‖direction‖ ^ 2 *
        (‖closedMultiDerivative field (2, 0)
            ⟨point, openDiskMembershipClosed point membership⟩‖ +
          2 * ‖closedMultiDerivative field (1, 1)
            ⟨point, openDiskMembershipClosed point membership⟩‖ +
          ‖closedMultiDerivative field (0, 2)
            ⟨point, openDiskMembershipClosed point membership⟩‖) := by
      rw [show (Finset.univ : Finset (Fin 2 → Fin 2)) =
          {![0, 0], ![0, 1], ![1, 0], ![1, 1]} by decide]
      rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
      rw [orderedSecondDerivative_zero_zero field membership,
        orderedSecondDerivative_zero_one field membership,
        orderedSecondDerivative_one_zero field membership,
        orderedSecondDerivative_one_one field membership]
      ring

theorem secondIteratedFDeriv_norm_le {dimension : ℕ}
    (field : ClosedJet dimension) {point : SpatialPlane}
    (membership : point ∈ openUnitDisk) (direction : SpatialPlane) :
    ‖iteratedFDeriv ℝ 2 (closedDiskLift field.value) point
        (fun _ ↦ direction)‖ ≤
      2 * ‖direction‖ ^ 2 *
        (∑ slot : Fin 6,
          ‖closedMultiDerivative field (diskSupMultiIndex slot)
            ⟨point, openDiskMembershipClosed point membership⟩‖) := by
  classical
  let derivative := iteratedFDeriv ℝ 2 (closedDiskLift field.value) point
  let derivativeSum : ℝ := ∑ slot : Fin 6,
    ‖closedMultiDerivative field (diskSupMultiIndex slot)
      ⟨point, openDiskMembershipClosed point membership⟩‖
  have directionAsSum : direction =
      ∑ coordinate : Fin 2, direction coordinate • spatialBasis coordinate := by
    simpa only [Fin.sum_univ_two] using spatialPlane_decompose direction
  have inputsAsSums : (fun _ : Fin 2 ↦ direction) =
      fun _ : Fin 2 ↦
        ∑ coordinate : Fin 2, direction coordinate • spatialBasis coordinate := by
    funext position
    exact directionAsSum
  have expansion :
      derivative (fun _ : Fin 2 ↦ direction) =
        ∑ word : Fin 2 → Fin 2,
          (∏ position : Fin 2, direction (word position)) •
            orderedSecondDerivative field point word := by
    dsimp only [derivative]
    rw [inputsAsSums, ContinuousMultilinearMap.map_sum]
    apply Finset.sum_congr rfl
    intro word _
    rw [ContinuousMultilinearMap.map_smul_univ]
    rfl
  have coefficientSum :
      (∑ word : Fin 2 → Fin 2,
          ∏ position : Fin 2, |direction (word position)|) =
        (|direction 0| + |direction 1|) ^ 2 := by
    have productExpansion := Finset.sum_pow'
      (Finset.univ : Finset (Fin 2)) (fun coordinate ↦ |direction coordinate|) 2
    rw [Fin.sum_univ_two] at productExpansion
    have piUniverse : Fintype.piFinset (fun _ : Fin 2 ↦
        (Finset.univ : Finset (Fin 2))) = Finset.univ := by
      ext word
      simp
    rw [piUniverse] at productExpansion
    symm
    simpa using productExpansion
  have coordinateSquare :
      (|direction 0| + |direction 1|) ^ 2 ≤ 2 * ‖direction‖ ^ 2 := by
    have normSquare := PiLp.norm_sq_eq_of_L2
      (fun _ : Fin 2 ↦ ℝ) direction
    rw [Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs] at normSquare
    nlinarith [sq_nonneg (|direction 0| - |direction 1|)]
  rw [show iteratedFDeriv ℝ 2 (closedDiskLift field.value) point = derivative from rfl,
    expansion]
  calc
    ‖∑ word : Fin 2 → Fin 2,
        (∏ position : Fin 2, direction (word position)) •
          orderedSecondDerivative field point word‖ ≤
      ∑ word : Fin 2 → Fin 2,
        ‖(∏ position : Fin 2, direction (word position)) •
          orderedSecondDerivative field point word‖ := norm_sum_le _ _
    _ = ∑ word : Fin 2 → Fin 2,
        (∏ position : Fin 2, |direction (word position)|) *
          ‖orderedSecondDerivative field point word‖ := by
      apply Finset.sum_congr rfl
      intro word _
      rw [norm_smul, Real.norm_eq_abs, Finset.abs_prod]
    _ ≤ ∑ word : Fin 2 → Fin 2,
        (∏ position : Fin 2, |direction (word position)|) * derivativeSum := by
      apply Finset.sum_le_sum
      intro word _
      exact mul_le_mul_of_nonneg_left
        (orderedSecondDerivative_norm_le_six_sum field membership word)
        (Finset.prod_nonneg fun _ _ ↦ abs_nonneg _)
    _ = (∑ word : Fin 2 → Fin 2,
        ∏ position : Fin 2, |direction (word position)|) * derivativeSum := by
      rw [Finset.sum_mul]
    _ ≤ (2 * ‖direction‖ ^ 2) * derivativeSum := by
      rw [coefficientSum]
      exact mul_le_mul_of_nonneg_right coordinateSquare
        (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
    _ = _ := by ring

/-- The sum of the norms of the exact six derivatives at one closed disk
point. -/
def diskDerivativeNormSum {dimension : ℕ} (field : ClosedJet dimension)
    (point : ClosedDisk) : ℝ :=
  ∑ slot : Fin 6,
    ‖closedMultiDerivative field (diskSupMultiIndex slot) point‖

theorem diskDerivativeNormSum_nonneg {dimension : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk) :
    0 ≤ diskDerivativeNormSum field point := by
  exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

theorem continuous_diskDerivativeNormSum {dimension : ℕ}
    (field : ClosedJet dimension) :
    Continuous (diskDerivativeNormSum field) := by
  unfold diskDerivativeNormSum
  fun_prop

theorem value_norm_le_diskDerivativeNormSum {dimension : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk) :
    ‖field.value point‖ ≤ diskDerivativeNormSum field point := by
  rw [← closedMultiDerivative_zero field]
  simpa [diskDerivativeNormSum, diskSupMultiIndex] using
    (Finset.single_le_sum (s := Finset.univ)
      (fun slot _ ↦
        (norm_nonneg
          (closedMultiDerivative field (diskSupMultiIndex slot) point)))
      (Finset.mem_univ (0 : Fin 6)))

theorem firstDerivativeNormSum_le_diskDerivativeNormSum {dimension : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk) :
    ‖closedMultiDerivative field (1, 0) point‖ +
        ‖closedMultiDerivative field (0, 1) point‖ ≤
      diskDerivativeNormSum field point := by
  have h0 : 0 ≤ ‖closedMultiDerivative field (0, 0) point‖ := norm_nonneg _
  have h3 : 0 ≤ ‖closedMultiDerivative field (2, 0) point‖ := norm_nonneg _
  have h4 : 0 ≤ ‖closedMultiDerivative field (1, 1) point‖ := norm_nonneg _
  have h5 : 0 ≤ ‖closedMultiDerivative field (0, 2) point‖ := norm_nonneg _
  simp only [diskDerivativeNormSum, Fin.sum_univ_succ]
  simp [diskSupMultiIndex]
  linarith

/-- Continuous projection of the real line onto `[0,1]`. -/
def unitIntervalProjection (t : ℝ) : ℝ := max 0 (min 1 t)

theorem unitIntervalProjection_mem (t : ℝ) :
    unitIntervalProjection t ∈ Icc (0 : ℝ) 1 := by
  constructor <;> simp [unitIntervalProjection]

@[simp] theorem unitIntervalProjection_eq {t : ℝ} (membership : t ∈ Icc (0 : ℝ) 1) :
    unitIntervalProjection t = t := by
  rcases membership with ⟨lower, upper⟩
  simp [unitIntervalProjection, lower, upper]

theorem continuous_unitIntervalProjection : Continuous unitIntervalProjection := by
  unfold unitIntervalProjection
  fun_prop

/-- The closed-disk segment, extended continuously to all real parameters by
projection onto `[0,1]`. -/
def closedDiskSegment (point base : ClosedDisk) (t : ℝ) : ClosedDisk :=
  ⟨base.val + unitIntervalProjection t • (point.val - base.val), by
    have projected := unitIntervalProjection_mem t
    have baseBound : ‖base.val‖ ≤ 1 := base.property
    have pointBound : ‖point.val‖ ≤ 1 := point.property
    rcases projected with ⟨nonnegative, atMostOne⟩
    have oneMinusNonnegative : 0 ≤ 1 - unitIntervalProjection t := by linarith
    have identity : base.val + unitIntervalProjection t • (point.val - base.val) =
        (1 - unitIntervalProjection t) • base.val +
          unitIntervalProjection t • point.val := by module
    change ‖base.val + unitIntervalProjection t • (point.val - base.val)‖ ≤ 1
    rw [identity]
    calc
      ‖(1 - unitIntervalProjection t) • base.val +
          unitIntervalProjection t • point.val‖ ≤
        ‖(1 - unitIntervalProjection t) • base.val‖ +
          ‖unitIntervalProjection t • point.val‖ := norm_add_le _ _
      _ = (1 - unitIntervalProjection t) * ‖base.val‖ +
          unitIntervalProjection t * ‖point.val‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg oneMinusNonnegative, abs_of_nonneg nonnegative]
      _ ≤ (1 - unitIntervalProjection t) * 1 +
          unitIntervalProjection t * 1 := by
        gcongr
      _ = 1 := by ring⟩

theorem continuous_closedDiskSegment (point base : ClosedDisk) :
    Continuous (closedDiskSegment point base) := by
  apply Continuous.subtype_mk
  change Continuous fun t : ℝ ↦
    base.val + unitIntervalProjection t • (point.val - base.val)
  exact continuous_const.add
    (continuous_unitIntervalProjection.smul continuous_const)

/-- The pointwise norm bound furnished by second-order Taylor expansion before
averaging.  The constants `9/4` and `25/8` are the exact coarse bounds
`1 + 5/4` and `2 (5/4)^2`; both are strictly below the final factor `4`. -/
theorem closedJet_taylorNormBound {dimension : ℕ}
    (field : ClosedJet dimension) (point base : ClosedDisk)
    (pointMembership : point.val ∈ openUnitDisk)
    (baseMembership : base.val ∈ diskAverageSet) :
    ‖field.value point‖ ≤
      (9 / 4 : ℝ) * diskDerivativeNormSum field base +
      ∫ t in 0..1, (25 / 8 : ℝ) * (1 - t) *
        diskDerivativeNormSum field (closedDiskSegment point base t) := by
  have baseInside := diskAverageSet_subset_openUnitDisk baseMembership
  have taylor := closedJet_secondOrderTaylor field pointMembership baseInside
  have taylorSimple : field.value point =
      field.value base +
        iteratedFDeriv ℝ 1 (closedDiskLift field.value) base.val
          (fun _ ↦ point.val - base.val) +
        ∫ t in 0..1, (1 - t) •
          iteratedFDeriv ℝ 2 (closedDiskLift field.value)
            (base.val + t • (point.val - base.val))
              (fun _ ↦ point.val - base.val) := by
    simpa [closedDiskLift, point.property, base.property,
      Finset.sum_range_succ, Nat.factorial, add_assoc] using taylor
  have differenceBound : ‖point.val - base.val‖ ≤ 5 / 4 :=
    diskDifference_norm_le_five_fourths point.property baseMembership
  let remainderMajorant : ℝ → ℝ := fun t ↦
    (25 / 8 : ℝ) * (1 - t) *
      diskDerivativeNormSum field (closedDiskSegment point base t)
  have remainderMajorantContinuous : Continuous remainderMajorant := by
    unfold remainderMajorant
    exact (continuous_const.mul (continuous_const.sub continuous_id)).mul
      ((continuous_diskDerivativeNormSum field).comp
        (continuous_closedDiskSegment point base))
  have remainderBound :
      ‖∫ t in 0..1, (1 - t) •
          iteratedFDeriv ℝ 2 (closedDiskLift field.value)
            (base.val + t • (point.val - base.val))
              (fun _ ↦ point.val - base.val)‖ ≤
        ∫ t in 0..1, remainderMajorant t := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    · filter_upwards with t tMembership
      have closedInterval : t ∈ Icc (0 : ℝ) 1 :=
        ⟨tMembership.1.le, tMembership.2⟩
      have segmentInside := openDisk_segment pointMembership baseInside closedInterval
      have secondBound := secondIteratedFDeriv_norm_le field segmentInside
        (point.val - base.val)
      have segmentIdentity : closedDiskSegment point base t =
          ⟨base.val + t • (point.val - base.val),
            openDiskMembershipClosed _ segmentInside⟩ := by
        apply Subtype.ext
        simp [closedDiskSegment, unitIntervalProjection_eq closedInterval]
      have derivativeSumNonnegative : 0 ≤
          diskDerivativeNormSum field (closedDiskSegment point base t) :=
        diskDerivativeNormSum_nonneg field _
      have oneMinusNonnegative : 0 ≤ 1 - t := sub_nonneg.mpr tMembership.2
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg oneMinusNonnegative]
      change (1 - t) *
          ‖iteratedFDeriv ℝ 2 (closedDiskLift field.value)
            (base.val + t • (point.val - base.val))
              (fun _ ↦ point.val - base.val)‖ ≤ _
      dsimp only [remainderMajorant]
      rw [segmentIdentity]
      have weightedSecond := mul_le_mul_of_nonneg_left secondBound oneMinusNonnegative
      have segmentSumNonnegative : 0 ≤
          diskDerivativeNormSum field
            ⟨base.val + t • (point.val - base.val),
              openDiskMembershipClosed _ segmentInside⟩ :=
        diskDerivativeNormSum_nonneg field _
      have squareBound :
          2 * ‖point.val - base.val‖ ^ 2 ≤ (25 / 8 : ℝ) := by
        have squared := pow_le_pow_left₀ (norm_nonneg _) differenceBound 2
        nlinarith
      calc
        (1 - t) *
            ‖iteratedFDeriv ℝ 2 (closedDiskLift field.value)
              (base.val + t • (point.val - base.val))
                (fun _ ↦ point.val - base.val)‖ ≤
          (1 - t) * (2 * ‖point.val - base.val‖ ^ 2 *
            diskDerivativeNormSum field
              ⟨base.val + t • (point.val - base.val),
                openDiskMembershipClosed _ segmentInside⟩) := weightedSecond
        _ ≤ (1 - t) * ((25 / 8 : ℝ) *
            diskDerivativeNormSum field
              ⟨base.val + t • (point.val - base.val),
                openDiskMembershipClosed _ segmentInside⟩) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right squareBound segmentSumNonnegative)
            oneMinusNonnegative
        _ = (25 / 8 : ℝ) * (1 - t) *
            diskDerivativeNormSum field
              ⟨base.val + t • (point.val - base.val),
                openDiskMembershipClosed _ segmentInside⟩ := by ring
    · exact remainderMajorantContinuous.intervalIntegrable 0 1
  have firstBound := firstIteratedFDeriv_norm_le field baseInside
    (point.val - base.val)
  have firstSumBound := firstDerivativeNormSum_le_diskDerivativeNormSum field base
  have baseValueBound := value_norm_le_diskDerivativeNormSum field base
  have firstFinal :
      ‖iteratedFDeriv ℝ 1 (closedDiskLift field.value) base.val
          (fun _ ↦ point.val - base.val)‖ ≤
        (5 / 4 : ℝ) * diskDerivativeNormSum field base :=
    firstBound.trans (mul_le_mul differenceBound firstSumBound
      (by positivity) (by positivity))
  rw [taylorSimple]
  calc
    ‖field.value base +
        iteratedFDeriv ℝ 1 (closedDiskLift field.value) base.val
          (fun _ ↦ point.val - base.val) +
        ∫ t in 0..1, (1 - t) •
          iteratedFDeriv ℝ 2 (closedDiskLift field.value)
            (base.val + t • (point.val - base.val))
              (fun _ ↦ point.val - base.val)‖ ≤
      ‖field.value base‖ +
        ‖iteratedFDeriv ℝ 1 (closedDiskLift field.value) base.val
          (fun _ ↦ point.val - base.val)‖ +
        ‖∫ t in 0..1, (1 - t) •
          iteratedFDeriv ℝ 2 (closedDiskLift field.value)
            (base.val + t • (point.val - base.val))
              (fun _ ↦ point.val - base.val)‖ := by
      calc
        _ ≤ ‖field.value base +
              iteratedFDeriv ℝ 1 (closedDiskLift field.value) base.val
                (fun _ ↦ point.val - base.val)‖ +
            ‖∫ t in 0..1, (1 - t) •
              iteratedFDeriv ℝ 2 (closedDiskLift field.value)
                (base.val + t • (point.val - base.val))
                  (fun _ ↦ point.val - base.val)‖ := norm_add_le _ _
        _ ≤ _ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ diskDerivativeNormSum field base +
        (5 / 4 : ℝ) * diskDerivativeNormSum field base +
        ∫ t in 0..1, remainderMajorant t := by
      exact add_le_add (add_le_add baseValueBound firstFinal) remainderBound
    _ = (9 / 4 : ℝ) * diskDerivativeNormSum field base +
        ∫ t in 0..1, (25 / 8 : ℝ) * (1 - t) *
          diskDerivativeNormSum field (closedDiskSegment point base t) := by
      unfold remainderMajorant
      ring

theorem diskAverage_measure_in_openDisk :
    (volume.restrict openUnitDisk) diskAverageSet =
      ENNReal.ofReal (Real.pi / 16) := by
  rw [Measure.restrict_apply measurableSet_diskAverageSet]
  rw [inter_eq_left.mpr diskAverageSet_subset_openUnitDisk]
  exact volume_diskAverageSet

theorem diskAverage_measureReal_in_openDisk :
    (volume.restrict openUnitDisk).real diskAverageSet = Real.pi / 16 := by
  rw [Measure.real_def, diskAverage_measure_in_openDisk]
  rw [ENNReal.toReal_ofReal]
  positivity

/-- Cauchy--Schwarz on the averaging disk, with the L² norm taken on the
whole open unit disk exactly as in the Cartesian grades. -/
theorem diskAverage_integral_norm_le {dimension : ℕ}
    (continuousField : ContinuousMap ClosedDisk (ComplexEuclidean dimension)) :
    ∫ point : SpatialPlane in diskAverageSet,
        ‖closedDiskLift continuousField point‖
        ∂volume.restrict openUnitDisk ≤
      Real.sqrt (Real.pi / 16) *
        ‖closedContinuousToDiskL2 continuousField‖ := by
  classical
  let indicatorOne : SpatialPlane → ℝ :=
    diskAverageSet.indicator (fun _ ↦ 1)
  have indicatorNonnegative : 0 ≤ᵐ[volume.restrict openUnitDisk] indicatorOne := by
    filter_upwards with point
    by_cases membership : point ∈ diskAverageSet <;>
      simp [indicatorOne, membership]
  have fieldNonnegative : 0 ≤ᵐ[volume.restrict openUnitDisk]
      fun point : SpatialPlane ↦ ‖closedDiskLift continuousField point‖ :=
    Filter.Eventually.of_forall fun _ ↦ norm_nonneg _
  have indicatorMem : MemLp indicatorOne (ENNReal.ofReal 2)
      (volume.restrict openUnitDisk) := by
    exact (memLp_const (1 : ℝ)).indicator measurableSet_diskAverageSet
  have fieldMem : MemLp
      (fun point : SpatialPlane ↦ ‖closedDiskLift continuousField point‖)
      (ENNReal.ofReal 2)
      (volume.restrict openUnitDisk) := by
    simpa using (closedContinuous_memLp continuousField).norm
  have holder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict openUnitDisk) (p := (2 : ℝ)) (q := (2 : ℝ))
    (by rw [Real.holderConjugate_iff]; norm_num : (2 : ℝ).HolderConjugate 2)
    indicatorNonnegative fieldNonnegative indicatorMem fieldMem
  have leftIdentity :
      ∫ point : SpatialPlane,
          indicatorOne point * ‖closedDiskLift continuousField point‖
          ∂volume.restrict openUnitDisk =
        ∫ point : SpatialPlane in diskAverageSet,
          ‖closedDiskLift continuousField point‖
          ∂volume.restrict openUnitDisk := by
    unfold indicatorOne
    rw [← MeasureTheory.integral_indicator measurableSet_diskAverageSet]
    apply integral_congr_ae
    filter_upwards with point
    by_cases membership : point ∈ diskAverageSet <;>
      simp [membership]
  have firstFactor :
      (∫ point : SpatialPlane, indicatorOne point ^ (2 : ℝ)
          ∂volume.restrict openUnitDisk) ^ (1 / (2 : ℝ)) =
        Real.sqrt (Real.pi / 16) := by
    have integralIdentity :
        (∫ point : SpatialPlane, indicatorOne point ^ (2 : ℝ)
            ∂volume.restrict openUnitDisk) = Real.pi / 16 := by
      have pointwise :
          (fun point : SpatialPlane ↦ indicatorOne point ^ (2 : ℝ)) =
            indicatorOne := by
        funext point
        by_cases membership : point ∈ diskAverageSet <;>
          simp [indicatorOne, membership]
      rw [pointwise]
      unfold indicatorOne
      rw [MeasureTheory.integral_indicator measurableSet_diskAverageSet]
      simp [diskAverage_measureReal_in_openDisk]
    rw [integralIdentity, ← Real.sqrt_eq_rpow]
  have secondFactor :
      (∫ point : SpatialPlane,
          ‖closedDiskLift continuousField point‖ ^ (2 : ℝ)
          ∂volume.restrict openUnitDisk) ^ (1 / (2 : ℝ)) =
        ‖closedContinuousToDiskL2 continuousField‖ := by
    rw [show (∫ point : SpatialPlane,
          ‖closedDiskLift continuousField point‖ ^ (2 : ℝ)
          ∂volume.restrict openUnitDisk) =
        ‖closedContinuousToDiskL2 continuousField‖ ^ 2 by
      simpa only [Real.rpow_two] using
        (closedContinuousToDiskL2_norm_sq continuousField).symm]
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]
  rw [leftIdentity, firstFactor, secondFactor] at holder
  exact holder

/-- The open-disk representative extended by zero to the ambient plane.  This
is the representative used for affine changes of variables below. -/
def diskZeroExtension {dimension : ℕ}
    (continuousField : ContinuousMap ClosedDisk (ComplexEuclidean dimension)) :
    SpatialPlane → ComplexEuclidean dimension :=
  openUnitDisk.indicator (closedDiskLift continuousField)

theorem diskZeroExtension_eq {dimension : ℕ}
    (continuousField : ContinuousMap ClosedDisk (ComplexEuclidean dimension))
    {point : SpatialPlane} (membership : point ∈ openUnitDisk) :
    diskZeroExtension continuousField point = closedDiskLift continuousField point := by
  simp [diskZeroExtension, membership]

theorem diskZeroExtension_memLp {dimension : ℕ}
    (continuousField : ContinuousMap ClosedDisk (ComplexEuclidean dimension)) :
    MemLp (diskZeroExtension continuousField) 2 volume := by
  rw [diskZeroExtension, memLp_indicator_iff_restrict openUnitDisk_isOpen.measurableSet]
  exact closedContinuous_memLp continuousField

theorem diskZeroExtension_integral_norm_sq {dimension : ℕ}
    (continuousField : ContinuousMap ClosedDisk (ComplexEuclidean dimension)) :
    ∫ point : SpatialPlane, ‖diskZeroExtension continuousField point‖ ^ 2 =
      ‖closedContinuousToDiskL2 continuousField‖ ^ 2 := by
  have pointwise :
      (fun point : SpatialPlane ↦ ‖diskZeroExtension continuousField point‖ ^ 2) =
        openUnitDisk.indicator
          (fun point : SpatialPlane ↦ ‖closedDiskLift continuousField point‖ ^ 2) := by
    funext point
    by_cases membership : point ∈ openUnitDisk <;>
      simp [diskZeroExtension, membership]
  rw [pointwise, MeasureTheory.integral_indicator openUnitDisk_isOpen.measurableSet]
  exact (closedContinuousToDiskL2_norm_sq continuousField).symm

/-- Exact two-dimensional Jacobian for the translated positive dilation of the
zero-extended open-disk representative. -/
theorem diskZeroExtension_affine_integral_norm_sq {dimension : ℕ}
    (continuousField : ContinuousMap ClosedDisk (ComplexEuclidean dimension))
    (scale : ℝ) (scalePositive : 0 < scale) (shift : SpatialPlane) :
    ∫ point : SpatialPlane,
        ‖diskZeroExtension continuousField (scale • point + shift)‖ ^ 2 =
      scale⁻¹ ^ 2 * ‖closedContinuousToDiskL2 continuousField‖ ^ 2 := by
  have dilation := MeasureTheory.Measure.integral_comp_smul_of_nonneg volume
    (fun point : SpatialPlane ↦
      ‖diskZeroExtension continuousField (point + shift)‖ ^ 2)
    scale (hR := scalePositive.le)
  rw [MeasureTheory.integral_add_right_eq_self
    (fun point : SpatialPlane ↦ ‖diskZeroExtension continuousField point‖ ^ 2)
    shift] at dilation
  rw [diskZeroExtension_integral_norm_sq] at dilation
  simpa [Module.finrank_pi_fintype, smul_eq_mul, inv_pow] using dilation

/-- Scalar Cauchy--Schwarz on the fixed averaging disk, retaining the exact
area factor. -/
theorem diskAverage_integral_le_sqrt_integral_sq
    (function : SpatialPlane → ℝ)
    (nonnegative : ∀ point, 0 ≤ function point)
    (squareIntegrable : MemLp function (ENNReal.ofReal 2) volume) :
    ∫ point : SpatialPlane in diskAverageSet, function point
        ∂volume.restrict openUnitDisk ≤
      Real.sqrt (Real.pi / 16) *
        Real.sqrt (∫ point : SpatialPlane, function point ^ (2 : ℝ)) := by
  classical
  let indicatorOne : SpatialPlane → ℝ :=
    diskAverageSet.indicator (fun _ ↦ 1)
  have indicatorNonnegative :
      0 ≤ᵐ[volume.restrict openUnitDisk] indicatorOne := by
    filter_upwards with point
    by_cases membership : point ∈ diskAverageSet <;>
      simp [indicatorOne, membership]
  have functionNonnegative : 0 ≤ᵐ[volume.restrict openUnitDisk] function :=
    Filter.Eventually.of_forall nonnegative
  have indicatorMem : MemLp indicatorOne (ENNReal.ofReal 2)
      (volume.restrict openUnitDisk) := by
    exact (memLp_const (1 : ℝ)).indicator measurableSet_diskAverageSet
  have holder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict openUnitDisk) (p := (2 : ℝ)) (q := (2 : ℝ))
    (by rw [Real.holderConjugate_iff]; norm_num : (2 : ℝ).HolderConjugate 2)
    indicatorNonnegative functionNonnegative indicatorMem
      (squareIntegrable.restrict openUnitDisk)
  have leftIdentity :
      ∫ point : SpatialPlane, indicatorOne point * function point
          ∂volume.restrict openUnitDisk =
        ∫ point : SpatialPlane in diskAverageSet, function point
          ∂volume.restrict openUnitDisk := by
    unfold indicatorOne
    rw [← MeasureTheory.integral_indicator measurableSet_diskAverageSet]
    apply integral_congr_ae
    filter_upwards with point
    by_cases membership : point ∈ diskAverageSet <;>
      simp [membership]
  have firstFactor :
      (∫ point : SpatialPlane, indicatorOne point ^ (2 : ℝ)
          ∂volume.restrict openUnitDisk) ^
          (1 / (2 : ℝ)) = Real.sqrt (Real.pi / 16) := by
    have integralIdentity :
        (∫ point : SpatialPlane, indicatorOne point ^ (2 : ℝ)
            ∂volume.restrict openUnitDisk) = Real.pi / 16 := by
      have pointwise :
          (fun point : SpatialPlane ↦ indicatorOne point ^ (2 : ℝ)) =
            indicatorOne := by
        funext point
        by_cases membership : point ∈ diskAverageSet <;>
          simp [indicatorOne, membership]
      rw [pointwise]
      unfold indicatorOne
      rw [MeasureTheory.integral_indicator measurableSet_diskAverageSet]
      simp [diskAverage_measureReal_in_openDisk]
    rw [integralIdentity, ← Real.sqrt_eq_rpow]
  have squareIntegrableNat : MemLp function 2 volume := by
    simpa using squareIntegrable
  have squareIntegralBound :
      (∫ point : SpatialPlane, function point ^ (2 : ℝ)
          ∂volume.restrict openUnitDisk) ≤
        ∫ point : SpatialPlane, function point ^ (2 : ℝ) := by
    have integrableNat := squareIntegrableNat.integrable_sq
    have integrableReal : Integrable
        (fun point : SpatialPlane ↦ function point ^ (2 : ℝ)) volume := by
      simpa only [Real.rpow_two] using integrableNat
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun point ↦
        Real.rpow_nonneg (nonnegative point) _)
      integrableReal
  have squareRootBound := Real.sqrt_le_sqrt squareIntegralBound
  rw [leftIdentity, firstFactor] at holder
  rw [← Real.sqrt_eq_rpow] at holder
  exact holder.trans (mul_le_mul_of_nonneg_left squareRootBound (Real.sqrt_nonneg _))

theorem diskZeroExtension_affine_memLp {dimension : ℕ}
    (continuousField : ContinuousMap ClosedDisk (ComplexEuclidean dimension))
    (scale : ℝ) (scaleNonzero : scale ≠ 0) (shift : SpatialPlane) :
    MemLp (fun point : SpatialPlane ↦
      diskZeroExtension continuousField (scale • point + shift)) 2 volume := by
  have translated : MemLp
      (fun point : SpatialPlane ↦ diskZeroExtension continuousField (point + shift))
      2 volume := by
    change MemLp (diskZeroExtension continuousField ∘ fun point ↦ point + shift) 2 volume
    exact (diskZeroExtension_memLp continuousField).comp_measurePreserving
      (MeasureTheory.measurePreserving_add_right volume shift)
  have underMap : MemLp
      (fun point : SpatialPlane ↦ diskZeroExtension continuousField (point + shift))
      2 (Measure.map (fun point : SpatialPlane ↦ scale • point) volume) := by
    rw [MeasureTheory.Measure.map_addHaar_smul volume scaleNonzero]
    exact translated.smul_measure (by simp)
  change MemLp
    ((fun point : SpatialPlane ↦ diskZeroExtension continuousField (point + shift)) ∘
      fun point ↦ scale • point) 2 volume
  exact underMap.comp_of_map (measurable_const_smul scale).aemeasurable

/-- The affine estimate used in the Taylor remainder.  Its single inverse
power is the cancellation between the two-dimensional Jacobian and the
square root in Cauchy--Schwarz. -/
theorem diskAverage_affine_integral_norm_le {dimension : ℕ}
    (continuousField : ContinuousMap ClosedDisk (ComplexEuclidean dimension))
    (scale : ℝ) (scalePositive : 0 < scale) (shift : SpatialPlane) :
    ∫ base : SpatialPlane in diskAverageSet,
        ‖diskZeroExtension continuousField (scale • base + shift)‖
          ∂volume.restrict openUnitDisk ≤
      Real.sqrt (Real.pi / 16) * scale⁻¹ *
        ‖closedContinuousToDiskL2 continuousField‖ := by
  have estimate := diskAverage_integral_le_sqrt_integral_sq
    (fun base : SpatialPlane ↦
      ‖diskZeroExtension continuousField (scale • base + shift)‖)
    (fun _ ↦ norm_nonneg _)
    (by simpa using
      (diskZeroExtension_affine_memLp continuousField scale scalePositive.ne' shift).norm)
  rw [show (∫ point : SpatialPlane,
      ‖diskZeroExtension continuousField (scale • point + shift)‖ ^ (2 : ℝ)) =
        scale⁻¹ ^ 2 * ‖closedContinuousToDiskL2 continuousField‖ ^ 2 by
      simpa only [Real.rpow_two] using
        diskZeroExtension_affine_integral_norm_sq
          continuousField scale scalePositive shift] at estimate
  have squareRootIdentity :
      Real.sqrt (scale⁻¹ ^ 2 * ‖closedContinuousToDiskL2 continuousField‖ ^ 2) =
        scale⁻¹ * ‖closedContinuousToDiskL2 continuousField‖ := by
    rw [← mul_pow, Real.sqrt_sq]
    exact mul_nonneg (inv_nonneg.mpr scalePositive.le) (norm_nonneg _)
  rw [squareRootIdentity] at estimate
  simpa [mul_assoc] using estimate

/-- The six actual disk `L²` norms before the final finite-dimensional
Cauchy--Schwarz step. -/
def diskDerivativeL2NormSum {dimension : ℕ} (field : ClosedJet dimension) : ℝ :=
  ∑ slot : Fin 6, ‖closedDerivativeL2 (diskSupMultiIndex slot) field‖

theorem diskDerivativeL2NormSum_nonneg {dimension : ℕ} (field : ClosedJet dimension) :
    0 ≤ diskDerivativeL2NormSum field := by
  exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

/-- Ordered Hessian slots `(20,11,11,02)`, retaining the multiplicity of the
mixed derivative in the Taylor formula. -/
def diskSecondMultiIndex (slot : Fin 4) : CartesianMultiIndex :=
  match slot.1 with
  | 0 => (2, 0)
  | 1 => (1, 1)
  | 2 => (1, 1)
  | _ => (0, 2)

def diskSecondDerivativeNormSum {dimension : ℕ} (field : ClosedJet dimension)
    (point : ClosedDisk) : ℝ :=
  ∑ slot : Fin 4,
    ‖closedMultiDerivative field (diskSecondMultiIndex slot) point‖

def diskSecondDerivativeL2NormSum {dimension : ℕ} (field : ClosedJet dimension) : ℝ :=
  ∑ slot : Fin 4, ‖closedDerivativeL2 (diskSecondMultiIndex slot) field‖

theorem diskSecondDerivativeNormSum_formula {dimension : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk) :
    diskSecondDerivativeNormSum field point =
      ‖closedMultiDerivative field (2, 0) point‖ +
      2 * ‖closedMultiDerivative field (1, 1) point‖ +
      ‖closedMultiDerivative field (0, 2) point‖ := by
  simp [diskSecondDerivativeNormSum, diskSecondMultiIndex, Fin.sum_univ_succ]
  ring

theorem diskSecondDerivativeNormSum_nonneg {dimension : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk) :
    0 ≤ diskSecondDerivativeNormSum field point := by
  exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

theorem continuous_diskSecondDerivativeNormSum {dimension : ℕ}
    (field : ClosedJet dimension) :
    Continuous (diskSecondDerivativeNormSum field) := by
  unfold diskSecondDerivativeNormSum
  fun_prop

theorem diskSecondDerivativeL2NormSum_nonneg {dimension : ℕ}
    (field : ClosedJet dimension) : 0 ≤ diskSecondDerivativeL2NormSum field := by
  exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

theorem diskAverage_affine_derivativeNormSum_le {dimension : ℕ}
    (field : ClosedJet dimension) (scale : ℝ) (scalePositive : 0 < scale)
    (shift : SpatialPlane) :
    ∫ base : SpatialPlane in diskAverageSet,
        (∑ slot : Fin 6,
          ‖diskZeroExtension
            (closedMultiDerivative field (diskSupMultiIndex slot))
            (scale • base + shift)‖)
        ∂volume.restrict openUnitDisk ≤
      Real.sqrt (Real.pi / 16) * scale⁻¹ *
        diskDerivativeL2NormSum field := by
  have integrableSlot : ∀ slot : Fin 6, IntegrableOn
      (fun base : SpatialPlane ↦
          ‖diskZeroExtension
          (closedMultiDerivative field (diskSupMultiIndex slot))
          (scale • base + shift)‖)
      diskAverageSet (volume.restrict openUnitDisk) := by
    intro slot
    have mem : MemLp
        (fun base : SpatialPlane ↦
          ‖diskZeroExtension
            (closedMultiDerivative field (diskSupMultiIndex slot))
            (scale • base + shift)‖)
        2 (volume.restrict openUnitDisk) :=
      ((diskZeroExtension_affine_memLp
        (closedMultiDerivative field (diskSupMultiIndex slot))
        scale scalePositive.ne' shift).norm.restrict openUnitDisk)
    exact (mem.integrable (by norm_num)).integrableOn
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun slot _ ↦ integrableSlot slot)]
  calc
    ∑ slot : Fin 6,
        ∫ base : SpatialPlane in diskAverageSet,
          ‖diskZeroExtension
            (closedMultiDerivative field (diskSupMultiIndex slot))
            (scale • base + shift)‖
          ∂volume.restrict openUnitDisk ≤
      ∑ slot : Fin 6,
        (Real.sqrt (Real.pi / 16) * scale⁻¹ *
          ‖closedDerivativeL2 (diskSupMultiIndex slot) field‖) := by
      exact Finset.sum_le_sum fun slot _ ↦
        diskAverage_affine_integral_norm_le
          (closedMultiDerivative field (diskSupMultiIndex slot))
          scale scalePositive shift
    _ = Real.sqrt (Real.pi / 16) * scale⁻¹ *
        diskDerivativeL2NormSum field := by
      simp only [diskDerivativeL2NormSum, Finset.mul_sum]

theorem diskAverage_affine_secondDerivativeNormSum_le {dimension : ℕ}
    (field : ClosedJet dimension) (scale : ℝ) (scalePositive : 0 < scale)
    (shift : SpatialPlane) :
    ∫ base : SpatialPlane in diskAverageSet,
        (∑ slot : Fin 4,
          ‖diskZeroExtension
            (closedMultiDerivative field (diskSecondMultiIndex slot))
            (scale • base + shift)‖)
        ∂volume.restrict openUnitDisk ≤
      Real.sqrt (Real.pi / 16) * scale⁻¹ *
        diskSecondDerivativeL2NormSum field := by
  have integrableSlot : ∀ slot : Fin 4, IntegrableOn
      (fun base : SpatialPlane ↦
        ‖diskZeroExtension
          (closedMultiDerivative field (diskSecondMultiIndex slot))
          (scale • base + shift)‖)
      diskAverageSet (volume.restrict openUnitDisk) := by
    intro slot
    have mem : MemLp
        (fun base : SpatialPlane ↦
          ‖diskZeroExtension
            (closedMultiDerivative field (diskSecondMultiIndex slot))
            (scale • base + shift)‖)
        2 (volume.restrict openUnitDisk) :=
      ((diskZeroExtension_affine_memLp
        (closedMultiDerivative field (diskSecondMultiIndex slot))
        scale scalePositive.ne' shift).norm.restrict openUnitDisk)
    exact (mem.integrable (by norm_num)).integrableOn
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun slot _ ↦ integrableSlot slot)]
  calc
    ∑ slot : Fin 4,
        ∫ base : SpatialPlane in diskAverageSet,
          ‖diskZeroExtension
            (closedMultiDerivative field (diskSecondMultiIndex slot))
            (scale • base + shift)‖
          ∂volume.restrict openUnitDisk ≤
      ∑ slot : Fin 4,
        (Real.sqrt (Real.pi / 16) * scale⁻¹ *
          ‖closedDerivativeL2 (diskSecondMultiIndex slot) field‖) := by
      exact Finset.sum_le_sum fun slot _ ↦
        diskAverage_affine_integral_norm_le
          (closedMultiDerivative field (diskSecondMultiIndex slot))
          scale scalePositive shift
    _ = Real.sqrt (Real.pi / 16) * scale⁻¹ *
        diskSecondDerivativeL2NormSum field := by
      simp only [diskSecondDerivativeL2NormSum, Finset.mul_sum]

/-- Continuous radial projection of the ambient plane to the closed unit disk.
It is literally the identity on the disk and lets the averaging integrands be
defined on the ambient measure space without any choice of membership proof. -/
def ambientClosedDisk (point : SpatialPlane) : ClosedDisk :=
  ⟨(max 1 ‖point‖)⁻¹ • point, by
    change ‖(max 1 ‖point‖)⁻¹ • point‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs]
    have maximumPositive : 0 < max 1 ‖point‖ :=
      lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    rw [abs_of_pos (inv_pos.mpr maximumPositive)]
    rw [inv_mul_eq_div]
    exact (div_le_one maximumPositive).mpr (le_max_right _ _)⟩

@[simp] theorem ambientClosedDisk_val_of_mem {point : SpatialPlane}
    (membership : point ∈ closedUnitDisk) :
    (ambientClosedDisk point).val = point := by
  change (max 1 ‖point‖)⁻¹ • point = point
  rw [max_eq_left membership]
  simp

theorem continuous_ambientClosedDisk : Continuous ambientClosedDisk := by
  apply Continuous.subtype_mk
  change Continuous fun point : SpatialPlane ↦ (max 1 ‖point‖)⁻¹ • point
  have denominatorContinuous : Continuous fun point : SpatialPlane ↦ max 1 ‖point‖ :=
    continuous_const.max continuous_norm
  have denominatorNonzero : ∀ point : SpatialPlane, max 1 ‖point‖ ≠ 0 :=
    fun point ↦ ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  exact (denominatorContinuous.inv₀ denominatorNonzero).smul continuous_id

/-- The six derivative norms along the clamped segment from an ambient base
point to a fixed disk point. -/
def averagedSegmentDerivativeNormSum {dimension : ℕ} (field : ClosedJet dimension)
    (point : ClosedDisk) (base : SpatialPlane) (t : ℝ) : ℝ :=
  diskDerivativeNormSum field (closedDiskSegment point (ambientClosedDisk base) t)

theorem continuous_averagedSegmentDerivativeNormSum {dimension : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk) :
    Continuous fun input : SpatialPlane × ℝ ↦
      averagedSegmentDerivativeNormSum field point input.1 input.2 := by
  apply (continuous_diskDerivativeNormSum field).comp
  apply Continuous.subtype_mk
  change Continuous fun input : SpatialPlane × ℝ ↦
    (ambientClosedDisk input.1).val + unitIntervalProjection input.2 •
      (point.val - (ambientClosedDisk input.1).val)
  have baseContinuous : Continuous fun input : SpatialPlane × ℝ ↦
      (ambientClosedDisk input.1).val :=
    continuous_subtype_val.comp (continuous_ambientClosedDisk.comp continuous_fst)
  exact baseContinuous.add
    ((continuous_unitIntervalProjection.comp continuous_snd).smul
      (continuous_const.sub baseContinuous))

theorem averagedSegmentDerivativeNormSum_eq_affine {dimension : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk)
    (pointMembership : point.val ∈ openUnitDisk) (base : SpatialPlane)
    (baseMembership : base ∈ diskAverageSet) (t : ℝ) (tMembership : t ∈ Icc 0 1) :
    averagedSegmentDerivativeNormSum field point base t =
      ∑ slot : Fin 6,
        ‖diskZeroExtension
          (closedMultiDerivative field (diskSupMultiIndex slot))
          ((1 - t) • base + t • point.val)‖ := by
  have baseInsideOpen := diskAverageSet_subset_openUnitDisk baseMembership
  have baseInsideClosed := openDiskMembershipClosed base baseInsideOpen
  have segmentInside := openDisk_segment pointMembership baseInsideOpen tMembership
  have affineInside : (1 - t) • base + t • point.val ∈ openUnitDisk := by
    rw [show (1 - t) • base + t • point.val =
      base + t • (point.val - base) by module]
    exact segmentInside
  have segmentValue :
      (closedDiskSegment point (ambientClosedDisk base) t).val =
        (1 - t) • base + t • point.val := by
    simp only [closedDiskSegment, ambientClosedDisk_val_of_mem baseInsideClosed,
      unitIntervalProjection_eq tMembership]
    module
  unfold averagedSegmentDerivativeNormSum diskDerivativeNormSum
  apply Finset.sum_congr rfl
  intro slot _
  rw [diskZeroExtension_eq
    (closedMultiDerivative field (diskSupMultiIndex slot))
    affineInside]
  unfold closedDiskLift
  rw [dif_pos (openDiskMembershipClosed _ affineInside)]
  congr 2
  exact Subtype.ext segmentValue

theorem restrict_openDisk_restrict_diskAverageSet :
    (volume.restrict openUnitDisk).restrict diskAverageSet =
      volume.restrict diskAverageSet :=
  Measure.restrict_restrict_of_subset diskAverageSet_subset_openUnitDisk

theorem diskAverage_integral_norm_le_volume {dimension : ℕ}
    (continuousField : ContinuousMap ClosedDisk (ComplexEuclidean dimension)) :
    ∫ point : SpatialPlane in diskAverageSet,
        ‖closedDiskLift continuousField point‖ ≤
      Real.sqrt (Real.pi / 16) *
        ‖closedContinuousToDiskL2 continuousField‖ := by
  have estimate := diskAverage_integral_norm_le continuousField
  change (∫ point : SpatialPlane, ‖closedDiskLift continuousField point‖
      ∂volume.restrict diskAverageSet) ≤ _
  rw [← restrict_openDisk_restrict_diskAverageSet]
  exact estimate

theorem diskDerivativeL2NormSum_le_sqrt_energy {dimension : ℕ}
    (field : ClosedJet dimension) :
    diskDerivativeL2NormSum field ≤
      Real.sqrt 6 * Real.sqrt (diskSupEnergy field) := by
  have cauchy := Real.sum_mul_le_sqrt_mul_sqrt
    (Finset.univ : Finset (Fin 6))
    (fun _ ↦ (1 : ℝ))
    (fun slot ↦ ‖closedDerivativeL2 (diskSupMultiIndex slot) field‖)
  simpa [diskDerivativeL2NormSum, diskSupEnergy] using cauchy

theorem diskAverage_ambientClosedDisk_norm_le {dimension : ℕ}
    (continuousField : ContinuousMap ClosedDisk (ComplexEuclidean dimension)) :
    ∫ base : SpatialPlane in diskAverageSet,
        ‖continuousField (ambientClosedDisk base)‖ ≤
      Real.sqrt (Real.pi / 16) *
        ‖closedContinuousToDiskL2 continuousField‖ := by
  have equality :
      (∫ base : SpatialPlane in diskAverageSet,
        ‖continuousField (ambientClosedDisk base)‖) =
      ∫ base : SpatialPlane in diskAverageSet,
        ‖closedDiskLift continuousField base‖ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_diskAverageSet] with
      base baseMembership
    have openMembership := diskAverageSet_subset_openUnitDisk baseMembership
    have closedMembership := openDiskMembershipClosed base openMembership
    have liftEquality : closedDiskLift continuousField base =
        continuousField (ambientClosedDisk base) := by
      unfold closedDiskLift
      rw [dif_pos closedMembership]
      have subtypeEquality : (⟨base, closedMembership⟩ : ClosedDisk) =
          ambientClosedDisk base := by
        apply Subtype.ext
        exact (ambientClosedDisk_val_of_mem closedMembership).symm
      rw [subtypeEquality]
    rw [liftEquality]
  rw [equality]
  exact diskAverage_integral_norm_le_volume continuousField

theorem diskDerivativeL2NormSum_formula {dimension : ℕ}
    (field : ClosedJet dimension) :
    diskDerivativeL2NormSum field =
      ‖closedDerivativeL2 (0, 0) field‖ +
      ‖closedDerivativeL2 (1, 0) field‖ +
      ‖closedDerivativeL2 (0, 1) field‖ +
      ‖closedDerivativeL2 (2, 0) field‖ +
      ‖closedDerivativeL2 (1, 1) field‖ +
      ‖closedDerivativeL2 (0, 2) field‖ := by
  simp [diskDerivativeL2NormSum, diskSupMultiIndex, Fin.sum_univ_succ]
  ring

theorem diskSecondDerivativeL2NormSum_formula {dimension : ℕ}
    (field : ClosedJet dimension) :
    diskSecondDerivativeL2NormSum field =
      ‖closedDerivativeL2 (2, 0) field‖ +
      2 * ‖closedDerivativeL2 (1, 1) field‖ +
      ‖closedDerivativeL2 (0, 2) field‖ := by
  simp [diskSecondDerivativeL2NormSum, diskSecondMultiIndex, Fin.sum_univ_succ]
  ring

theorem sharpWeightedL2Sum_le_four {dimension : ℕ}
    (field : ClosedJet dimension) :
    Real.sqrt (Real.pi / 16) * ‖closedDerivativeL2 (0, 0) field‖ +
        (5 / 4 : ℝ) * Real.sqrt (Real.pi / 16) *
          (‖closedDerivativeL2 (1, 0) field‖ +
            ‖closedDerivativeL2 (0, 1) field‖) +
        (25 / 16 : ℝ) * Real.sqrt (Real.pi / 16) *
          diskSecondDerivativeL2NormSum field ≤
      4 * Real.sqrt (Real.pi / 16) * diskDerivativeL2NormSum field := by
  rw [diskDerivativeL2NormSum_formula, diskSecondDerivativeL2NormSum_formula]
  have rootNonnegative : 0 ≤ Real.sqrt (Real.pi / 16) := Real.sqrt_nonneg _
  nlinarith [norm_nonneg (closedDerivativeL2 (0, 0) field),
    norm_nonneg (closedDerivativeL2 (1, 0) field),
    norm_nonneg (closedDerivativeL2 (0, 1) field),
    norm_nonneg (closedDerivativeL2 (2, 0) field),
    norm_nonneg (closedDerivativeL2 (1, 1) field),
    norm_nonneg (closedDerivativeL2 (0, 2) field)]

theorem diskAverage_affine_derivativeNormSum_le_volume {dimension : ℕ}
    (field : ClosedJet dimension) (scale : ℝ) (scalePositive : 0 < scale)
    (shift : SpatialPlane) :
    ∫ base : SpatialPlane in diskAverageSet,
        (∑ slot : Fin 6,
          ‖diskZeroExtension
            (closedMultiDerivative field (diskSupMultiIndex slot))
            (scale • base + shift)‖) ≤
      Real.sqrt (Real.pi / 16) * scale⁻¹ *
        diskDerivativeL2NormSum field := by
  have estimate := diskAverage_affine_derivativeNormSum_le
    field scale scalePositive shift
  change (∫ base : SpatialPlane,
      ∑ slot : Fin 6,
        ‖diskZeroExtension
          (closedMultiDerivative field (diskSupMultiIndex slot))
          (scale • base + shift)‖
      ∂volume.restrict diskAverageSet) ≤ _
  rw [← restrict_openDisk_restrict_diskAverageSet]
  exact estimate

theorem diskAverage_affine_secondDerivativeNormSum_le_volume {dimension : ℕ}
    (field : ClosedJet dimension) (scale : ℝ) (scalePositive : 0 < scale)
    (shift : SpatialPlane) :
    ∫ base : SpatialPlane in diskAverageSet,
        (∑ slot : Fin 4,
          ‖diskZeroExtension
            (closedMultiDerivative field (diskSecondMultiIndex slot))
            (scale • base + shift)‖) ≤
      Real.sqrt (Real.pi / 16) * scale⁻¹ *
        diskSecondDerivativeL2NormSum field := by
  have estimate := diskAverage_affine_secondDerivativeNormSum_le
    field scale scalePositive shift
  change (∫ base : SpatialPlane,
      ∑ slot : Fin 4,
        ‖diskZeroExtension
          (closedMultiDerivative field (diskSecondMultiIndex slot))
          (scale • base + shift)‖
      ∂volume.restrict diskAverageSet) ≤ _
  rw [← restrict_openDisk_restrict_diskAverageSet]
  exact estimate

/-- Sharp Taylor bound retaining the disjoint zeroth, first and ordered-second
derivative groups needed to keep the paper's numerical constant. -/
theorem closedJet_taylorNormBound_sharp {dimension : ℕ}
    (field : ClosedJet dimension) (point base : ClosedDisk)
    (pointMembership : point.val ∈ openUnitDisk)
    (baseMembership : base.val ∈ diskAverageSet) :
    ‖field.value point‖ ≤
      ‖field.value base‖ +
      (5 / 4 : ℝ) *
        (‖closedMultiDerivative field (1, 0) base‖ +
          ‖closedMultiDerivative field (0, 1) base‖) +
      ∫ t in 0..1, (25 / 16 : ℝ) * (1 - t) *
        diskSecondDerivativeNormSum field (closedDiskSegment point base t) := by
  have baseInside := diskAverageSet_subset_openUnitDisk baseMembership
  have taylor := closedJet_secondOrderTaylor field pointMembership baseInside
  have taylorSimple : field.value point =
      field.value base +
        iteratedFDeriv ℝ 1 (closedDiskLift field.value) base.val
          (fun _ ↦ point.val - base.val) +
        ∫ t in 0..1, (1 - t) •
          iteratedFDeriv ℝ 2 (closedDiskLift field.value)
            (base.val + t • (point.val - base.val))
              (fun _ ↦ point.val - base.val) := by
    simpa [closedDiskLift, point.property, base.property,
      Finset.sum_range_succ, Nat.factorial, add_assoc] using taylor
  have differenceBound : ‖point.val - base.val‖ ≤ 5 / 4 :=
    diskDifference_norm_le_five_fourths point.property baseMembership
  have firstBound := firstIteratedFDeriv_norm_le field baseInside
    (point.val - base.val)
  have firstFinal :
      ‖iteratedFDeriv ℝ 1 (closedDiskLift field.value) base.val
          (fun _ ↦ point.val - base.val)‖ ≤
        (5 / 4 : ℝ) *
          (‖closedMultiDerivative field (1, 0) base‖ +
            ‖closedMultiDerivative field (0, 1) base‖) := by
    exact firstBound.trans
      (mul_le_mul_of_nonneg_right differenceBound
        (add_nonneg (norm_nonneg _) (norm_nonneg _)))
  have remainderBound :
      ‖∫ t in 0..1, (1 - t) •
          iteratedFDeriv ℝ 2 (closedDiskLift field.value)
            (base.val + t • (point.val - base.val))
              (fun _ ↦ point.val - base.val)‖ ≤
        ∫ t in 0..1, (25 / 16 : ℝ) * (1 - t) *
          diskSecondDerivativeNormSum field (closedDiskSegment point base t) := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    · filter_upwards with t tInterval
      have closedInterval : t ∈ Icc (0 : ℝ) 1 :=
        ⟨tInterval.1.le, tInterval.2⟩
      have segmentInside := openDisk_segment pointMembership baseInside closedInterval
      have secondBound := secondIteratedFDeriv_norm_le_sharp field segmentInside
        (point.val - base.val)
      have segmentIdentity : closedDiskSegment point base t =
          ⟨base.val + t • (point.val - base.val),
            openDiskMembershipClosed _ segmentInside⟩ := by
        apply Subtype.ext
        simp [closedDiskSegment, unitIntervalProjection_eq closedInterval]
      have squareBound : ‖point.val - base.val‖ ^ 2 ≤ (25 / 16 : ℝ) := by
        have squared := pow_le_pow_left₀ (norm_nonneg _) differenceBound 2
        nlinarith
      have secondSumNonnegative : 0 ≤ diskSecondDerivativeNormSum field
          ⟨base.val + t • (point.val - base.val),
            openDiskMembershipClosed _ segmentInside⟩ :=
        diskSecondDerivativeNormSum_nonneg field _
      rw [diskSecondDerivativeNormSum_formula] at secondSumNonnegative
      have oneMinusNonnegative : 0 ≤ 1 - t := sub_nonneg.mpr tInterval.2
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg oneMinusNonnegative]
      change (1 - t) *
          ‖iteratedFDeriv ℝ 2 (closedDiskLift field.value)
            (base.val + t • (point.val - base.val))
              (fun _ ↦ point.val - base.val)‖ ≤ _
      rw [segmentIdentity, diskSecondDerivativeNormSum_formula]
      calc
        (1 - t) *
            ‖iteratedFDeriv ℝ 2 (closedDiskLift field.value)
              (base.val + t • (point.val - base.val))
                (fun _ ↦ point.val - base.val)‖ ≤
          (1 - t) * (‖point.val - base.val‖ ^ 2 *
            (‖closedMultiDerivative field (2, 0)
                ⟨base.val + t • (point.val - base.val),
                  openDiskMembershipClosed _ segmentInside⟩‖ +
              2 * ‖closedMultiDerivative field (1, 1)
                ⟨base.val + t • (point.val - base.val),
                  openDiskMembershipClosed _ segmentInside⟩‖ +
              ‖closedMultiDerivative field (0, 2)
                ⟨base.val + t • (point.val - base.val),
                  openDiskMembershipClosed _ segmentInside⟩‖)) :=
            mul_le_mul_of_nonneg_left secondBound oneMinusNonnegative
        _ ≤ (1 - t) * ((25 / 16 : ℝ) *
            (‖closedMultiDerivative field (2, 0)
                ⟨base.val + t • (point.val - base.val),
                  openDiskMembershipClosed _ segmentInside⟩‖ +
              2 * ‖closedMultiDerivative field (1, 1)
                ⟨base.val + t • (point.val - base.val),
                  openDiskMembershipClosed _ segmentInside⟩‖ +
              ‖closedMultiDerivative field (0, 2)
                ⟨base.val + t • (point.val - base.val),
                  openDiskMembershipClosed _ segmentInside⟩‖)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right squareBound secondSumNonnegative)
            oneMinusNonnegative
        _ = (25 / 16 : ℝ) * (1 - t) *
            (‖closedMultiDerivative field (2, 0)
                ⟨base.val + t • (point.val - base.val),
                  openDiskMembershipClosed _ segmentInside⟩‖ +
              2 * ‖closedMultiDerivative field (1, 1)
                ⟨base.val + t • (point.val - base.val),
                  openDiskMembershipClosed _ segmentInside⟩‖ +
              ‖closedMultiDerivative field (0, 2)
                ⟨base.val + t • (point.val - base.val),
                  openDiskMembershipClosed _ segmentInside⟩‖) := by ring
    · exact ((continuous_const.mul (continuous_const.sub continuous_id)).mul
        ((continuous_diskSecondDerivativeNormSum field).comp
          (continuous_closedDiskSegment point base))).intervalIntegrable 0 1
  rw [taylorSimple]
  calc
    ‖field.value base +
        iteratedFDeriv ℝ 1 (closedDiskLift field.value) base.val
          (fun _ ↦ point.val - base.val) +
        ∫ t in 0..1, (1 - t) •
          iteratedFDeriv ℝ 2 (closedDiskLift field.value)
            (base.val + t • (point.val - base.val))
              (fun _ ↦ point.val - base.val)‖ ≤
      ‖field.value base‖ +
        ‖iteratedFDeriv ℝ 1 (closedDiskLift field.value) base.val
          (fun _ ↦ point.val - base.val)‖ +
        ‖∫ t in 0..1, (1 - t) •
          iteratedFDeriv ℝ 2 (closedDiskLift field.value)
            (base.val + t • (point.val - base.val))
              (fun _ ↦ point.val - base.val)‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add le_rfl firstFinal) remainderBound

def averagedSegmentSecondDerivativeNormSum {dimension : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk)
    (base : SpatialPlane) (t : ℝ) : ℝ :=
  diskSecondDerivativeNormSum field
    (closedDiskSegment point (ambientClosedDisk base) t)

theorem continuous_averagedSegmentSecondDerivativeNormSum {dimension : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk) :
    Continuous fun input : SpatialPlane × ℝ ↦
      averagedSegmentSecondDerivativeNormSum field point input.1 input.2 := by
  apply (continuous_diskSecondDerivativeNormSum field).comp
  apply Continuous.subtype_mk
  change Continuous fun input : SpatialPlane × ℝ ↦
    (ambientClosedDisk input.1).val + unitIntervalProjection input.2 •
      (point.val - (ambientClosedDisk input.1).val)
  have baseContinuous : Continuous fun input : SpatialPlane × ℝ ↦
      (ambientClosedDisk input.1).val :=
    continuous_subtype_val.comp (continuous_ambientClosedDisk.comp continuous_fst)
  exact baseContinuous.add
    ((continuous_unitIntervalProjection.comp continuous_snd).smul
      (continuous_const.sub baseContinuous))

theorem averagedSegmentSecondDerivativeNormSum_eq_affine {dimension : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk)
    (pointMembership : point.val ∈ openUnitDisk) (base : SpatialPlane)
    (baseMembership : base ∈ diskAverageSet) (t : ℝ) (tMembership : t ∈ Icc 0 1) :
    averagedSegmentSecondDerivativeNormSum field point base t =
      ∑ slot : Fin 4,
        ‖diskZeroExtension
          (closedMultiDerivative field (diskSecondMultiIndex slot))
          ((1 - t) • base + t • point.val)‖ := by
  have baseInsideOpen := diskAverageSet_subset_openUnitDisk baseMembership
  have baseInsideClosed := openDiskMembershipClosed base baseInsideOpen
  have segmentInside := openDisk_segment pointMembership baseInsideOpen tMembership
  have affineInside : (1 - t) • base + t • point.val ∈ openUnitDisk := by
    rw [show (1 - t) • base + t • point.val =
      base + t • (point.val - base) by module]
    exact segmentInside
  have segmentValue :
      (closedDiskSegment point (ambientClosedDisk base) t).val =
        (1 - t) • base + t • point.val := by
    simp only [closedDiskSegment, ambientClosedDisk_val_of_mem baseInsideClosed,
      unitIntervalProjection_eq tMembership]
    module
  unfold averagedSegmentSecondDerivativeNormSum diskSecondDerivativeNormSum
  apply Finset.sum_congr rfl
  intro slot _
  rw [diskZeroExtension_eq
    (closedMultiDerivative field (diskSecondMultiIndex slot)) affineInside]
  unfold closedDiskLift
  rw [dif_pos (openDiskMembershipClosed _ affineInside)]
  congr 2
  exact Subtype.ext segmentValue

def averagedSharpTaylorRemainderIntegrand {dimension : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk)
    (t : ℝ) (base : SpatialPlane) : ℝ :=
  (25 / 16 : ℝ) * (1 - t) *
    averagedSegmentSecondDerivativeNormSum field point base t

theorem continuous_averagedSharpTaylorRemainderIntegrand {dimension : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk) :
    Continuous fun input : ℝ × SpatialPlane ↦
      averagedSharpTaylorRemainderIntegrand field point input.1 input.2 := by
  have baseContinuous : Continuous fun input : ℝ × SpatialPlane ↦
      (ambientClosedDisk input.2).val :=
    continuous_subtype_val.comp (continuous_ambientClosedDisk.comp continuous_snd)
  have closedSegmentContinuous : Continuous fun input : ℝ × SpatialPlane ↦
      closedDiskSegment point (ambientClosedDisk input.2) input.1 := by
    apply Continuous.subtype_mk
    change Continuous fun input : ℝ × SpatialPlane ↦
      (ambientClosedDisk input.2).val + unitIntervalProjection input.1 •
        (point.val - (ambientClosedDisk input.2).val)
    exact baseContinuous.add
      ((continuous_unitIntervalProjection.comp continuous_fst).smul
        (continuous_const.sub baseContinuous))
  have segmentContinuous : Continuous fun input : ℝ × SpatialPlane ↦
      diskSecondDerivativeNormSum field
        (closedDiskSegment point (ambientClosedDisk input.2) input.1) :=
    (continuous_diskSecondDerivativeNormSum field).comp closedSegmentContinuous
  change Continuous fun input : ℝ × SpatialPlane ↦
    (25 / 16 : ℝ) * (1 - input.1) *
      diskSecondDerivativeNormSum field
        (closedDiskSegment point (ambientClosedDisk input.2) input.1)
  exact (continuous_const.mul (continuous_const.sub continuous_fst)).mul
    segmentContinuous

theorem averagedSharpTaylorRemainderIntegrableOn {dimension : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk) :
    IntegrableOn
      (Function.uncurry (averagedSharpTaylorRemainderIntegrand field point))
      (uIoc (0 : ℝ) 1 ×ˢ diskAverageSet) (volume.prod volume) := by
  have onCompact : IntegrableOn
      (Function.uncurry (averagedSharpTaylorRemainderIntegrand field point))
      (uIcc (0 : ℝ) 1 ×ˢ diskAverageSet) (volume.prod volume) :=
    (continuous_averagedSharpTaylorRemainderIntegrand field point).continuousOn.integrableOn_compact
      (isCompact_uIcc.prod (by
        unfold diskAverageSet
        exact isCompact_closedBall 0 (1 / 4 : ℝ)))
  exact onCompact.mono_set (Set.prod_mono uIoc_subset_uIcc Subset.rfl)

theorem averagedSharpTaylorRemainder_integral_swap {dimension : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk) :
    ∫ t in (0 : ℝ)..1,
        ∫ base : SpatialPlane in diskAverageSet,
          averagedSharpTaylorRemainderIntegrand field point t base =
      ∫ base : SpatialPlane in diskAverageSet,
        ∫ t in (0 : ℝ)..1,
          averagedSharpTaylorRemainderIntegrand field point t base := by
  have productIntegrable : Integrable
      (Function.uncurry (averagedSharpTaylorRemainderIntegrand field point))
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod
        (volume.restrict diskAverageSet)) := by
    rw [Measure.prod_restrict]
    exact averagedSharpTaylorRemainderIntegrableOn field point
  exact MeasureTheory.intervalIntegral_integral_swap productIntegrable

theorem averagedSharpTaylorRemainder_integrable_base {dimension : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk) :
    IntegrableOn
      (fun base : SpatialPlane ↦
        ∫ t in (0 : ℝ)..1,
          averagedSharpTaylorRemainderIntegrand field point t base)
      diskAverageSet volume := by
  have productIntegrable : Integrable
      (Function.uncurry (averagedSharpTaylorRemainderIntegrand field point))
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod
        (volume.restrict diskAverageSet)) := by
    rw [Measure.prod_restrict]
    exact averagedSharpTaylorRemainderIntegrableOn field point
  have fiberIntegrable := productIntegrable.integral_prod_right
  change Integrable
    (fun base : SpatialPlane ↦
      ∫ t in (0 : ℝ)..1,
        averagedSharpTaylorRemainderIntegrand field point t base)
    (volume.restrict diskAverageSet)
  convert fiberIntegrable using 1
  funext base
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  simp [Function.uncurry, uIoc_of_le]

theorem averagedSharpTaylorRemainder_inner_le {dimension : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk)
    (pointMembership : point.val ∈ openUnitDisk) (t : ℝ)
    (tMembership : t ∈ Icc (0 : ℝ) 1) :
    (∫ base : SpatialPlane in diskAverageSet,
      averagedSharpTaylorRemainderIntegrand field point t base) ≤
      (25 / 16 : ℝ) * Real.sqrt (Real.pi / 16) *
        diskSecondDerivativeL2NormSum field := by
  rcases lt_or_eq_of_le tMembership.2 with strictUpper | endpoint
  · have scalePositive : 0 < 1 - t := sub_pos.mpr strictUpper
    have averagedEquality :
        (∫ base : SpatialPlane in diskAverageSet,
          averagedSegmentSecondDerivativeNormSum field point base t) =
        ∫ base : SpatialPlane in diskAverageSet,
          ∑ slot : Fin 4,
            ‖diskZeroExtension
              (closedMultiDerivative field (diskSecondMultiIndex slot))
              ((1 - t) • base + t • point.val)‖ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_diskAverageSet] with
        base baseMembership
      exact averagedSegmentSecondDerivativeNormSum_eq_affine
        field point pointMembership base baseMembership t tMembership
    have affineBound := diskAverage_affine_secondDerivativeNormSum_le_volume field
      (1 - t) scalePositive (t • point.val)
    have averagedBound :
        (∫ base : SpatialPlane in diskAverageSet,
          averagedSegmentSecondDerivativeNormSum field point base t) ≤
        Real.sqrt (Real.pi / 16) * (1 - t)⁻¹ *
          diskSecondDerivativeL2NormSum field := by
      rw [averagedEquality]
      simpa only [add_comm] using affineBound
    have innerMul : (∫ base : SpatialPlane in diskAverageSet,
        averagedSharpTaylorRemainderIntegrand field point t base) =
        (25 / 16 : ℝ) * (1 - t) *
          ∫ base : SpatialPlane in diskAverageSet,
            averagedSegmentSecondDerivativeNormSum field point base t := by
      simp only [averagedSharpTaylorRemainderIntegrand]
      rw [MeasureTheory.integral_const_mul]
    rw [innerMul]
    calc
      (25 / 16 : ℝ) * (1 - t) *
          ∫ base : SpatialPlane in diskAverageSet,
            averagedSegmentSecondDerivativeNormSum field point base t ≤
        (25 / 16 : ℝ) * (1 - t) *
          (Real.sqrt (Real.pi / 16) * (1 - t)⁻¹ *
            diskSecondDerivativeL2NormSum field) := by
          exact mul_le_mul_of_nonneg_left averagedBound (by positivity)
      _ = (25 / 16 : ℝ) * Real.sqrt (Real.pi / 16) *
          diskSecondDerivativeL2NormSum field := by
        field_simp
  · subst t
    simp only [averagedSharpTaylorRemainderIntegrand, sub_self, mul_zero,
      zero_mul, MeasureTheory.integral_zero]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (diskSecondDerivativeL2NormSum_nonneg field)

theorem averagedSharpTaylorRemainder_after_averaging_le {dimension : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk)
    (pointMembership : point.val ∈ openUnitDisk) :
    ∫ t in (0 : ℝ)..1,
        ∫ base : SpatialPlane in diskAverageSet,
          averagedSharpTaylorRemainderIntegrand field point t base ≤
      (25 / 16 : ℝ) * Real.sqrt (Real.pi / 16) *
        diskSecondDerivativeL2NormSum field := by
  have productIntegrable : Integrable
      (Function.uncurry (averagedSharpTaylorRemainderIntegrand field point))
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod
        (volume.restrict diskAverageSet)) := by
    rw [Measure.prod_restrict]
    exact averagedSharpTaylorRemainderIntegrableOn field point
  have innerIntegrable : Integrable
      (fun t : ℝ ↦ ∫ base : SpatialPlane in diskAverageSet,
        averagedSharpTaylorRemainderIntegrand field point t base)
      (volume.restrict (uIoc (0 : ℝ) 1)) :=
    productIntegrable.integral_prod_left
  have constantIntegrable : Integrable
      (fun _ : ℝ ↦ (25 / 16 : ℝ) * Real.sqrt (Real.pi / 16) *
        diskSecondDerivativeL2NormSum field)
      (volume.restrict (uIoc (0 : ℝ) 1)) := by
    change IntegrableOn
      (fun _ : ℝ ↦ (25 / 16 : ℝ) * Real.sqrt (Real.pi / 16) *
        diskSecondDerivativeL2NormSum field) (uIoc (0 : ℝ) 1) volume
    exact (continuous_const.continuousOn.integrableOn_compact isCompact_uIcc).mono_set
      uIoc_subset_uIcc
  have pointwiseBound :
      (fun t : ℝ ↦ ∫ base : SpatialPlane in diskAverageSet,
        averagedSharpTaylorRemainderIntegrand field point t base) ≤ᵐ[
          volume.restrict (uIoc (0 : ℝ) 1)]
        (fun _ : ℝ ↦ (25 / 16 : ℝ) * Real.sqrt (Real.pi / 16) *
          diskSecondDerivativeL2NormSum field) := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t tMembership
    have orderedMembership : t ∈ Ioc (0 : ℝ) 1 := by
      simpa [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using tMembership
    exact averagedSharpTaylorRemainder_inner_le field point pointMembership t
      ⟨orderedMembership.1.le, orderedMembership.2⟩
  have setBound := integral_mono_ae innerIntegrable constantIntegrable pointwiseBound
  rw [show uIoc (0 : ℝ) 1 = Ioc 0 1 by simp] at setBound
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at setBound
  simpa using setBound

/-- The sharp Taylor estimate after averaging the base point over the fixed
radius-`1/4` disk.  The three terms remain separated until their respective
`L²` estimates are applied. -/
theorem closedJet_interior_averaged_bound {dimension : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk)
    (pointMembership : point.val ∈ openUnitDisk) :
    (Real.pi / 16) * ‖field.value point‖ ≤
      Real.sqrt (Real.pi / 16) * ‖closedDerivativeL2 (0, 0) field‖ +
      (5 / 4 : ℝ) * Real.sqrt (Real.pi / 16) *
        (‖closedDerivativeL2 (1, 0) field‖ +
          ‖closedDerivativeL2 (0, 1) field‖) +
      (25 / 16 : ℝ) * Real.sqrt (Real.pi / 16) *
        diskSecondDerivativeL2NormSum field := by
  have compactAverage : IsCompact diskAverageSet := by
    unfold diskAverageSet
    exact isCompact_closedBall 0 (1 / 4 : ℝ)
  have valueIntegrable : IntegrableOn
      (fun base : SpatialPlane ↦ ‖field.value (ambientClosedDisk base)‖)
      diskAverageSet volume :=
    ((field.value.continuous.comp continuous_ambientClosedDisk).norm.continuousOn.integrableOn_compact
      compactAverage)
  have firstXIntegrable : IntegrableOn
      (fun base : SpatialPlane ↦
        ‖closedMultiDerivative field (1, 0) (ambientClosedDisk base)‖)
      diskAverageSet volume :=
    (((closedMultiDerivative field (1, 0)).continuous.comp
      continuous_ambientClosedDisk).norm.continuousOn.integrableOn_compact
        compactAverage)
  have firstYIntegrable : IntegrableOn
      (fun base : SpatialPlane ↦
        ‖closedMultiDerivative field (0, 1) (ambientClosedDisk base)‖)
      diskAverageSet volume :=
    (((closedMultiDerivative field (0, 1)).continuous.comp
      continuous_ambientClosedDisk).norm.continuousOn.integrableOn_compact
        compactAverage)
  have remainderIntegrable :=
    averagedSharpTaylorRemainder_integrable_base field point
  have firstIntegrable : IntegrableOn
      (fun base : SpatialPlane ↦
        (5 / 4 : ℝ) *
          (‖closedMultiDerivative field (1, 0) (ambientClosedDisk base)‖ +
            ‖closedMultiDerivative field (0, 1) (ambientClosedDisk base)‖))
      diskAverageSet volume :=
    (firstXIntegrable.add firstYIntegrable).const_mul (5 / 4 : ℝ)
  have majorantIntegrable : IntegrableOn
      (fun base : SpatialPlane ↦
        ‖field.value (ambientClosedDisk base)‖ +
        (5 / 4 : ℝ) *
          (‖closedMultiDerivative field (1, 0) (ambientClosedDisk base)‖ +
            ‖closedMultiDerivative field (0, 1) (ambientClosedDisk base)‖) +
        ∫ t in (0 : ℝ)..1,
          averagedSharpTaylorRemainderIntegrand field point t base)
      diskAverageSet volume :=
    (valueIntegrable.add firstIntegrable).add remainderIntegrable
  have constantIntegrable : IntegrableOn
      (fun _ : SpatialPlane ↦ ‖field.value point‖)
      diskAverageSet volume :=
    continuous_const.continuousOn.integrableOn_compact compactAverage
  have pointwiseBound :
      (fun _ : SpatialPlane ↦ ‖field.value point‖) ≤ᵐ[volume.restrict diskAverageSet]
      (fun base : SpatialPlane ↦
        ‖field.value (ambientClosedDisk base)‖ +
        (5 / 4 : ℝ) *
          (‖closedMultiDerivative field (1, 0) (ambientClosedDisk base)‖ +
            ‖closedMultiDerivative field (0, 1) (ambientClosedDisk base)‖) +
        ∫ t in (0 : ℝ)..1,
          averagedSharpTaylorRemainderIntegrand field point t base) := by
    filter_upwards [ae_restrict_mem measurableSet_diskAverageSet] with
      base baseMembership
    have baseClosed := openDiskMembershipClosed base
      (diskAverageSet_subset_openUnitDisk baseMembership)
    have taylorBound := closedJet_taylorNormBound_sharp field point
      (ambientClosedDisk base) pointMembership
      (by simpa [ambientClosedDisk_val_of_mem baseClosed] using baseMembership)
    simpa only [averagedSharpTaylorRemainderIntegrand,
      averagedSegmentSecondDerivativeNormSum] using taylorBound
  have averagedBound := integral_mono_ae constantIntegrable majorantIntegrable
    pointwiseBound
  have valueBound := diskAverage_ambientClosedDisk_norm_le field.value
  have firstXBound := diskAverage_ambientClosedDisk_norm_le
    (closedMultiDerivative field (1, 0))
  have firstYBound := diskAverage_ambientClosedDisk_norm_le
    (closedMultiDerivative field (0, 1))
  have valueBound' :
      (∫ base : SpatialPlane in diskAverageSet,
          ‖field.value (ambientClosedDisk base)‖) ≤
        Real.sqrt (Real.pi / 16) *
          ‖closedDerivativeL2 (0, 0) field‖ := by
    simpa [closedDerivativeL2, closedMultiDerivative_zero field] using valueBound
  have firstXBound' :
      (∫ base : SpatialPlane in diskAverageSet,
          ‖closedMultiDerivative field (1, 0) (ambientClosedDisk base)‖) ≤
        Real.sqrt (Real.pi / 16) *
          ‖closedDerivativeL2 (1, 0) field‖ := by
    simpa [closedDerivativeL2] using firstXBound
  have firstYBound' :
      (∫ base : SpatialPlane in diskAverageSet,
          ‖closedMultiDerivative field (0, 1) (ambientClosedDisk base)‖) ≤
        Real.sqrt (Real.pi / 16) *
          ‖closedDerivativeL2 (0, 1) field‖ := by
    simpa [closedDerivativeL2] using firstYBound
  have remainderBound := averagedSharpTaylorRemainder_after_averaging_le
    field point pointMembership
  rw [averagedSharpTaylorRemainder_integral_swap] at remainderBound
  have outerSplit :
      (∫ base : SpatialPlane in diskAverageSet,
        ((‖field.value (ambientClosedDisk base)‖ +
          (5 / 4 : ℝ) *
            (‖closedMultiDerivative field (1, 0) (ambientClosedDisk base)‖ +
              ‖closedMultiDerivative field (0, 1) (ambientClosedDisk base)‖)) +
          (∫ t in (0 : ℝ)..1,
            averagedSharpTaylorRemainderIntegrand field point t base))) =
        (∫ base : SpatialPlane in diskAverageSet,
          (‖field.value (ambientClosedDisk base)‖ +
          (5 / 4 : ℝ) *
            (‖closedMultiDerivative field (1, 0) (ambientClosedDisk base)‖ +
              ‖closedMultiDerivative field (0, 1) (ambientClosedDisk base)‖))) +
        (∫ base : SpatialPlane in diskAverageSet,
          ∫ t in (0 : ℝ)..1,
            averagedSharpTaylorRemainderIntegrand field point t base) := by
    simpa only [Pi.add_apply] using
      (integral_add (valueIntegrable.add firstIntegrable) remainderIntegrable)
  have valueFirstSplit :
      (∫ base : SpatialPlane in diskAverageSet,
        (‖field.value (ambientClosedDisk base)‖ +
          (5 / 4 : ℝ) *
            (‖closedMultiDerivative field (1, 0) (ambientClosedDisk base)‖ +
              ‖closedMultiDerivative field (0, 1) (ambientClosedDisk base)‖))) =
        (∫ base : SpatialPlane in diskAverageSet,
          ‖field.value (ambientClosedDisk base)‖) +
        (∫ base : SpatialPlane in diskAverageSet,
          (5 / 4 : ℝ) *
            (‖closedMultiDerivative field (1, 0) (ambientClosedDisk base)‖ +
              ‖closedMultiDerivative field (0, 1) (ambientClosedDisk base)‖)) := by
    simpa only [Pi.add_apply] using integral_add valueIntegrable firstIntegrable
  have firstScalarSplit :
      (∫ base : SpatialPlane in diskAverageSet,
        (5 / 4 : ℝ) *
          (‖closedMultiDerivative field (1, 0) (ambientClosedDisk base)‖ +
            ‖closedMultiDerivative field (0, 1) (ambientClosedDisk base)‖)) =
        (5 / 4 : ℝ) *
          (∫ base : SpatialPlane in diskAverageSet,
            (‖closedMultiDerivative field (1, 0) (ambientClosedDisk base)‖ +
              ‖closedMultiDerivative field (0, 1) (ambientClosedDisk base)‖)) := by
    rw [MeasureTheory.integral_const_mul]
  have firstSumSplit :
      (∫ base : SpatialPlane in diskAverageSet,
        (‖closedMultiDerivative field (1, 0) (ambientClosedDisk base)‖ +
          ‖closedMultiDerivative field (0, 1) (ambientClosedDisk base)‖)) =
        (∫ base : SpatialPlane in diskAverageSet,
          ‖closedMultiDerivative field (1, 0) (ambientClosedDisk base)‖) +
        (∫ base : SpatialPlane in diskAverageSet,
          ‖closedMultiDerivative field (0, 1) (ambientClosedDisk base)‖) := by
    simpa only [Pi.add_apply] using integral_add firstXIntegrable firstYIntegrable
  have splitMajorant :
      (∫ base : SpatialPlane in diskAverageSet,
        (‖field.value (ambientClosedDisk base)‖ +
        (5 / 4 : ℝ) *
          (‖closedMultiDerivative field (1, 0) (ambientClosedDisk base)‖ +
            ‖closedMultiDerivative field (0, 1) (ambientClosedDisk base)‖) +
        ∫ t in (0 : ℝ)..1,
          averagedSharpTaylorRemainderIntegrand field point t base)) =
        (∫ base : SpatialPlane in diskAverageSet,
          ‖field.value (ambientClosedDisk base)‖) +
        (5 / 4 : ℝ) *
          ((∫ base : SpatialPlane in diskAverageSet,
              ‖closedMultiDerivative field (1, 0) (ambientClosedDisk base)‖) +
            (∫ base : SpatialPlane in diskAverageSet,
              ‖closedMultiDerivative field (0, 1) (ambientClosedDisk base)‖)) +
        (∫ base : SpatialPlane in diskAverageSet,
          ∫ t in (0 : ℝ)..1,
            averagedSharpTaylorRemainderIntegrand field point t base) := by
    rw [outerSplit, valueFirstSplit, firstScalarSplit, firstSumSplit]
  have firstBoundCombined :
      (5 / 4 : ℝ) *
          ((∫ base : SpatialPlane in diskAverageSet,
              ‖closedMultiDerivative field (1, 0) (ambientClosedDisk base)‖) +
            (∫ base : SpatialPlane in diskAverageSet,
              ‖closedMultiDerivative field (0, 1) (ambientClosedDisk base)‖)) ≤
        (5 / 4 : ℝ) * Real.sqrt (Real.pi / 16) *
          (‖closedDerivativeL2 (1, 0) field‖ +
            ‖closedDerivativeL2 (0, 1) field‖) := by
    calc
      _ ≤ (5 / 4 : ℝ) *
          (Real.sqrt (Real.pi / 16) * ‖closedDerivativeL2 (1, 0) field‖ +
            Real.sqrt (Real.pi / 16) * ‖closedDerivativeL2 (0, 1) field‖) :=
        mul_le_mul_of_nonneg_left (add_le_add firstXBound' firstYBound')
          (by norm_num)
      _ = _ := by ring
  calc
    (Real.pi / 16) * ‖field.value point‖ =
        ∫ _base : SpatialPlane in diskAverageSet, ‖field.value point‖ := by
      simp [volumeReal_diskAverageSet]
    _ ≤ ∫ base : SpatialPlane in diskAverageSet,
        (‖field.value (ambientClosedDisk base)‖ +
        (5 / 4 : ℝ) *
          (‖closedMultiDerivative field (1, 0) (ambientClosedDisk base)‖ +
            ‖closedMultiDerivative field (0, 1) (ambientClosedDisk base)‖) +
        ∫ t in (0 : ℝ)..1,
          averagedSharpTaylorRemainderIntegrand field point t base) := averagedBound
    _ = (∫ base : SpatialPlane in diskAverageSet,
          ‖field.value (ambientClosedDisk base)‖) +
        (5 / 4 : ℝ) *
          ((∫ base : SpatialPlane in diskAverageSet,
              ‖closedMultiDerivative field (1, 0) (ambientClosedDisk base)‖) +
            (∫ base : SpatialPlane in diskAverageSet,
              ‖closedMultiDerivative field (0, 1) (ambientClosedDisk base)‖)) +
        (∫ base : SpatialPlane in diskAverageSet,
          ∫ t in (0 : ℝ)..1,
            averagedSharpTaylorRemainderIntegrand field point t base) := splitMajorant
    _ ≤ _ := by
      exact add_le_add
        (add_le_add valueBound' firstBoundCombined)
        remainderBound

/-- The exact interior form of the six-derivative disk supremum estimate. -/
theorem closedJet_diskSup_bound_interior {dimension : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk)
    (pointMembership : point.val ∈ openUnitDisk) :
    ‖field.value point‖ ≤
      diskSupConstant * Real.sqrt (diskSupEnergy field) := by
  have averaged := closedJet_interior_averaged_bound field point pointMembership
  have grouped := sharpWeightedL2Sum_le_four field
  have areaBound :
      (Real.pi / 16) * ‖field.value point‖ ≤
        Real.sqrt Real.pi * diskDerivativeL2NormSum field := by
    have chained := averaged.trans grouped
    rw [sqrt_pi_div_sixteen] at chained
    nlinarith
  have rootPositive : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have rootSquare : (Real.sqrt Real.pi) ^ 2 = Real.pi :=
    Real.sq_sqrt Real.pi_nonneg
  have normalized :
      ‖field.value point‖ ≤
        (16 / Real.sqrt Real.pi) * diskDerivativeL2NormSum field := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ rootPositive).2
    have scaled : Real.pi * ‖field.value point‖ ≤
        16 * Real.sqrt Real.pi * diskDerivativeL2NormSum field := by
      nlinarith [areaBound]
    have cancelReady :
        Real.sqrt Real.pi * (‖field.value point‖ * Real.sqrt Real.pi) ≤
          Real.sqrt Real.pi * (16 * diskDerivativeL2NormSum field) := by
      calc
        Real.sqrt Real.pi * (‖field.value point‖ * Real.sqrt Real.pi) =
            (Real.sqrt Real.pi) ^ 2 * ‖field.value point‖ := by ring
        _ = Real.pi * ‖field.value point‖ := by rw [rootSquare]
        _ ≤ 16 * Real.sqrt Real.pi * diskDerivativeL2NormSum field := scaled
        _ = Real.sqrt Real.pi * (16 * diskDerivativeL2NormSum field) := by ring
    exact le_of_mul_le_mul_left cancelReady rootPositive
  have derivativeBound := diskDerivativeL2NormSum_le_sqrt_energy field
  calc
    ‖field.value point‖ ≤
        (16 / Real.sqrt Real.pi) * diskDerivativeL2NormSum field := normalized
    _ ≤ (16 / Real.sqrt Real.pi) *
        (Real.sqrt 6 * Real.sqrt (diskSupEnergy field)) :=
      mul_le_mul_of_nonneg_left derivativeBound (by positivity)
    _ = diskSupConstant * Real.sqrt (diskSupEnergy field) := by
      unfold diskSupConstant
      ring

/-- A08 / M4, including the boundary: every value of a closed jet is bounded
by the exact six-term derivative energy with constant
`16 * sqrt 6 / sqrt pi`. -/
theorem diskSup_bound {dimension : ℕ} (field : ClosedJet dimension)
    (point : ClosedDisk) :
    ‖field.value point‖ ≤
      diskSupConstant * Real.sqrt (diskSupEnergy field) := by
  let left : ClosedDisk → ℝ := fun diskPoint ↦ ‖field.value diskPoint‖
  let right : ClosedDisk → ℝ := fun _ ↦
    diskSupConstant * Real.sqrt (diskSupEnergy field)
  have onInterior : ∀ diskPoint ∈ Set.range openDiskInclusion,
      left diskPoint ≤ right diskPoint := by
    rintro _ ⟨interiorPoint, rfl⟩
    exact closedJet_diskSup_bound_interior field (openDiskInclusion interiorPoint)
      interiorPoint.property
  have leftContinuous : Continuous left := by
    exact field.value.continuous.norm
  have rightContinuous : Continuous right := continuous_const
  have closureMembership : point ∈ closure (Set.range openDiskInclusion) := by
    rw [openDisk_dense.closure_eq]
    exact Set.mem_univ point
  exact le_on_closure onInterior leftContinuous.continuousOn
    rightContinuous.continuousOn closureMembership

def averagedTaylorRemainderIntegrand {dimension : ℕ} (field : ClosedJet dimension)
    (point : ClosedDisk) (t : ℝ) (base : SpatialPlane) : ℝ :=
  (25 / 8 : ℝ) * (1 - t) *
    averagedSegmentDerivativeNormSum field point base t

theorem continuous_averagedTaylorRemainderIntegrand {dimension : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk) :
    Continuous fun input : ℝ × SpatialPlane ↦
      averagedTaylorRemainderIntegrand field point input.1 input.2 := by
  have baseContinuous : Continuous fun input : ℝ × SpatialPlane ↦
      (ambientClosedDisk input.2).val :=
    continuous_subtype_val.comp (continuous_ambientClosedDisk.comp continuous_snd)
  have closedSegmentContinuous : Continuous fun input : ℝ × SpatialPlane ↦
      closedDiskSegment point (ambientClosedDisk input.2) input.1 := by
    apply Continuous.subtype_mk
    change Continuous fun input : ℝ × SpatialPlane ↦
      (ambientClosedDisk input.2).val + unitIntervalProjection input.1 •
        (point.val - (ambientClosedDisk input.2).val)
    exact baseContinuous.add
      ((continuous_unitIntervalProjection.comp continuous_fst).smul
        (continuous_const.sub baseContinuous))
  have segmentContinuous : Continuous fun input : ℝ × SpatialPlane ↦
      diskDerivativeNormSum field
        (closedDiskSegment point (ambientClosedDisk input.2) input.1) :=
    (continuous_diskDerivativeNormSum field).comp closedSegmentContinuous
  change Continuous fun input : ℝ × SpatialPlane ↦
    (25 / 8 : ℝ) * (1 - input.1) *
      diskDerivativeNormSum field
        (closedDiskSegment point (ambientClosedDisk input.2) input.1)
  exact (continuous_const.mul (continuous_const.sub continuous_fst)).mul
    segmentContinuous

theorem averagedTaylorRemainderIntegrableOn {dimension : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk) :
    IntegrableOn
      (Function.uncurry (averagedTaylorRemainderIntegrand field point))
      (uIoc (0 : ℝ) 1 ×ˢ diskAverageSet) (volume.prod volume) := by
  have onCompact : IntegrableOn
      (Function.uncurry (averagedTaylorRemainderIntegrand field point))
      (uIcc (0 : ℝ) 1 ×ˢ diskAverageSet) (volume.prod volume) :=
    (continuous_averagedTaylorRemainderIntegrand field point).continuousOn.integrableOn_compact
      (isCompact_uIcc.prod (by
        unfold diskAverageSet
        exact isCompact_closedBall 0 (1 / 4 : ℝ)))
  exact onCompact.mono_set (Set.prod_mono uIoc_subset_uIcc Subset.rfl)

theorem averagedTaylorRemainder_integral_swap {dimension : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk) :
    ∫ t in (0 : ℝ)..1,
        ∫ base : SpatialPlane in diskAverageSet,
          averagedTaylorRemainderIntegrand field point t base =
      ∫ base : SpatialPlane in diskAverageSet,
        ∫ t in (0 : ℝ)..1,
          averagedTaylorRemainderIntegrand field point t base := by
  have productIntegrable : Integrable
      (Function.uncurry (averagedTaylorRemainderIntegrand field point))
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod
        (volume.restrict diskAverageSet)) := by
    rw [Measure.prod_restrict]
    exact averagedTaylorRemainderIntegrableOn field point
  exact MeasureTheory.intervalIntegral_integral_swap productIntegrable

theorem averagedTaylorRemainder_inner_le {dimension : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk)
    (pointMembership : point.val ∈ openUnitDisk) (t : ℝ)
    (tMembership : t ∈ Icc (0 : ℝ) 1) :
    (∫ base : SpatialPlane in diskAverageSet,
      averagedTaylorRemainderIntegrand field point t base) ≤
      (25 / 8 : ℝ) * Real.sqrt (Real.pi / 16) *
        diskDerivativeL2NormSum field := by
  rcases lt_or_eq_of_le tMembership.2 with strictUpper | endpoint
  · have scalePositive : 0 < 1 - t := sub_pos.mpr strictUpper
    have averagedEquality :
        (∫ base : SpatialPlane in diskAverageSet,
          averagedSegmentDerivativeNormSum field point base t) =
        ∫ base : SpatialPlane in diskAverageSet,
          ∑ slot : Fin 6,
            ‖diskZeroExtension
              (closedMultiDerivative field (diskSupMultiIndex slot))
              ((1 - t) • base + t • point.val)‖ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_diskAverageSet] with
        base baseMembership
      exact averagedSegmentDerivativeNormSum_eq_affine field point pointMembership
        base baseMembership t tMembership
    have affineBound := diskAverage_affine_derivativeNormSum_le_volume field
      (1 - t) scalePositive (t • point.val)
    have averagedBound :
        (∫ base : SpatialPlane in diskAverageSet,
          averagedSegmentDerivativeNormSum field point base t) ≤
        Real.sqrt (Real.pi / 16) * (1 - t)⁻¹ *
          diskDerivativeL2NormSum field := by
      rw [averagedEquality]
      simpa only [add_comm] using affineBound
    have innerMul : (∫ base : SpatialPlane in diskAverageSet,
        averagedTaylorRemainderIntegrand field point t base) =
        (25 / 8 : ℝ) * (1 - t) *
          ∫ base : SpatialPlane in diskAverageSet,
            averagedSegmentDerivativeNormSum field point base t := by
      simp only [averagedTaylorRemainderIntegrand]
      rw [MeasureTheory.integral_const_mul]
    rw [innerMul]
    calc
      (25 / 8 : ℝ) * (1 - t) *
          ∫ base : SpatialPlane in diskAverageSet,
            averagedSegmentDerivativeNormSum field point base t ≤
        (25 / 8 : ℝ) * (1 - t) *
          (Real.sqrt (Real.pi / 16) * (1 - t)⁻¹ *
            diskDerivativeL2NormSum field) := by
          exact mul_le_mul_of_nonneg_left averagedBound (by positivity)
      _ = (25 / 8 : ℝ) * Real.sqrt (Real.pi / 16) *
          diskDerivativeL2NormSum field := by
        field_simp
  · subst t
    simp only [averagedTaylorRemainderIntegrand, sub_self, mul_zero,
      zero_mul, MeasureTheory.integral_zero]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (diskDerivativeL2NormSum_nonneg field)

theorem averagedTaylorRemainder_after_averaging_le {dimension : ℕ}
    (field : ClosedJet dimension) (point : ClosedDisk)
    (pointMembership : point.val ∈ openUnitDisk) :
    ∫ t in (0 : ℝ)..1,
        ∫ base : SpatialPlane in diskAverageSet,
          averagedTaylorRemainderIntegrand field point t base ≤
      (25 / 8 : ℝ) * Real.sqrt (Real.pi / 16) *
        diskDerivativeL2NormSum field := by
  have productIntegrable : Integrable
      (Function.uncurry (averagedTaylorRemainderIntegrand field point))
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod
        (volume.restrict diskAverageSet)) := by
    rw [Measure.prod_restrict]
    exact averagedTaylorRemainderIntegrableOn field point
  have innerIntegrable : Integrable
      (fun t : ℝ ↦ ∫ base : SpatialPlane in diskAverageSet,
        averagedTaylorRemainderIntegrand field point t base)
      (volume.restrict (uIoc (0 : ℝ) 1)) :=
    productIntegrable.integral_prod_left
  have constantIntegrable : Integrable
      (fun _ : ℝ ↦ (25 / 8 : ℝ) * Real.sqrt (Real.pi / 16) *
        diskDerivativeL2NormSum field)
      (volume.restrict (uIoc (0 : ℝ) 1)) := by
    change IntegrableOn
      (fun _ : ℝ ↦ (25 / 8 : ℝ) * Real.sqrt (Real.pi / 16) *
        diskDerivativeL2NormSum field) (uIoc (0 : ℝ) 1) volume
    exact (continuous_const.continuousOn.integrableOn_compact isCompact_uIcc).mono_set
      uIoc_subset_uIcc
  have pointwiseBound :
      (fun t : ℝ ↦ ∫ base : SpatialPlane in diskAverageSet,
        averagedTaylorRemainderIntegrand field point t base) ≤ᵐ[
          volume.restrict (uIoc (0 : ℝ) 1)]
        (fun _ : ℝ ↦ (25 / 8 : ℝ) * Real.sqrt (Real.pi / 16) *
          diskDerivativeL2NormSum field) := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t tMembership
    have orderedMembership : t ∈ Ioc (0 : ℝ) 1 := by
      simpa [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using tMembership
    exact averagedTaylorRemainder_inner_le field point pointMembership t
      ⟨orderedMembership.1.le, orderedMembership.2⟩
  have setBound := integral_mono_ae innerIntegrable constantIntegrable pointwiseBound
  rw [show uIoc (0 : ℝ) 1 = Ioc 0 1 by simp] at setBound
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at setBound
  simpa using setBound

end Grad.CartesianState
