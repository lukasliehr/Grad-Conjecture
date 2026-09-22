import ANL4FiniteNormalEnergy

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.CircularNormalLift
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.BoundaryLift Grad.CollarCartesian
open Grad.Constraints Grad.CircularHighWeak Grad.GaugeCoefficients.Algebra

/-- The AN22 kernel, with its actual radial factor and the accepted cutoff. -/
def normalKernel (mode : ℤ) (point : SpatialPlane) : ℂ :=
  ((‖point‖ - 1 : ℝ) : ℂ) * boundaryKernel (mode, 0) point

theorem normalKernel_zero_inner (mode : ℤ) (point : SpatialPlane)
    (inside : ‖point‖ ≤ (7 / 8 : ℝ)) : normalKernel mode point = 0 := by
  rw [normalKernel, boundaryKernel_zero_inner _ _ inside, mul_zero]

theorem normalKernel_smooth (mode : ℤ) : ContDiff ℝ ∞ (normalKernel mode) := by
  rw [contDiff_iff_contDiffAt]
  intro point
  by_cases isZero : point = 0
  · subst point
    apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [Metric.ball_mem_nhds (0 : SpatialPlane) (by norm_num : (0 : ℝ) < 7 / 8)] with source inside
    exact normalKernel_zero_inner mode source (by simpa only [Metric.mem_ball, dist_zero_right] using (Metric.mem_ball.mp inside).le)
  · have normSmooth : ContDiffAt ℝ ∞ (fun source : SpatialPlane => ‖source‖) point := contDiffAt_norm ℝ isZero
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp point (normSmooth.sub contDiffAt_const)).mul
      (boundaryKernel_smooth (mode, 0)).contDiffAt

theorem normalKernel_polar (mode : ℤ) (time : ℝ) (beforeAxis : time < 1) (angle : CellCircle) :
    normalKernel mode ((1 - time) • boundaryCirclePoint angle) =
      (normalProfile mode time : ℂ) * fourier mode angle := by
  rw [normalKernel, norm_smul, boundaryCirclePoint_norm, mul_one,
    Real.norm_of_nonneg (sub_pos.mpr beforeAxis).le, boundaryKernel_polar _ time beforeAxis]
  simp only [normalProfile, cutoffExponentialProfile, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_neg]
  ring

theorem normalKernel_boundary (mode : ℤ) (angle : CellCircle) :
    normalKernel mode (boundaryCirclePoint angle) = 0 := by
  rw [normalKernel, boundaryCirclePoint_norm, sub_self, Complex.ofReal_zero, zero_mul]

def finiteNormalField {dimension : ℕ} (modes : Finset ℤ)
    (values : ℤ → ComplexEuclidean dimension) (point : SpatialPlane) : ComplexEuclidean dimension :=
  ∑ mode ∈ modes, normalKernel mode point • values mode

theorem finiteNormalField_smooth {dimension : ℕ} (modes : Finset ℤ)
    (values : ℤ → ComplexEuclidean dimension) : ContDiff ℝ ∞ (finiteNormalField modes values) := by
  apply ContDiff.sum
  intro mode _
  exact (normalKernel_smooth mode).smul contDiff_const

theorem finiteNormalField_zero_inner {dimension : ℕ} (modes : Finset ℤ)
    (values : ℤ → ComplexEuclidean dimension) (point : SpatialPlane) (inside : ‖point‖ ≤ (7 / 8 : ℝ)) :
    finiteNormalField modes values point = 0 := by
  unfold finiteNormalField
  apply Finset.sum_eq_zero
  intro mode _
  rw [normalKernel_zero_inner _ _ inside, zero_smul]

theorem finiteNormalField_polar {dimension : ℕ} (modes : Finset ℤ)
    (values : ℤ → ComplexEuclidean dimension) (point : ℝ × ℝ) (beforeAxis : point.1 < 1) :
    finiteNormalField modes values (collarPlane point) =
      finiteProfileField modes (normalProfiles values) point := by
  simp only [finiteNormalField, finiteProfileField, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro mode _
  unfold profileMode normalProfiles
  rw [collarPlane_eq_scaled_boundary, normalKernel_polar mode point.1 beforeAxis, ← cellCharacter_coe]
  apply PiLp.ext
  intro coordinate
  simp only [PiLp.smul_apply, Complex.real_smul, smul_eq_mul]
  change (normalProfile mode point.1 : ℂ) * (fourier mode (point.2 : CellCircle)) * (values mode).ofLp coordinate =
    fourier mode (point.2 : CellCircle) * ((normalProfile mode point.1 : ℂ) * (values mode).ofLp coordinate)
  ring

def finiteNormalJet {dimension : ℕ} (modes : Finset ℤ)
    (values : ℤ → ComplexEuclidean dimension) : ClosedJet dimension :=
  globalClosedJet (finiteNormalField modes values) (finiteNormalField_smooth modes values)

theorem finiteNormalJet_boundary {dimension : ℕ} (modes : Finset ℤ)
    (values : ℤ → ComplexEuclidean dimension) (angle : CellCircle) :
    (finiteNormalJet modes values).value (boundaryDiskPoint angle) = 0 := by
  change ∑ mode ∈ modes, normalKernel mode (boundaryCirclePoint angle) • values mode = 0
  simp only [normalKernel_boundary, zero_smul, Finset.sum_const_zero]

def normalCartesianConstant (index : CartesianMultiIndex) : ℝ :=
  Classical.choose (arbitraryFiniteFamily_cartesian_consumer (fun _ => 1) contDiff_const index)

theorem normalCartesianConstant_nonnegative (index : CartesianMultiIndex) : 0 ≤ normalCartesianConstant index :=
  (Classical.choose_spec (arbitraryFiniteFamily_cartesian_consumer (fun _ => 1) contDiff_const index)).1

theorem finiteNormalJet_row {dimension : ℕ} (modes : Finset ℤ)
    (values : ℤ → ComplexEuclidean dimension) (grade : ℕ) (gradeBound : 2 ≤ grade)
    (index : CartesianMultiIndex) (orderBound : cartesianOrder index ≤ grade) :
    ‖closedDerivativeL2 index (finiteNormalJet modes values)‖ ^ 2 ≤
      (normalCartesianConstant index * normalFinitePolarConstant (cartesianOrder index)) *
        normalFiniteBoundaryEnergy grade modes values := by
  have comparison := (Classical.choose_spec
    (arbitraryFiniteFamily_cartesian_consumer (fun _ => 1) contDiff_const index)).2
      dimension modes (normalProfiles values) (normalProfiles_smooth values)
      (finiteNormalField modes values) (finiteNormalField_smooth modes values)
      (fun point inside => finiteNormalField_zero_inner modes values point (by linarith)) (by
        intro point inside
        have beforeAxis : point.1 < 1 := by have := inside.1.2; linarith
        have openRegion : IsOpen {source : ℝ × ℝ | source.1 < 1} := isOpen_lt continuous_fst continuous_const
        filter_upwards [openRegion.mem_nhds beforeAxis] with source sourceIn
        simpa only [Function.comp_apply, one_smul] using finiteNormalField_polar modes values source sourceIn)
  have scaled := mul_le_mul_of_nonneg_left
    (normalFiniteProfileEnergy_bound modes values grade (cartesianOrder index) gradeBound orderBound)
    (normalCartesianConstant_nonnegative index)
  exact (comparison.trans scaled).trans_eq (by ring)

def normalSobolevConstant (grade : ℕ) : ℝ :=
  ∑ index : DerivativeIndex grade, normalCartesianConstant (derivativeMultiIndex index) *
    normalFinitePolarConstant (cartesianOrder (derivativeMultiIndex index))

theorem normalSobolevConstant_nonnegative (grade : ℕ) : 0 ≤ normalSobolevConstant grade :=
  Finset.sum_nonneg (fun _index _ => mul_nonneg (normalCartesianConstant_nonnegative _)
    (normalFinitePolarConstant_nonnegative _))

/-- Original ordinary disk Sobolev norm, uniform in every finite mode set. -/
theorem finiteNormalJet_norm_sq (modes : Finset ℤ) (values : ℤ → ComplexEuclidean 1)
    (grade : ℕ) (gradeBound : 2 ≤ grade) :
    ‖unitDiskCoreInto grade (finiteNormalJet modes values)‖ ^ 2 ≤
      normalSobolevConstant grade * normalFiniteBoundaryEnergy grade modes values := by
  rw [unitDiskSobolev_norm_sq]
  simp only [unitDiskDerivative_core, normalSobolevConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro index _
  exact finiteNormalJet_row modes values grade gradeBound (derivativeMultiIndex index) (by
    exact index.property)

end Grad.CircularNormalLift
