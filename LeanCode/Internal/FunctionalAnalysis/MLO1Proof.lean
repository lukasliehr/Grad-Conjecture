import MLO1Interface
import MP1Independent

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers Grad.Mollifier.Pointwise
open scoped ContDiff Pointwise

universe valueUniverse

namespace Grad.Mollifier.Locality

theorem kernel_difference_mem (kernel : Spatial → ℝ) (epsilon : ℝ)
    (supported : KernelSupported kernel epsilon) (point source : Spatial)
    (nonzero : kernel (point - source) ≠ 0) : source ∈ Metric.closedBall point epsilon := by
  have bound := supported (subset_tsupport kernel nonzero)
  simpa only [Metric.mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero, norm_sub_rev] using bound

theorem kernel_zero_outside (kernel : Spatial → ℝ) (epsilon : ℝ)
    (supported : KernelSupported kernel epsilon) (carrier : Set Spatial) (point source : Spatial)
    (outside : point ∉ thickening carrier epsilon) (inside : source ∈ carrier) :
    kernel (point - source) = 0 := by
  by_contra nonzero
  apply outside
  exact Set.mem_add.mpr ⟨source, inside, point - source,
    supported (subset_tsupport kernel nonzero), by abel⟩

theorem thickening_compact (carrier : Set Spatial) (compactCarrier : IsCompact carrier)
    (epsilon : ℝ) : IsCompact (thickening carrier epsilon) :=
  compactCarrier.add (isCompact_closedBall (0 : Spatial) epsilon)

theorem support_result_mono {Value : Type valueUniverse} [NormedAddCommGroup Value]
    (function : Spatial → Value) (carrier larger : Set Spatial)
    (supported : SupportResult function carrier) (included : carrier ⊆ larger) :
    SupportResult function larger :=
  ⟨fun point outside => supported.1 point (fun inside => outside (included inside)),
    supported.2.1.trans included, supported.2.2⟩

theorem kernelSupportGoal : KernelSupportGoal := by
  intro kernel smoothness compactSupport epsilon supported rank word
  have derivative := kernelDerivativeGoal kernel smoothness compactSupport rank word
  exact ⟨derivative.1, derivative.2.1, derivative.2.2.1.trans supported⟩

variable (Value : Type valueUniverse) [NormedAddCommGroup Value]
  [InnerProductSpace ℂ Value]

theorem representative_zero (kernel : Spatial → ℝ) (epsilon : ℝ)
    (kernelSupport : KernelSupported kernel epsilon) (carrier : Set Spatial)
    (field : DomainL2 Value Set.univ) (fieldSupport : FieldSupported Value carrier field)
    (point : Spatial) (outside : point ∉ thickening carrier epsilon) :
    smoothRepresentative Value kernel field point = 0 := by
  change (∫ source : Spatial, kernel (point - source) • field source) = 0
  apply integral_eq_zero_of_ae
  filter_upwards [fieldSupport] with source zeroOutside
  change kernel (point - source) • field source = 0
  by_cases inside : source ∈ carrier
  · simp only [kernel_zero_outside kernel epsilon kernelSupport carrier point source outside inside, zero_smul]
  · simp only [zeroOutside inside, smul_zero]

theorem representative_support (kernel : Spatial → ℝ) (epsilon : ℝ)
    (kernelSupport : KernelSupported kernel epsilon) (carrier : Set Spatial)
    (compactCarrier : IsCompact carrier) (field : DomainL2 Value Set.univ)
    (fieldSupport : FieldSupported Value carrier field) :
    SupportResult (smoothRepresentative Value kernel field) (thickening carrier epsilon) := by
  have vanishes := representative_zero Value kernel epsilon kernelSupport carrier field fieldSupport
  have contained : Function.support (smoothRepresentative Value kernel field) ⊆ thickening carrier epsilon := by
    intro point nonzero
    by_contra outside
    exact nonzero (vanishes point outside)
  have compactThickening := thickening_compact carrier compactCarrier epsilon
  exact ⟨vanishes, closure_minimal contained compactThickening.isClosed,
    HasCompactSupport.of_support_subset_isCompact compactThickening contained⟩

theorem actual_derivative_eq [CompleteSpace Value] (kernel : Spatial → ℝ) (smoothness : ContDiff ℝ ∞ kernel)
    (compactSupport : HasCompactSupport kernel) (field : DomainL2 Value Set.univ)
    (rank : ℕ) (word : Word rank) :
    orderedDerivative rank word (smoothRepresentative Value kernel field) =
      smoothRepresentative Value (orderedDerivative rank word kernel) field := by
  funext point
  exact ((pointwiseGoal Value kernel smoothness compactSupport field).2.2 rank word point).2

theorem supportGoal : SupportGoal.{valueUniverse} := by
  intro Value normed inner complete kernel smoothness compactSupport epsilon kernelSupport carrier compactCarrier field fieldSupport
  refine ⟨representative_support Value kernel epsilon kernelSupport carrier compactCarrier field fieldSupport, ?_⟩
  intro rank word
  have derivativeSupport := (orderedDerivative_support rank word kernel).trans kernelSupport
  have supported := representative_support Value _ epsilon derivativeSupport carrier compactCarrier field fieldSupport
  have equality := actual_derivative_eq Value kernel smoothness compactSupport field rank word
  exact ⟨supported, equality.symm ▸ supported, equality⟩

theorem representative_agreement (kernel : Spatial → ℝ) (epsilon : ℝ)
    (kernelSupport : KernelSupported kernel epsilon) (domain : Set Spatial) (openDomain : IsOpen domain)
    (first second : DomainL2 Value Set.univ) (agreement : FieldsAgree Value domain first second)
    (point : Spatial) (safe : point ∈ safeRegion domain epsilon) :
    smoothRepresentative Value kernel first point = smoothRepresentative Value kernel second point := by
  have insideAgreement : ∀ᵐ source ∂volume, source ∈ domain → first source = second source :=
    (ae_restrict_iff' openDomain.measurableSet).mp agreement
  change (∫ source : Spatial, kernel (point - source) • first source) =
    ∫ source : Spatial, kernel (point - source) • second source
  apply integral_congr_ae
  filter_upwards [insideAgreement] with source sameInside
  by_cases zeroKernel : kernel (point - source) = 0
  · simp only [zeroKernel, zero_smul]
  · rw [sameInside (safe (kernel_difference_mem kernel epsilon kernelSupport point source zeroKernel))]

theorem agreementGoal : AgreementGoal.{valueUniverse} := by
  intro Value normed inner complete kernel smoothness compactSupport epsilon kernelSupport domain openDomain first second agreement point safe
  refine ⟨representative_agreement Value kernel epsilon kernelSupport domain openDomain first second agreement point safe, ?_⟩
  intro rank word
  have derivativeSupport := (orderedDerivative_support rank word kernel).trans kernelSupport
  have same := representative_agreement Value _ epsilon derivativeSupport domain openDomain first second agreement point safe
  refine ⟨?_, same⟩
  rw [actual_derivative_eq Value kernel smoothness compactSupport first rank word,
    actual_derivative_eq Value kernel smoothness compactSupport second rank word]
  exact same

theorem scaled_kernel_supported (epsilon : ℝ) (positive : 0 < epsilon) :
    KernelSupported (scaledEta epsilon) epsilon := by
  rw [KernelSupported, scaledEta_tsupport epsilon positive]

theorem scaledGoal : ScaledGoal.{valueUniverse} := by
  intro Value normed inner complete epsilon positive
  exact ⟨supportGoal Value _ (scaledEta_contDiff epsilon) (scaledEta_compactSupport epsilon positive)
      epsilon (scaled_kernel_supported epsilon positive),
    agreementGoal Value _ (scaledEta_contDiff epsilon) (scaledEta_compactSupport epsilon positive)
      epsilon (scaled_kernel_supported epsilon positive)⟩

theorem thickening_disk_subset (center : Spatial) (innerRadius outerRadius epsilon : ℝ)
    (margin : innerRadius + epsilon < outerRadius) :
    thickening (Metric.closedBall center innerRadius) epsilon ⊆ Metric.ball center outerRadius := by
  intro point member
  rcases Set.mem_add.mp member with ⟨source, sourceBound, offset, offsetBound, rfl⟩
  apply Metric.mem_ball.mpr
  calc
    dist (source + offset) center = ‖(source - center) + offset‖ := by
      rw [dist_eq_norm]
      congr 1
      abel
    _ ≤ ‖source - center‖ + ‖offset‖ := norm_add_le _ _
    _ ≤ innerRadius + epsilon := add_le_add
      (by simpa only [Metric.mem_closedBall, dist_eq_norm] using sourceBound)
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using offsetBound)
    _ < outerRadius := margin

theorem disk_subset_safeRegion (center : Spatial) (innerRadius outerRadius epsilon : ℝ)
    (margin : innerRadius + epsilon < outerRadius) :
    Metric.closedBall center innerRadius ⊆ safeRegion (Metric.ball center outerRadius) epsilon := by
  intro point inside
  apply Metric.closedBall_subset_ball'
  have bound : dist point center ≤ innerRadius := inside
  linarith

theorem diskGoal : DiskGoal.{valueUniverse} := by
  intro Value normed inner complete kernel smoothness compactSupport epsilon _nonnegativeEpsilon kernelSupport center innerRadius outerRadius _nonnegativeInner margin
  have included := thickening_disk_subset center innerRadius outerRadius epsilon margin
  have safe := disk_subset_safeRegion center innerRadius outerRadius epsilon margin
  refine ⟨included, safe, ?_, ?_⟩
  · intro field fieldSupport
    have supported := supportGoal Value kernel smoothness compactSupport epsilon kernelSupport
      (Metric.closedBall center innerRadius) (isCompact_closedBall center innerRadius) field fieldSupport
    refine ⟨support_result_mono _ _ _ supported.1 included, ?_⟩
    intro rank word
    exact ⟨support_result_mono _ _ _ (supported.2 rank word).2.1 included,
      support_result_mono _ _ _ (supported.2 rank word).1 included⟩
  · intro first second agreement point inside
    exact agreementGoal Value kernel smoothness compactSupport epsilon kernelSupport
      (Metric.ball center outerRadius) Metric.isOpen_ball first second agreement point (safe inside)

theorem canonicalGoal : CanonicalGoal := by
  intro dimension epsilon positive
  refine ⟨scaledGoal (CellValues dimension) epsilon positive, ?_⟩
  intro center innerRadius outerRadius nonnegativeInner margin
  exact diskGoal (CellValues dimension) _ (scaledEta_contDiff epsilon)
    (scaledEta_compactSupport epsilon positive) epsilon positive.le (scaled_kernel_supported epsilon positive)
    center innerRadius outerRadius nonnegativeInner margin

theorem coordinateGoal : CoordinateGoal := by
  intro dimension epsilon positive domain openDomain first second agreement point safe cell physical
  have same := (scaledGoal (CellValues dimension) epsilon positive).2 domain openDomain first second agreement point safe
  refine ⟨congrArg (fun value : CellValues dimension => value cell physical) same.1, ?_⟩
  intro rank word
  exact congrArg (fun value : CellValues dimension => value cell physical) (same.2 rank word).1

theorem zeroGoal : ZeroGoal.{valueUniverse} := by
  refine ⟨fun epsilon positive => scaledGoal (CellValues 0) epsilon positive, ?_⟩
  intro Value normed inner complete kernel field word
  exact orderedDerivative_zero word _

theorem blockGoal : BlockGoal.{valueUniverse} :=
  ⟨kernelSupportGoal, supportGoal, agreementGoal, scaledGoal, diskGoal, canonicalGoal, coordinateGoal, zeroGoal⟩

end Grad.Mollifier.Locality
