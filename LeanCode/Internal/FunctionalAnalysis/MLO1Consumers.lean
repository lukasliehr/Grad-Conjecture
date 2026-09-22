import MLO1Proof

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers Grad.Mollifier.Pointwise
open scoped ContDiff Pointwise

universe valueUniverse

namespace Grad.Mollifier.Locality.Consumer

theorem fullBlock : BlockGoal.{valueUniverse} := blockGoal

theorem smoothCompactField (dimension : ℕ) (epsilon : ℝ) (positive : 0 < epsilon)
    (carrier : Set Spatial) (compactCarrier : IsCompact carrier) (field : FieldL2 dimension Set.univ)
    (supported : FieldSupported (CellValues dimension) carrier field) :
    ContDiff ℝ ∞ (smoothRepresentative (CellValues dimension) (scaledEta epsilon) field) ∧
      SupportSpecification (CellValues dimension) carrier epsilon (scaledEta epsilon) field :=
  ⟨(pointwiseGoal (CellValues dimension) _ (scaledEta_contDiff epsilon)
      (scaledEta_compactSupport epsilon positive) field).2.1,
    (scaledGoal (CellValues dimension) epsilon positive).1 carrier compactCarrier field supported⟩

theorem compactFieldCoordinates (dimension : ℕ) (epsilon : ℝ) (positive : 0 < epsilon)
    (carrier : Set Spatial) (compactCarrier : IsCompact carrier) (field : FieldL2 dimension Set.univ)
    (supported : FieldSupported (CellValues dimension) carrier field) :
    ∀ point ∉ carrier + Metric.closedBall (0 : Spatial) epsilon,
      ∀ (cell : ℤ) (physical : Fin dimension),
        smoothRepresentative (CellValues dimension) (scaledEta epsilon) field point cell physical = 0 ∧
        ∀ (rank : ℕ) (word : Fin rank → Fin 2),
          (iteratedFDeriv ℝ rank (smoothRepresentative (CellValues dimension) (scaledEta epsilon) field)
            point (fun position => spatialDirection (word position))) cell physical = 0 := by
  intro point outside cell physical
  have support := (smoothCompactField dimension epsilon positive carrier compactCarrier field supported).2
  constructor
  · exact congrArg (fun value : CellValues dimension => value cell physical) (support.1.1 point outside)
  · intro rank word
    exact congrArg (fun value : CellValues dimension => value cell physical)
      ((support.2 rank word).2.1.1 point outside)

theorem rawLocalAgreement (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] [CompleteSpace Value] (kernel : Spatial → ℝ) (epsilon : ℝ)
    (kernelSupport : tsupport kernel ⊆ Metric.closedBall (0 : Spatial) epsilon)
    (domain : Set Spatial) (openDomain : IsOpen domain) (first second : DomainL2 Value Set.univ)
    (agreement : first =ᵐ[volume.restrict domain] second) (point : Spatial)
    (contained : Metric.closedBall point epsilon ⊆ domain) :
    (∫ source : Spatial, kernel (point - source) • first source) =
      ∫ source : Spatial, kernel (point - source) • second source :=
  representative_agreement Value kernel epsilon kernelSupport domain openDomain first second agreement point contained

theorem allOrderedLocalAgreement (dimension : ℕ) (epsilon : ℝ) (positive : 0 < epsilon)
    (domain : Set Spatial) (openDomain : IsOpen domain) (first second : FieldL2 dimension Set.univ)
    (agreement : first =ᵐ[volume.restrict domain] second) (point : Spatial)
    (contained : Metric.closedBall point epsilon ⊆ domain)
    (rank : ℕ) (word : Fin rank → Fin 2) (cell : ℤ) (physical : Fin dimension) :
    (iteratedFDeriv ℝ rank (smoothRepresentative (CellValues dimension) (scaledEta epsilon) first)
      point (fun position => spatialDirection (word position))) cell physical =
    (iteratedFDeriv ℝ rank (smoothRepresentative (CellValues dimension) (scaledEta epsilon) second)
      point (fun position => spatialDirection (word position))) cell physical :=
  (coordinateGoal dimension epsilon positive domain openDomain first second agreement point contained cell physical).2 rank word

theorem centeredDisk (dimension : ℕ) (epsilon : ℝ) (positive : 0 < epsilon)
    (innerRadius outerRadius : ℝ) (nonnegativeInner : 0 ≤ innerRadius)
    (margin : innerRadius + epsilon < outerRadius) :
    DiskSpecification (CellValues dimension) (0 : Spatial) innerRadius outerRadius epsilon (scaledEta epsilon) :=
  (canonicalGoal dimension epsilon positive).2 0 innerRadius outerRadius nonnegativeInner margin

theorem strictDiskSupport (dimension : ℕ) (epsilon : ℝ) (positive : 0 < epsilon)
    (innerRadius outerRadius : ℝ) (nonnegativeInner : 0 ≤ innerRadius)
    (margin : innerRadius + epsilon < outerRadius) (field : FieldL2 dimension Set.univ)
    (supported : ∀ᵐ point ∂volume, point ∉ Metric.closedBall (0 : Spatial) innerRadius → field point = 0) :
    tsupport (smoothRepresentative (CellValues dimension) (scaledEta epsilon) field) ⊆
        Metric.ball (0 : Spatial) outerRadius ∧
      ∀ (rank : ℕ) (word : Fin rank → Fin 2),
        tsupport (orderedDerivative rank word
          (smoothRepresentative (CellValues dimension) (scaledEta epsilon) field)) ⊆
          Metric.ball (0 : Spatial) outerRadius := by
  have support := (centeredDisk dimension epsilon positive innerRadius outerRadius nonnegativeInner margin).2.2.1 field supported
  exact ⟨support.1.2.1, fun rank word => (support.2 rank word).1.2.1⟩

theorem zeroDimension (epsilon : ℝ) (positive : 0 < epsilon) :
    ScaledSpecification (CellValues 0) epsilon ∧
      ∀ (center : Spatial) (innerRadius outerRadius : ℝ), 0 ≤ innerRadius →
        innerRadius + epsilon < outerRadius →
          DiskSpecification (CellValues 0) center innerRadius outerRadius epsilon (scaledEta epsilon) :=
  canonicalGoal 0 epsilon positive

theorem zeroRank (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] [CompleteSpace Value] (kernel : Spatial → ℝ)
    (field : DomainL2 Value Set.univ) (word : Fin 0 → Fin 2) :
    orderedDerivative 0 word (smoothRepresentative Value kernel field) = smoothRepresentative Value kernel field :=
  zeroGoal.2 Value kernel field word

end Grad.Mollifier.Locality.Consumer
