module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
public import Development.WeilBound.ThetaLifts.LatticeBasics.FdEqZero
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Prelims.SqShift
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
public import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.ThetaLifts.LatticeBasics.EulerA
/-! # MatrixCoefficientBoundedByValueAtOne: Preliminary helper declarations for global theta kernels. -/

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions UpperTheory.TP

namespace UpperTheory.MatrixCoefficientBound

open scoped Pointwise

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable Γ] {D : Set G}

private theorem coef_le (hfin : μ D < ⊤) (hD : IsFundamentalDomain Γ D μ) {φ : G → ℂ} (hc : Continuous φ)
    (hi : ∀ γ ∈ Γ, ∀ y, φ (γ * y) = φ y) {C : ℝ} (hC : ∀ y, ‖φ y‖ ≤ C) (g : G) :
    ‖∫ y in D, φ (y * g) * star (φ y) ∂μ‖ ≤ ∫ y in D, ‖φ y‖ ^ 2 ∂μ := by
  have hb : ∀ {ψ : G → ℂ}, Continuous ψ → (∀ y, ‖ψ y‖ ≤ C) → IntegrableOn (fun y => ‖ψ y‖ ^ 2) D μ := fun {ψ} h1 h2 =>
    Measure.integrableOn_of_bounded (M := C ^ 2) hfin.ne (h1.norm.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [norm_pow, norm_norm]; exact pow_le_pow_left₀ (norm_nonneg _) (h2 y) 2)
  have hcg : Continuous fun y => φ (y * g) := hc.comp (continuous_mul_const g)
  have i1 := hb hcg fun y => hC _
  have i2 := hb hc hC
  have e := _root_.UpperTheory.Reformulated.B.Qk59.sq_shift (μ := μ) hD (f := fun y => ‖φ y‖ ^ 2) (fun γ hγ y => by simp only [hi γ hγ y]) g
  calc ‖∫ y in D, φ (y * g) * star (φ y) ∂μ‖ ≤ ∫ y in D, ‖φ (y * g) * star (φ y)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y in D, (‖φ (y * g)‖ ^ 2 + ‖φ y‖ ^ 2) / 2 ∂μ := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _) ((i1.add i2).div_const 2) (Eventually.of_forall fun y => ?_)
      simp only [norm_mul, norm_star]
      nlinarith [sq_nonneg (‖φ (y * g)‖ - ‖φ y‖)]
    _ = ∫ y in D, ‖φ y‖ ^ 2 ∂μ := by
      rw [integral_div, integral_add i1 i2, e]
      ring

end UpperTheory.MatrixCoefficientBound

theorem UpperTheory.matrix_coefficient_bounded_by_value_at_one :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}, Cpt σ X.J → M.μ.IsHaarMeasure → IsFundamentalDomain (ratU σ X.J) M.dom M.μ → ∀ {φ : UA σ X.J → ℂ}, IsFn φ → φ ≠ 0 → ∃ r : ℝ, 0 < r ∧ mc M φ 1 = r ∧ ∀ g, ‖mc M φ g‖ ≤ r := by
  intro F E _ _ _ _ _ σ n d X W M hK hμ hD φ hφ h0
  haveI := hK.cnt
  haveI := hK.right M.μ hμ
  obtain ⟨C, hC⟩ := hK.bdd hφ.1 hφ.2
  have e1 : mc M φ 1 = ((∫ y in M.dom, ‖φ y‖ ^ 2 ∂M.μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp only [mc, pet, mul_one]
    exact integral_congr_ae (Eventually.of_forall fun y => by simpa using Complex.mul_conj' (φ y))
  have hp : (∫ y in M.dom, ‖φ y‖ ^ 2 ∂M.μ) ≠ 0 := fun h => h0 <| hK.eq_zero hμ hD hφ.1 hφ.2 (by
    have : pet M.μ M.dom φ φ = mc M φ 1 := by simp [mc]
    rw [this, e1, h]; simp)
  refine ⟨_, lt_of_le_of_ne (integral_nonneg fun y => by positivity) hp.symm, e1, fun g => ?_⟩
  exact UpperTheory.MatrixCoefficientBound.coef_le (hK.fin M.μ M.dom hμ hD) hD hφ.1 hφ.2 hC g
