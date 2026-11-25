module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Formalism.PeriodIntegrals.DSInfCharCap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CayleyTransport

section Smooth

open scoped Matrix.Norms.Elementwise

theorem smoothOn_comp {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {H J A B : Matrix (Fin n) (Fin n) ℂ} (hAB : ∀ g, gᴴ * J * g = J → (A * g * B)ᴴ * H * (A * g * B) = H)
    {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : PI.UpqRep.SmoothOnH H f) :
    PI.PhMeasCore.SmoothOnH J (fun g => f (A * g * B)) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hm, hF, he⟩ := hf (A * g₀ * B) (hAB g₀ hg₀)
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun g => A * g * B
      map_add' := fun x y => by simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c x => by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  let L' := LinearMap.toContinuousLinearMap L
  refine ⟨L' ⁻¹' U, F ∘ L', hU.preimage L'.continuous, hm, ?_, ?_⟩
  · exact hF.comp L'.contDiff.contDiffOn (fun x hx => hx)
  · intro g hg hgJ
    exact he (A * g * B) hg (hAB g hgJ)

end Smooth

theorem dsig_conj {k r : ℕ} (R : Rep k r) {Q : Mx k r} (hQ : IsUnit Q) (X : Mx k r) (v : R.H) :
    PI.PhMeasCore.dsig (fun g => R.σ (Q⁻¹ * g * Q)) X v =
      PI.UpqRep.dsig (k := k) (r := r) R.σ (Q⁻¹ * X * Q) v := by
  unfold PI.PhMeasCore.dsig PI.UpqRep.dsig
  congr 1
  funext t
  have : (t : ℂ) • (Q⁻¹ * X * Q) = Q⁻¹ * ((t : ℂ) • X) * Q := by
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [this, Matrix.exp_conj' Q _ hQ]

theorem smooth_and_dsigC_transport : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (R : Rep k r) (Q : Mx k r), PI.UpqRep.IsCayleyU k r ε Q → (∀ v ∈ R.sm, v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) (fun g => R.σ (Q⁻¹ * g * Q))) ∧ ∀ Y v, PI.DSInfCharCap.dsigC ε (fun g => R.σ (Q⁻¹ * g * Q)) Y v = R.dC (Q⁻¹ * Y * Q) v := by
  intro k r ε R Q ⟨⟨hunit, hcay⟩, hU⟩
  have h1 : Q * Qᴴ = 1 := (Matrix.mem_unitaryGroup_iff).mp hU
  have h2 : Qᴴ * Q = 1 := (Matrix.mem_unitaryGroup_iff').mp hU
  have hinv : Q⁻¹ = Qᴴ := Matrix.inv_eq_left_inv h2
  have hH : Formalism.QuantumDeterminants.Hpk k r = Qᴴ * Formalism.REAL.Jm ε * Q := hcay.symm
  have hc : ∀ Z : Mx k r, Q * (Qᴴ * Z) = Z := fun Z => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  constructor
  · intro v hv
    refine smoothOn_comp (H := PI.UpqRep.Hpk k r) (f := fun g => R.σ g v) ?_ hv
    intro g hg
    rw [← hcay, hinv]
    have hg' : gᴴ * PI.UpqRep.Jm ε * g = PI.UpqRep.Jm ε := hg
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, hc]
    simp only [Matrix.mul_assoc] at hg'
    rw [← Matrix.mul_assoc (PI.UpqRep.Jm ε) g Q, ← Matrix.mul_assoc gᴴ _ Q, hg']
  · intro Y v
    have ht : Q⁻¹ * PI.DSInfCharCap.thetaJ ε Y * Q =
        -(Formalism.QuantumDeterminants.Hpk k r * (Q⁻¹ * Y * Q)ᴴ * Formalism.QuantumDeterminants.Hpk k r) := by
      rw [hH, hinv, PI.DSInfCharCap.thetaJ]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, hc,
        Matrix.mul_neg, Matrix.neg_mul]
    unfold PI.DSInfCharCap.dsigC Rep.dC
    rw [dsig_conj R hunit, dsig_conj R hunit, ← ht]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]

end GlobalTheory.CayleyTransport
