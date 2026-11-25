module

public import GroundTheory.AutomorphicForms.GL2.AdelicFourier2TensorCosetIndicatorAlgebraMap
public import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform
public import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
import GroundTheory.GlobalFields.TateThesis.AdelePoisson
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatUniformSummableMajorant, Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SummableProdCoord, Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSummableMajorantLatticeSum

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatUniformSummableMajorant =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatUniformSummableMajorant", "h": "module\n\npublic import GroundTheory.AutomorphicForms.GL2.AdelicFourier2TensorCosetIndicatorAlgebraMap\nimport GroundTheory.GlobalFields.TateThesis.AdelePoisson\npublic import GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform\npublic import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.EisRk1Bound

open NumberField NumberField.mixedEmbedding IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical nonZeroDivisors Pointwise
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2

set_option synthInstance.maxSize 1000

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem continuous_infRingHom : Continuous (infRingHom (K := K)) := by
  exact (GroundTheory.Global.homeomorphMixedSpace K).continuous.comp continuous_fst

theorem continuous_finRingHom : Continuous (finRingHom (K := K)) := by
  exact continuous_snd

def latticeWeight (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (k : ℕ) (x : K) : ℝ :=
  if x ∈ (J : FractionalIdeal (𝓞 K)⁰ K) then ((1 + ‖mixedEmbedding K x‖) ^ k)⁻¹ else 0

theorem latticeWeight_nonneg (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (k : ℕ) (x : K) :
    0 ≤ latticeWeight J k x := by
  unfold latticeWeight
  split_ifs <;> positivity

end

end GlobalTheory.CompanionTheory.EisRk1Bound
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatUniformSummableMajorant =====

-- ===== clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SummableProdCoord =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SummableProdCoord", "h": "module\n\npublic import Mathlib.Topology.Algebra.InfiniteSum.Defs\npublic import Mathlib.Topology.MetricSpace.Pseudo.Defs\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Lemma\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.Algebra.BigOperators.Ring.Finset\npublic import Mathlib.Algebra.Order.BigOperators.Group.Finset\npublic import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset\npublic import Mathlib.Topology.Algebra.InfiniteSum.Order\npublic import Mathlib.Topology.Algebra.InfiniteSum.Real\n\n"}
section -- clump:auto
@[expose] public section

private lemma sum_prod_le {ι : Type*} [Fintype ι] [DecidableEq ι] {α : Type*} {g : α → ℝ}
    (hg : ∀ x, 0 ≤ g x) (hs : Summable g) (s : Finset (ι → α)) :
    ∑ ξ ∈ s, ∏ i, g (ξ i) ≤ ∏ _i : ι, ∑' x, g x := by
  haveI : DecidableEq α := Classical.decEq α
  let t : ι → Finset α := fun i => s.image fun η : ι → α => η i
  have hsub : s ⊆ Fintype.piFinset t := by
    intro ξ hξ
    rw [Fintype.mem_piFinset]
    intro i
    exact Finset.mem_image.2 ⟨ξ, hξ, rfl⟩
  have h1 : ∑ ξ ∈ s, ∏ i, g (ξ i) ≤ ∑ ξ ∈ Fintype.piFinset t, ∏ i, g (ξ i) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun ξ _ _ => Finset.prod_nonneg fun i _ => hg (ξ i)
  have h2 : ∏ i, ∑ x ∈ t i, g x = ∑ ξ ∈ Fintype.piFinset t, ∏ i, g (ξ i) :=
    Finset.prod_univ_sum t fun _ x => g x
  have h3 : ∏ i, ∑ x ∈ t i, g x ≤ ∏ _i : ι, ∑' x, g x := by
    apply Finset.prod_le_prod₀
    · intro i _
      exact Finset.sum_nonneg fun x _ => hg x
    · intro i _
      exact hs.sum_le_tsum (t i) fun x _ => hg x
  exact h1.trans (h2.symm.le.trans h3)

theorem UpperTheory.Reformulated.B.Qo1.summable_prod_coord.{u_2, u_3} :
    ∀ {ι : Type u_2} [inst : Fintype ι] [DecidableEq ι] {α : Type u_3} {g : α → ℝ},
    (∀ (x : α), (0 : ℝ) ≤ g x) → Summable g → Summable fun (ξ : ι → α) ↦ ∏ i : ι, g (ξ i) := by
  intro ι _ _ α g hg hs
  have h0 : ∀ ξ : ι → α, 0 ≤ ∏ i, g (ξ i) := fun ξ => Finset.prod_nonneg fun i _ => hg (ξ i)
  exact summable_of_sum_le h0 (sum_prod_le hg hs)
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SummableProdCoord =====

-- ===== clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSummableMajorantLatticeSum =====
-- clump-header: {"m": "Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSummableMajorantLatticeSum", "h": "module\n\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatUniformSummableMajorant\npublic import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont\npublic import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SummableProdCoord\nimport GroundTheory.GlobalFields.TateThesis.AdelePoisson\nimport GroundTheory.GlobalFields.TateThesis.AdelePoissonUniform\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.EisRkNBound

open NumberField NumberField.mixedEmbedding IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap Classical nonZeroDivisors Pointwise
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix GlobalTheory.CompanionTheory.EisRk1Bound

set_option synthInstance.maxSize 1000

noncomputable section

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem inv_mulVec_mulVec (x : ι → 𝔸[K]) (h : GL ι 𝔸[K]) :
    ((h⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]) *ᵥ ((h : Matrix ι ι 𝔸[K]) *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem continuous_inv_entry (i j : ι) :
    Continuous fun h : GL ι 𝔸[K] ↦ ((h⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]) i j := by
  have h : Continuous fun h : GL ι 𝔸[K] ↦ ((h⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]) :=
    Units.continuous_val.comp continuous_inv
  exact h.matrix_elem i j


omit [DecidableEq ι] in
theorem finPartPi_mulVec (M : Matrix ι ι 𝔸[K]) (x : ι → 𝔸[K]) :
    finPartPi (M *ᵥ x) = M.map Adele2.finRingHom *ᵥ finPartPi x := by
  funext i
  show Adele2.finRingHom (∑ j, M i j * x j) = _

  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ map_mul _ _ _


omit [DecidableEq ι] in
theorem infPartPi_mulVec (M : Matrix ι ι 𝔸[K]) (x : ι → 𝔸[K]) :
    infPartPi (M *ᵥ x) = M.map Adele2.infRingHom *ᵥ infPartPi x := by
  funext i
  show Adele2.infRingHom (∑ j, M i j * x j) = _

  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ ↦ map_mul _ _ _


omit [DecidableEq ι] in
theorem norm_mulVec_le (M : Matrix ι ι (mixedSpace K)) (u : ι → mixedSpace K) :
    ‖M *ᵥ u‖ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖u‖ := by
  have hc : 0 ≤ ∑ i, ∑ j, ‖M i j‖ :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hc (norm_nonneg _))).mpr fun i ↦ ?_
  calc ‖(M *ᵥ u) i‖ = ‖∑ j, M i j * u j‖ := rfl
    _ ≤ ∑ j, ‖M i j * u j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖M i j‖ * ‖u‖ := Finset.sum_le_sum fun j _ ↦
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm u j) (norm_nonneg _))
    _ = (∑ j, ‖M i j‖) * ‖u‖ := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖u‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun i ↦ ∑ j, ‖M i j‖)
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i)

theorem exists_fractionalIdeal_of_isCompact (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : ι → 𝔸ᶠ[K])
    {C : Set (GL ι 𝔸[K])} (hC : IsCompact C) :
    ∃ J : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∀ h ∈ C, ∀ ξ : ι → K,
      (∀ i, finPartPi ((h : Matrix ι ι 𝔸[K]) *ᵥ fun i ↦ algebraMap K 𝔸[K] (ξ i)) i - b i ∈
        idealFiniteAdeles I) → ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 K)⁰ K) := by
  set B : Set (ι → 𝔸ᶠ[K]) :=
    Set.pi Set.univ fun i ↦ b i +ᵥ (idealFiniteAdeles I : Set 𝔸ᶠ[K])
  have hB : IsCompact B := isCompact_univ_pi fun i ↦ (isCompact_idealFiniteAdeles I).vadd (b i)
  let T : GL ι 𝔸[K] × (ι → 𝔸ᶠ[K]) → ι → 𝔸ᶠ[K] := fun p ↦
    (((p.1⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]).map Adele2.finRingHom) *ᵥ p.2
  have hT : Continuous T := by
    refine continuous_pi fun i ↦ ?_
    simp only [T, Matrix.mulVec, dotProduct, Matrix.map_apply]
    refine continuous_finsetSum _ fun j _ ↦ ?_
    exact (continuous_finRingHom.comp ((continuous_inv_entry i j).comp continuous_fst)).mul
      ((continuous_apply j).comp continuous_snd)
  set S : Set 𝔸ᶠ[K] := ⋃ i : ι, (fun x : ι → 𝔸ᶠ[K] ↦ x i) '' (T '' (C ×ˢ B))
  have hS : IsCompact S := isCompact_iUnion fun i ↦
    ((hC.prod hB).image hT).image (continuous_apply i)
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hS
  set dK := algebraMap (𝓞 K) K d
  have hdK : dK ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hd0
  refine ⟨Units.mk0 (FractionalIdeal.spanSingleton (𝓞 K)⁰ dK⁻¹)
    ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr (inv_ne_zero hdK)), ?_⟩
  intro h hh ξ hξ i
  set X : ι → 𝔸[K] := fun i ↦ algebraMap K 𝔸[K] (ξ i)
  have hTX : T (h, finPartPi ((h : Matrix ι ι 𝔸[K]) *ᵥ X)) =
      fun i ↦ algebraMap K 𝔸ᶠ[K] (ξ i) := by
    show _ *ᵥ finPartPi ((h : Matrix ι ι 𝔸[K]) *ᵥ X) = _
    rw [← finPartPi_mulVec, inv_mulVec_mulVec, finPartPi_algebraMap]
  have hmem : algebraMap K 𝔸ᶠ[K] (ξ i) ∈ S := by
    have hp : finPartPi ((h : Matrix ι ι 𝔸[K]) *ᵥ X) ∈ B := fun j _ ↦
      mem_vadd_idealFiniteAdeles.mpr (hξ j)
    have hq : (fun i ↦ algebraMap K 𝔸ᶠ[K] (ξ i)) ∈ T '' (C ×ˢ B) :=
      ⟨(h, finPartPi ((h : Matrix ι ι 𝔸[K]) *ᵥ X)), ⟨hh, hp⟩, hTX⟩
    exact Set.mem_iUnion.mpr ⟨i, _, hq, rfl⟩
  have h1 := hd _ hmem
  rw [← map_mul] at h1
  have h2 : dK * ξ i ∈ ((1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← algebraMap_mem_idealFiniteAdeles_iff, ← SetLike.mem_coe, idealFiniteAdeles_one]
    exact h1
  rw [Units.val_one] at h2
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp h2
  refine (FractionalIdeal.mem_spanSingleton _).mpr ⟨r, ?_⟩
  rw [Algebra.smul_def, hr, mul_comm dK, mul_assoc, mul_inv_cancel₀ hdK, mul_one]

theorem summable_latticeWeight_prod (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Summable fun ξ : ι → K ↦
      ∏ i, latticeWeight J (Module.finrank ℤ (idealLattice K J) + 1) (ξ i) :=
  _root_.UpperTheory.Reformulated.B.Qo1.summable_prod_coord (latticeWeight_nonneg J _)
    (summable_ite_mem_of_summable_idealLattice J
      (h := fun x ↦ ((1 + ‖x‖) ^ (Module.finrank ℤ (idealLattice K J) + 1))⁻¹)
      (summable_inv_one_add_norm_pow_idealLattice J))

theorem exists_summable_bound_tensor_cosetIndicator (φ : 𝓢(ι → mixedSpace K, ℂ))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b : ι → 𝔸ᶠ[K]) {C : Set (GL ι 𝔸[K])}
    (hC : IsCompact C) :
    ∃ u : (ι → K) → ℝ, Summable u ∧ ∀ h ∈ C, ∀ ξ : ι → K,
      ‖schwartzBruhatTensorPi φ (finiteTensor fun i ↦ cosetIndicator I (b i))
        ((h : Matrix ι ι 𝔸[K]) *ᵥ fun i ↦ algebraMap K 𝔸[K] (ξ i))‖ ≤ u ξ := by
  obtain ⟨J, hJ⟩ := exists_fractionalIdeal_of_isCompact I b hC
  set k := Module.finrank ℤ (idealLattice K J) + 1
  set n := Fintype.card ι
  obtain ⟨A, hA, hφ⟩ := exists_norm_le_inv_one_add_pow φ (k * n)
  let c : GL ι 𝔸[K] → ℝ := fun h ↦ ∑ i, ∑ j,
    ‖(((h⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]).map Adele2.infRingHom) i j‖
  have hc : Continuous c := continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦
    (continuous_infRingHom.comp (continuous_inv_entry i j)).norm
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  set B' := max B 1
  have hB'1 : 1 ≤ B' := le_max_right _ _
  have hB'0 : 0 < B' := zero_lt_one.trans_le hB'1
  refine ⟨fun ξ ↦ A * B' ^ (k * n) * ∏ i, latticeWeight J k (ξ i),
    (summable_latticeWeight_prod J).mul_left _, ?_⟩
  intro h hh ξ
  have hu0 : 0 ≤ A * B' ^ (k * n) * ∏ i, latticeWeight J k (ξ i) :=
    mul_nonneg (by positivity) (Finset.prod_nonneg fun i _ ↦ latticeWeight_nonneg J k _)
  set X : ι → 𝔸[K] := fun i ↦ algebraMap K 𝔸[K] (ξ i)
  set Y := (h : Matrix ι ι 𝔸[K]) *ᵥ X
  simp only [schwartzBruhatTensorPi, finiteTensor]
  by_cases hm : ∀ i, finPartPi Y i - b i ∈ idealFiniteAdeles I
  · have h1 : ∏ i, cosetIndicator I (b i) (finPartPi Y i) = 1 :=
      Finset.prod_eq_one fun i _ ↦ by rw [cosetIndicator_apply, ite_eq_left (hm i)]
    rw [h1, mul_one]
    have hξJ := hJ h hh ξ hm
    have hw : ∀ i, latticeWeight J k (ξ i) = ((1 + ‖mixedEmbedding K (ξ i)‖) ^ k)⁻¹ :=
      fun i ↦ ite_eq_left (hξJ i)
    simp only [hw]
    set y := infPartPi Y
    have hy : embPi K ξ =
        (((h⁻¹ : GL ι 𝔸[K]) : Matrix ι ι 𝔸[K]).map Adele2.infRingHom) *ᵥ y := by
      rw [← infPartPi_mulVec, inv_mulVec_mulVec, infPartPi_algebraMap]
    have hcB : c h ≤ B' := (le_abs_self _).trans (((Real.norm_eq_abs _).symm.trans_le (hB h hh)).trans
      (le_max_left _ _))
    have he : ‖embPi K ξ‖ ≤ B' * ‖y‖ := by
      rw [hy]
      exact (norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right hcB (norm_nonneg _))
    set t := B' * (1 + ‖y‖)
    have ht : 0 < t := by positivity
    have hle : ∀ i, 1 + ‖mixedEmbedding K (ξ i)‖ ≤ t := fun i ↦ by
      have h1 : ‖mixedEmbedding K (ξ i)‖ ≤ ‖embPi K ξ‖ := norm_le_pi_norm (embPi K ξ) i
      have : t = B' + B' * ‖y‖ := by simp only [t]; ring
      linarith
    have hinv : ∀ i, (t ^ k)⁻¹ ≤ ((1 + ‖mixedEmbedding K (ξ i)‖) ^ k)⁻¹ := fun i ↦ by
      have h0 : 0 < 1 + ‖mixedEmbedding K (ξ i)‖ := by positivity
      gcongr
      exact hle i
    calc ‖φ y‖ ≤ A * ((1 + ‖y‖) ^ (k * n))⁻¹ := hφ y
      _ = A * B' ^ (k * n) * ∏ _i : ι, (t ^ k)⁻¹ := by
          have hB0 : B' ^ (k * n) ≠ 0 := by positivity
          have hprod : ∏ _i : ι, (t ^ k)⁻¹ = (t ^ (k * n))⁻¹ := by
            rw [Finset.prod_const, Finset.card_univ, inv_pow, ← pow_mul]
          have ht' : t ^ (k * n) = B' ^ (k * n) * (1 + ‖y‖) ^ (k * n) := mul_pow _ _ _
          rw [hprod, ht', mul_inv, ← mul_assoc, mul_assoc A, mul_inv_cancel₀ hB0, mul_one]
      _ ≤ A * B' ^ (k * n) * ∏ i, ((1 + ‖mixedEmbedding K (ξ i)‖) ^ k)⁻¹ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun i _ ↦ hinv i
  · push Not at hm
    obtain ⟨i, hi⟩ := hm
    have hz : ∏ i, cosetIndicator I (b i) (finPartPi Y i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [cosetIndicator_apply, ite_eq_right hi])
    rw [hz, mul_zero, norm_zero]
    exact hu0

theorem exists_summable_bound_mulVec {F : (ι → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhatPi (K := K) (ι := ι))
    {C : Set (GL ι 𝔸[K])} (hC : IsCompact C) :
    ∃ u : (ι → K) → ℝ, Summable u ∧ ∀ h ∈ C, ∀ ξ : ι → K,
      ‖F ((h : Matrix ι ι 𝔸[K]) *ᵥ fun i ↦ algebraMap K 𝔸[K] (ξ i))‖ ≤ u ξ := by
  rw [schwartzBruhatPi_eq_cosetSpanPi] at hF
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, I, b, rfl⟩ := hG
    exact exists_summable_bound_tensor_cosetIndicator φ I b hC
  | zero => exact ⟨0, summable_zero, fun _ _ _ ↦ by simp⟩
  | add G H _ _ hG hH =>
    obtain ⟨u, hu, hGu⟩ := hG
    obtain ⟨w, hw, hHw⟩ := hH
    exact ⟨u + w, hu.add hw,
      fun a ha ξ ↦ (norm_add_le _ _).trans (add_le_add (hGu a ha ξ) (hHw a ha ξ))⟩
  | smul r G _ hG =>
    obtain ⟨u, hu, hGu⟩ := hG
    refine ⟨fun ξ ↦ ‖r‖ * u ξ, hu.mul_left _, fun a ha ξ ↦ ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (hGu a ha ξ) (norm_nonneg r)

theorem exists_summable_bound_thetaC {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι]
    [DecidableEq ι] {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι))
    {C : Set (GL ι 𝔸[k])} (hC : IsCompact C) :
    ∃ u : (ι → k) → ℝ, Summable u ∧ ∀ h ∈ C, ∀ ξ : ι → k,
      ‖F ((h : Matrix ι ι 𝔸[k]) *ᵥ PositivityTheory.RgEis.ratV ξ)‖ ≤ u ξ :=
  exists_summable_bound_mulVec hF hC

end

end GlobalTheory.CompanionTheory.EisRkNBound
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSummableMajorantLatticeSum =====
