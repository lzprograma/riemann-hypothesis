module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Basic.Finite.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory

theorem exists_unit_of_cocycle_rightAction_charZero :
    ∀ (K : Type) [Field K] [CharZero K] (Γ : Type) [Group Γ] [Finite Γ] (σ : Γ → K →+* K),
    (∀ γ δ a, σ (γ * δ) a = σ δ (σ γ a)) → ∀ (c : Γ → Kˣ),
    (∀ γ δ, (c (γ * δ) : K) = σ δ (c γ) * c δ) → (∀ γ, (∀ a, σ γ a = a) → c γ = 1) →
    ∃ f : Kˣ, ∀ γ, σ γ f = c γ * f := by
  intro K _ _ Γ _ _ σ hσ c hc htriv
  classical
  haveI := Fintype.ofFinite Γ
  have h1 : ∀ a, σ 1 a = a := by
    intro a
    have e := hσ 1 1 a
    rw [mul_one] at e
    exact (σ 1).injective e.symm
  have key : ∀ γ δ, (σ δ (c γ : K))⁻¹ = (c δ : K) * ((c (γ * δ) : K))⁻¹ := by
    intro γ δ
    rw [hc γ δ, mul_inv, mul_left_comm, mul_inv_cancel₀ (Units.ne_zero _), mul_one]
  let F : K → K := fun b => ∑ γ, ((c γ : K))⁻¹ * σ γ b
  have hF : ∀ b δ, σ δ (F b) = c δ * F b := by
    intro b δ

    simp only [F, map_sum, map_mul, map_inv₀, Finset.mul_sum]
    apply Fintype.sum_equiv (Equiv.mulRight δ)
    intro γ
    simp only [Equiv.coe_mulRight]
    rw [key γ δ, hσ]
    ring
  have hex : ∃ b, F b ≠ 0 := by
    by_contra! hno
    let φ : Γ → (K →* K) := fun γ => (σ γ : K →* K)
    let s : Finset (K →* K) := Finset.univ.image φ
    let g : (K →* K) → K := fun ψ => ∑ γ ∈ Finset.univ.filter (fun γ => φ γ = ψ), ((c γ : K))⁻¹
    have hli := linearIndependent_monoidHom K K
    have hsum : ∑ ψ ∈ s, g ψ • (ψ : K → K) = 0 := by
      funext b
      rw [Finset.sum_apply, Pi.zero_apply, ← hno b]
      simp only [Pi.smul_apply, smul_eq_mul, g, Finset.sum_mul]
      have hterm : ∀ ψ ∈ s, ∑ i ∈ Finset.univ.filter (fun γ => φ γ = ψ), ((c i : K))⁻¹ * ψ b
          = ∑ i ∈ Finset.univ.filter (fun γ => φ γ = ψ), ((c i : K))⁻¹ * σ i b := fun ψ _ =>
        Finset.sum_congr rfl fun γ hγ => by rw [← (Finset.mem_filter.mp hγ).2]; rfl
      rw [Finset.sum_congr rfl hterm, Finset.sum_fiberwise_of_maps_to
        (fun γ _ => Finset.mem_image_of_mem φ (Finset.mem_univ γ))]
    have hz := linearIndependent_iff'.mp hli s g hsum (φ 1)
      (Finset.mem_image_of_mem φ (Finset.mem_univ 1))
    have hterm : ∀ γ ∈ Finset.univ.filter (fun γ => φ γ = φ 1), ((c γ : K))⁻¹ = 1 := by
      intro γ hγ
      rw [Finset.mem_filter] at hγ
      have hid : ∀ a, σ γ a = a := fun a => (DFunLike.congr_fun hγ.2 a).trans (h1 a)
      rw [htriv γ hid]
      simp
    have hcard : g (φ 1) = ((Finset.univ.filter (fun γ => φ γ = φ 1)).card : K) := by
      simp only [g]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hcard, Nat.cast_eq_zero, Finset.card_eq_zero] at hz
    have hmem : (1 : Γ) ∈ Finset.univ.filter (fun γ => φ γ = φ 1) := by simp
    rw [hz] at hmem
    simp at hmem
  obtain ⟨b, hb⟩ := hex
  refine ⟨Units.mk0 (F b) hb, fun γ => ?_⟩
  simp only [Units.val_mk0]
  exact hF b γ

end GlobalTheory
