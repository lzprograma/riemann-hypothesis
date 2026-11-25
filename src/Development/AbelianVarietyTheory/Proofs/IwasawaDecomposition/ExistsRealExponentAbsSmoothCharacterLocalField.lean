module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.GenericUnitary.NormEqOneOfValuationEqOne

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
namespace GlobalTheory.SmoothCharNorm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem finite_image_units (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    (χ '' {x : kˣ | valuation k (x : k) = 1}).Finite := by
  have hS := GlobalTheory.SmGL.UnramFixed.isCompact_unitsO k
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover
    (fun z : kˣ => (fun y => z⁻¹ * y) ⁻¹' (χ.ker : Set kˣ))
    (fun z => (continuous_const.mul continuous_id).isOpen_preimage _ hχ)
    (fun y _ => Set.mem_iUnion.2 ⟨y, by simp⟩)
  refine (t.finite_toSet.image χ).subset ?_
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 (ht hy)
  refine ⟨i, hi, ?_⟩
  have : χ (i⁻¹ * y) = 1 := hyi
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this

theorem norm_eq_one_of_valuation_eq_one (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (u : kˣ)
    (hu : valuation k (u : k) = 1) : ‖(χ u : ℂ)‖ = 1 := by
  apply _root_.PositivityTheory.RgUd.Exp.Rpow.norm_eq_one_of_valuation_eq_one <;> assumption

noncomputable def ordHom (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : kˣ →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (ord k x)
  map_one' := by
    have : ord k (1 : kˣ) = 0 := ord_eq_zero_iff.2 (by simp)
    simp [this]
  map_mul' x y := by simp [ord_mul, ofAdd_add]

theorem ord_zpow (x : kˣ) (n : ℤ) : ord k (x ^ n) = n * ord k x := by
  have := congrArg Multiplicative.toAdd (map_zpow (ordHom k) x n)
  simpa [ordHom, toAdd_zpow, smul_eq_mul] using this

end GlobalTheory.SmoothCharNorm

theorem GlobalTheory.SmoothCharNorm.norm_eq_nabs_rpow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ), IsSmoothChar χ → ∃ s : ℝ, ∀ z : kˣ, ‖(χ z : ℂ)‖ = nabs k z ^ s := by
  apply _root_.PositivityTheory.RgUd.Exp.Rpow.norm_eq_nabs_rpow <;> assumption
