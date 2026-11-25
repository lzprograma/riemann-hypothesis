module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FundamentalDomainUnitaryAdelicExistsMeasureEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.Published.SiegelOneVector

section Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def IsSchwartzArch {M n : ℕ} (Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) : Prop :=
  ∃ (N : ℕ) (e : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ)),
    Continuous e ∧ Continuous e.symm ∧ ∃ f : SchwartzMap (Fin N → ℝ) ℂ, ∀ X, Φinf X = f (e X)

def IsSchwartzBruhat {M n : ℕ} (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) : Prop :=
  ∃ (k : ℕ) (Φinf : Fin k → (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (Φf : Fin k → (Fin n → Fin M → Af F ⊗[F] E) → ℂ),
    (∀ i, IsSchwartzArch (Φinf i)) ∧ (∀ i, IsSB (Φf i)) ∧
      ∀ X, Φ X = ∑ i, Φinf i (projInf X) * Φf i (projFin X)

variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

def thetaTerm (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) (h : HA (AF F) σ J) (x : Fin 1 → Fin M → E) : ℂ :=
  Φ (h⁻¹ • ratTup (F := F) (AF F) x)

def theta (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) (h : HA (AF F) σ J) : ℂ :=
  ∑' x : Fin 1 → Fin M → E, thetaTerm σ J Φ h x

end Defs

end GlobalTheory.Published.SiegelOneVector

namespace GlobalTheory.Published.SiegelOneVector

section Inhabitants

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isSchwartzBruhat_of_prod {M n : ℕ} {Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ}
    {Φinf : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ} {Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ}
    (hi : IsSchwartzArch Φinf) (hf : IsSB Φf) (h : IsProdInfFin Φ Φinf Φf) : IsSchwartzBruhat Φ :=
  ⟨1, fun _ => Φinf, fun _ => Φf, fun _ => hi, fun _ => hf, fun X => by simp [h X]⟩

variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem normalise (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) (μ : Measure (HA (AF F) σ J))
    (𝓕 : Set (HA (AF F) σ J)) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ) :
    μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤ ∧ ((μ 𝓕)⁻¹ • μ).IsHaarMeasure ∧
      IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 ((μ 𝓕)⁻¹ • μ) ∧ ((μ 𝓕)⁻¹ • μ) 𝓕 = 1 := by
  have h0 : μ 𝓕 ≠ 0 := ((GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary F E σ M J μ hμ).2 𝓕 𝓕 h𝓕 h𝓕).2
  have h1 : μ 𝓕 ≠ ⊤ := (GlobalTheory.Mem.VolFin.finVol F E σ hCM M J hJ μ hμ 𝓕 h𝓕).ne
  refine ⟨h0, h1, Measure.IsHaarMeasure.smul μ (ENNReal.inv_ne_zero.2 h1) (ENNReal.inv_ne_top.2 h0),
    h𝓕.mono Measure.smul_absolutelyContinuous, ?_⟩
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 h1]

theorem exists_normalised (hCM : IsCMExt F E σ) (hJ : IsHermND σ J) :
    ∃ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)),
      μ.IsHaarMeasure ∧ IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ ∧ μ 𝓕 = 1 := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA σ J
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA σ J
  have := (GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary F E σ M J).1
  have hμ : (Measure.haar : Measure (HA (AF F) σ J)).IsHaarMeasure := inferInstance
  obtain ⟨𝓕, h𝓕⟩ := (GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary F E σ M J _ hμ).1
  obtain ⟨-, -, h1, h2, h3⟩ := normalise σ J hCM hJ _ 𝓕 hμ h𝓕
  exact ⟨_, 𝓕, h1, h2, h3⟩

end Inhabitants

end GlobalTheory.Published.SiegelOneVector
