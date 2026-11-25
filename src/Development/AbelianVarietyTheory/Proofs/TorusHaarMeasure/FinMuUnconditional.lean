module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsContinuousGramSchmidt
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.UpperTriangularPreservesDiagonalIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuOfFiniteCovolume
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetNeZeroOfIsOrth
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OrthonormalFramesBoundedOfDefinite
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsDriftFunctionRealUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIntMulIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContinuousOnRmul
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureStatements
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MuFLtTopOfIsCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Group.ModularCharacter
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsStrictMeasurableFundamentalSetOfDiscrete
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Presheaf

section
@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.FinCovol

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isCompact_orth_bounded :
    (∀ (r : ℕ) (X : Data E r) (R : ℝ),
      IsCompact {x : Frame X.Ψ r | IsOrth X x ∧ ∀ τ a b, ‖x τ a b‖ ≤ R}) := by
  intro r X R
  have h1 : IsClosed {x : Frame X.Ψ r | IsOrth X x} := by
    simp only [IsOrth, Set.ofPred_forall]
    refine isClosed_iInter fun τ => isClosed_eq ?_ continuous_const
    refine continuous_matrix fun a b => ?_
    simp only [gram, hermC, col, mat, Matrix.of_apply]
    fun_prop
  have h2 : IsClosed {x : Frame X.Ψ r | ∀ τ a b, ‖x τ a b‖ ≤ R} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_le ?_ continuous_const
    fun_prop
  refine Metric.isCompact_of_isClosed_isBounded (h1.inter h2) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Frame X.Ψ r)) (r := |R|)).subset ?_
  rintro x ⟨-, hx⟩
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (abs_nonneg R)]
  intro τ
  rw [pi_norm_le_iff_of_nonneg (abs_nonneg R)]
  intro a
  rw [pi_norm_le_iff_of_nonneg (abs_nonneg R)]
  intro b
  exact (hx τ a b).trans (le_abs_self R)

end GlobalTheory.FinCovol
end
end


section
@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.FiniteCovolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def uStabSubgroup {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) :
    Subgroup (GL (Fin r) E) where
  carrier := {γ | IsUStab G Λ γ}
  one_mem' := by simp [IsUStab]
  mul_mem' := fun {γ δ} hγ hδ => by
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hγ.1, hδ.1]
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← hγ.2, ← hδ.2]
  inv_mem' := fun h => isUStab_inv h


open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.FiniteCovolume.exists_stabiliser_image_subgroup :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∃ Γ : Subgroup H, ∀ g : H, g ∈ Γ ↔ (∃ γ : GL (Fin r) E, _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab X.Gm X.Λ γ ∧ ∀ τ : X.Ψ, ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1)) := by
  intro r X H _
  refine ⟨((_root_.GlobalTheory.FiniteCovolume.uStabSubgroup X.Gm X.Λ).map (_root_.GlobalTheory.FiniteCovolume.embGL X.Ψ)).comap
    H.subtype, fun g => ?_⟩
  simp only [Subgroup.mem_comap, Subgroup.mem_map, Subgroup.coe_subtype]
  constructor
  · rintro ⟨γ, hγ, hg⟩
    refine ⟨γ, hγ, fun τ => ?_⟩
    rw [← hg, _root_.GlobalTheory.FiniteCovolume.embGL_val]
  · rintro ⟨γ, hγ, hg⟩
    refine ⟨γ, hγ, funext fun τ => Units.ext ?_⟩
    rw [_root_.GlobalTheory.FiniteCovolume.embGL_val, hg]

end GlobalTheory.FiniteCovolume
end
end


section
section -- clump:auto
@[expose] public section

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem finite_covolume_of_drift_function :
    (∀ (Y σ : Type) [MeasurableSpace Y] [Fintype σ] [Nonempty σ] (μ : Measure Y) (R : Y → Y → Prop) (t : σ → Y → Y) (f : Y → ℝ) (c b : ℝ), (∀ s, Measurable (t s)) → (∀ s y y', R y y' → R (t s y) (t s y')) → (∀ φ : Y → ℝ≥0∞, Measurable φ → (∀ y y', R y y' → φ y = φ y') → ∀ s, ∫⁻ y, φ (t s y) ∂μ = ∫⁻ y, φ y ∂μ) → Measurable f → (∀ y, 0 ≤ f y) → (∀ y y', R y y' → f y = f y') → 0 ≤ c → c < 1 → 0 ≤ b → (∀ y, ∑ s, f (t s y) ≤ Fintype.card σ * (c * f y + b)) → ∃ M : ℝ, μ Set.univ ≤ 2 * μ {y | f y ≤ M}) → (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G), (∃ U ∈ 𝓝 (1 : G), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → Countable Γ ∧ ∃ F : Set G, MeasurableSet F ∧ ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ F) → (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (h k : G), k * h = h⁻¹ * k → ν.map (fun g => g * h) = ν) → (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] (F : Set G), MeasurableSet F → (∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ F) → (∀ h : G, ν.map (fun g => g * h) = ν → ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) → ∫⁻ g in F, φ (g * h) ∂ν = ∫⁻ g in F, φ g ∂ν) ∧ ∀ K : Set G, MeasurableSet K → ν (F ∩ {g | ∃ γ ∈ Γ, ∃ k ∈ K, g = γ * k}) ≤ ν K) → (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (Γ : Subgroup G) (σ : Type) [Fintype σ] [Nonempty σ] (h : σ → G) (f : G → ℝ) (c b : ℝ), (∃ U ∈ 𝓝 (1 : G), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → (∀ s, ∃ k : G, k * h s = (h s)⁻¹ * k) → Measurable f → (∀ g, 0 ≤ f g) → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → 0 ≤ c → c < 1 → 0 ≤ b → (∀ g, ∑ s, f (g * h s) ≤ Fintype.card σ * (c * f g + b)) → (∀ M : ℝ, ∃ K : Set G, IsCompact K ∧ ∀ g, f g ≤ M → ∃ γ ∈ Γ, ∃ k ∈ K, g = γ * k) → ∃ Ω : Set G, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : G, ∃ γ ∈ Γ, ∃ w ∈ Ω, g = γ * w) := by
  intro h₁ h₂ h₃ h₄ G _ _ _ _ _ _ _ _ ν _ Γ σ _ _ h f c b hΓ hh hf hf0 hfΓ hc0 hc1 hb hd hK
  obtain ⟨hcount, F, hF, hFu⟩ := h₂ G Γ hΓ
  obtain ⟨hinv, hle⟩ := h₄ G ν Γ F hF hFu
  obtain ⟨M, hM⟩ := h₁ G σ (ν.restrict F) (fun y y' => ∃ γ ∈ Γ, y' = γ * y)
    (fun s g => g * h s) f c b (fun s => measurable_mul_const (h s))
    (by
      rintro s y y' ⟨γ, hγ, rfl⟩
      exact ⟨γ, hγ, mul_assoc _ _ _⟩)
    (by
      intro φ hφ hR s
      obtain ⟨k, hk⟩ := hh s
      exact hinv (h s) (h₃ G ν (h s) k hk) φ hφ
        (fun γ hγ g => (hR g (γ * g) ⟨γ, hγ, rfl⟩).symm))
    hf hf0
    (by
      rintro y y' ⟨γ, hγ, rfl⟩
      exact (hfΓ γ hγ y).symm)
    hc0 hc1 hb hd
  obtain ⟨K, hKc, hKf⟩ := hK M
  refine ⟨F, hF, ?_, ?_⟩
  · rw [Measure.restrict_apply_univ, Measure.restrict_apply' hF] at hM
    have h5 : ν ({y | f y ≤ M} ∩ F) ≤ ν K := by
      refine le_trans (measure_mono ?_) (hle K hKc.measurableSet)
      rintro g ⟨hg, hgF⟩
      exact ⟨hgF, hKf g hg⟩
    refine lt_of_le_of_lt hM (ENNReal.mul_lt_top (by simp) ?_)
    exact lt_of_le_of_lt h5 hKc.measure_lt_top
  · intro g
    obtain ⟨γ, hγ, -⟩ := hFu g
    exact ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, γ * g, hγ, by group⟩

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FiniteCovolumeOfDriftFunction =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FundamentalSetLintegralMulRightAndMeasureLe =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FundamentalSetLintegralMulRightAndMeasureLe", "h": "module\n\npublic import Mathlib.MeasureTheory.Group.Measure\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Dynamics.Ergodic.Action.Regular\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.MeasureTheory.Group.FundamentalDomain\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem fundamentalSet_lintegral_mul_right_and_measure_le :
    (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] (F : Set G), MeasurableSet F → (∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ F) → (∀ h : G, ν.map (fun g => g * h) = ν → ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) → ∫⁻ g in F, φ (g * h) ∂ν = ∫⁻ g in F, φ g ∂ν) ∧ ∀ K : Set G, MeasurableSet K → ν (F ∩ {g | ∃ γ ∈ Γ, ∃ k ∈ K, g = γ * k}) ≤ ν K) := by
  intro G _ _ _ _ _ _ _ _ ν _ Γ _ F hF hex
  have hFD : IsFundamentalDomain Γ F ν :=
    IsFundamentalDomain.mk' hF.nullMeasurableSet (fun g => hex g)
  refine ⟨?_, ?_⟩
  · intro h hh φ hφ hinv
    have hmeas : MeasurableSet {g : G | g * h⁻¹ ∈ F} := (measurable_mul_const h⁻¹) hF
    have hFD' : IsFundamentalDomain Γ {g : G | g * h⁻¹ ∈ F} ν := by
      refine IsFundamentalDomain.mk' hmeas.nullMeasurableSet (fun g => ?_)
      have := hex (g * h⁻¹)
      simpa [Subgroup.smul_def, mul_assoc] using this
    have h1 : ∫⁻ g in {g : G | g * h⁻¹ ∈ F}, φ g ∂ν = ∫⁻ g in F, φ (g * h) ∂ν := by
      conv_lhs => rw [← hh]
      rw [setLIntegral_map hmeas hφ (measurable_mul_const h)]
      congr 2
      ext g
      simp
    rw [← h1]
    exact hFD'.setLIntegral_eq hFD φ (fun γ g => hinv γ γ.2 g)
  · intro K hK
    rw [hFD.measure_eq_tsum K]
    refine le_trans (measure_mono ?_) (measure_iUnion_le _)
    rintro g ⟨hg, γ, hγ, k, hk, rfl⟩
    exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨k, hk, rfl⟩, hg⟩

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FundamentalSetLintegralMulRightAndMeasureLe =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.HaarMapMulRightOfConjInv =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.HaarMapMulRightOfConjInv", "h": "module\n\npublic import Mathlib.MeasureTheory.Group.ModularCharacter\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem haar_map_mul_right_of_conj_inv :
    (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (h k : G), k * h = h⁻¹ * k → ν.map (fun g => g * h) = ν) := by
  intro G _ _ _ _ _ _ _ _ ν _ h k hk
  have e : h * (k * h) = k := by rw [hk, mul_inv_cancel_left]
  have e2 := congrArg Measure.modularCharacterFun e
  rw [Measure.modularCharacterFun_map_mul, Measure.modularCharacterFun_map_mul] at e2
  have hk0 : (0 : ℝ) < Measure.modularCharacterFun k := Measure.modularCharacterFun_pos k
  have hh0 : (0 : ℝ) < Measure.modularCharacterFun h := Measure.modularCharacterFun_pos h
  have e3 : (Measure.modularCharacterFun h : ℝ) *
      ((Measure.modularCharacterFun k : ℝ) * Measure.modularCharacterFun h) =
      Measure.modularCharacterFun k := by exact_mod_cast e2
  have e4 : (Measure.modularCharacterFun h : ℝ) * Measure.modularCharacterFun h = 1 := by
    apply mul_left_cancel₀ hk0.ne'
    linarith
  have e5 : (Measure.modularCharacterFun h : ℝ) = 1 := by nlinarith
  have e6 : Measure.modularCharacterFun h = 1 := by exact_mod_cast e5
  have hm : ν.map (fun g => g * h) = Measure.modularCharacterFun h • ν := by
    rw [Measure.modularCharacterFun_eq_haarScalarFactor ν h]
    exact Measure.isMulLeftInvariant_eq_smul _ ν
  rw [hm, e6, one_smul]

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.HaarMapMulRightOfConjInv =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureUnivLeTwoMulSublevelOfDrift =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureUnivLeTwoMulSublevelOfDrift", "h": "module\n\npublic import Mathlib.MeasureTheory.Integral.Lebesgue.Basic\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Monotonicity.Lemmas\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Presheaf\npublic import Mathlib.MeasureTheory.Constructions.BorelSpace.Real\npublic import Mathlib.MeasureTheory.Integral.Lebesgue.Add\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem measure_univ_le_two_mul_sublevel_of_drift :
    (∀ (Y σ : Type) [MeasurableSpace Y] [Fintype σ] [Nonempty σ] (μ : Measure Y)
      (R : Y → Y → Prop) (t : σ → Y → Y) (f : Y → ℝ) (c b : ℝ), (∀ s, Measurable (t s)) →
      (∀ s y y', R y y' → R (t s y) (t s y')) →
      (∀ φ : Y → ℝ≥0∞, Measurable φ → (∀ y y', R y y' → φ y = φ y') →
        ∀ s, ∫⁻ y, φ (t s y) ∂μ = ∫⁻ y, φ y ∂μ) →
      Measurable f → (∀ y, 0 ≤ f y) → (∀ y y', R y y' → f y = f y') → 0 ≤ c → c < 1 → 0 ≤ b →
      (∀ y, ∑ s, f (t s y) ≤ Fintype.card σ * (c * f y + b)) →
      ∃ M : ℝ, μ Set.univ ≤ 2 * μ {y | f y ≤ M}) := by
  intro Y σ _ _ _ μ R t f c b ht hR hinv hf hf0 hfR hc0 hc1 hb hdrift
  classical
  have h1c : 0 < 1 - c := by linarith
  obtain ⟨K, hK, hK0⟩ : ∃ K : ℝ, b = K * (1 - c) ∧ 0 ≤ K :=
    ⟨b / (1 - c), by field_simp, div_nonneg hb h1c.le⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 2 * K + 1 := ⟨_, rfl⟩
  have hM0 : 0 < M := by rw [hM]; linarith
  refine ⟨M, ?_⟩
  have hN : (0 : ℝ) < Fintype.card σ := by exact_mod_cast Fintype.card_pos
  have hA : MeasurableSet {y | f y ≤ M} := measurableSet_le hf measurable_const
  let g : ℕ → Y → ℝ := fun n =>
    Nat.rec (fun y => if f y ≤ M then 1 else 0)
      (fun _ h y => (Fintype.card σ : ℝ)⁻¹ * ∑ s, h (t s y)) n
  have g0 : ∀ y, g 0 y = if f y ≤ M then 1 else 0 := fun y => rfl
  have gs : ∀ n y, g (n + 1) y = (Fintype.card σ : ℝ)⁻¹ * ∑ s, g n (t s y) := fun n y => rfl
  clear_value g
  have gmeas : ∀ n, Measurable (g n) := by
    intro n
    induction n with
    | zero =>
      rw [show g 0 = _ from funext g0]
      exact Measurable.ite hA measurable_const measurable_const
    | succ n ih =>
      rw [show g (n + 1) = _ from funext (gs n)]
      exact measurable_const.mul (Finset.measurable_sum _ fun s _ => ih.comp (ht s))
  have gnn : ∀ n y, 0 ≤ g n y := by
    intro n
    induction n with
    | zero => intro y; rw [g0]; split_ifs <;> norm_num
    | succ n ih =>
      intro y; rw [gs]
      exact mul_nonneg (inv_nonneg.2 hN.le) (Finset.sum_nonneg fun s _ => ih _)
  have gR : ∀ n y y', R y y' → g n y = g n y' := by
    intro n
    induction n with
    | zero => intro y y' h; rw [g0, g0, hfR y y' h]
    | succ n ih =>
      intro y y' h; rw [gs, gs]
      congr 1
      exact Finset.sum_congr rfl fun s _ => ih _ _ (hR s _ _ h)
  have gint : ∀ n, ∫⁻ y, ENNReal.ofReal (g n y) ∂μ = μ {y | f y ≤ M} := by
    intro n
    induction n with
    | zero =>
      rw [← lintegral_indicator_one hA]
      refine lintegral_congr fun y => ?_
      rw [g0]
      by_cases h : f y ≤ M <;> simp [h, Set.indicator]
    | succ n ih =>
      have hm : Measurable fun y => ENNReal.ofReal (g n y) := (gmeas n).ennreal_ofReal
      have e : ∀ y, ENNReal.ofReal (g (n + 1) y) =
          (Fintype.card σ : ℝ≥0∞)⁻¹ * ∑ s, ENNReal.ofReal (g n (t s y)) := by
        intro y
        rw [gs, ENNReal.ofReal_mul (inv_nonneg.2 hN.le), ENNReal.ofReal_inv_of_pos hN,
          ENNReal.ofReal_natCast, ENNReal.ofReal_sum_of_nonneg fun s _ => gnn n _]
      simp_rw [e]
      have hN0 : (Fintype.card σ : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
      have hms : ∀ s, Measurable fun y => ENNReal.ofReal (g n (t s y)) :=
        fun s => hm.comp (ht s)
      rw [lintegral_const_mul _ (Finset.measurable_sum _ fun s _ => hms s),
        MeasureTheory.lintegral_finsetSum _ fun s _ => hms s]
      have : ∀ s, ∫⁻ y, ENNReal.ofReal (g n (t s y)) ∂μ = μ {y | f y ≤ M} := fun s => by
        rw [← ih]
        exact hinv (fun y => ENNReal.ofReal (g n y)) hm
          (fun y y' h => by simp only [gR n y y' h]) s
      simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, ENNReal.inv_mul_cancel hN0 (ENNReal.natCast_ne_top _), one_mul]
  have glow : ∀ n y, M - (c ^ n * f y + K * (1 - c ^ n)) ≤ M * g n y := by
    intro n
    induction n with
    | zero =>
      intro y; rw [g0]
      have := hf0 y
      split_ifs with h
      · simp [this]
      · simp only [pow_zero, one_mul, sub_self, mul_zero, add_zero]
        linarith [not_le.1 h]
    | succ n ih =>
      intro y
      have hcn : 0 ≤ c ^ n := pow_nonneg hc0 n
      have h1 : ∑ s, (M - (c ^ n * f (t s y) + K * (1 - c ^ n))) ≤ ∑ s, M * g n (t s y) :=
        Finset.sum_le_sum fun s _ => ih _
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        at h1
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
      have h2 := mul_le_mul_of_nonneg_left (hdrift y) hcn
      rw [gs, mul_left_comm, le_inv_mul_iff₀ hN, pow_succ]
      rw [hK] at h2
      rw [← Finset.mul_sum] at h1
      nlinarith
  have hlim : ∀ y, (2⁻¹ : ℝ≥0∞) ≤
      Filter.liminf (fun n => ENNReal.ofReal (g n y)) Filter.atTop := by
    intro y
    refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
    have h0 : Filter.Tendsto (fun n : ℕ => c ^ n * f y) Filter.atTop (𝓝 (0 * f y)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const _
    rw [zero_mul] at h0
    filter_upwards [h0.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with n hn
    have h1 := glow n y
    have h2 : 0 ≤ K * c ^ n := mul_nonneg hK0 (pow_nonneg hc0 n)
    have h3 : M * 2⁻¹ ≤ M * g n y := by nlinarith
    have h4 : (2⁻¹ : ℝ) ≤ g n y := le_of_mul_le_mul_left h3 hM0
    have := ENNReal.ofReal_le_ofReal h4
    rwa [ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat] at this
  have hF : 2⁻¹ * μ Set.univ ≤ μ {y | f y ≤ M} := by
    rw [← lintegral_const]
    refine (lintegral_mono hlim).trans ?_
    refine (lintegral_liminf_le fun n => (gmeas n).ennreal_ofReal).trans ?_
    simp only [gint, Filter.liminf_const, le_refl]
  calc μ Set.univ = 2 * (2⁻¹ * μ Set.univ) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    _ ≤ _ := by gcongr

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureUnivLeTwoMulSublevelOfDrift =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsFiniteMeasureCoverOfDriftFunction =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsFiniteMeasureCoverOfDriftFunction", "h": "module\n\npublic import Mathlib.MeasureTheory.Group.Measure\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsStrictMeasurableFundamentalSetOfDiscrete\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FiniteCovolumeOfDriftFunction\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FundamentalSetLintegralMulRightAndMeasureLe\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.HaarMapMulRightOfConjInv\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureUnivLeTwoMulSublevelOfDrift\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem exists_finite_measure_cover_of_drift_function : (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (Γ : Subgroup G) (σ : Type) [Fintype σ] [Nonempty σ] (h : σ → G) (f : G → ℝ) (c b : ℝ), (∃ U ∈ 𝓝 (1 : G), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → (∀ s, ∃ k : G, k * h s = (h s)⁻¹ * k) → Measurable f → (∀ g, 0 ≤ f g) → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → 0 ≤ c → c < 1 → 0 ≤ b → (∀ g, ∑ s, f (g * h s) ≤ Fintype.card σ * (c * f g + b)) → (∀ M : ℝ, ∃ K : Set G, IsCompact K ∧ ∀ g, f g ≤ M → ∃ γ ∈ Γ, ∃ k ∈ K, g = γ * k) → ∃ Ω : Set G, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : G, ∃ γ ∈ Γ, ∃ w ∈ Ω, g = γ * w) :=
  GlobalTheory.finite_covolume_of_drift_function GlobalTheory.measure_univ_le_two_mul_sublevel_of_drift
    GlobalTheory.exists_strict_measurable_fundamental_set_of_discrete GlobalTheory.haar_map_mul_right_of_conj_inv
    GlobalTheory.fundamentalSet_lintegral_mul_right_and_measure_le

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsFiniteMeasureCoverOfDriftFunction =====
end


-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsBoundOrthonormalFrameMahler, Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsUnitaryElemOfIsUStab, Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CompactModLatticeStabiliserOfLeFirstMinimum, Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CompactSpaceRealUnitaryGroupOfDefinite, Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GamDisc, Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsFiniteMeasureCoverUnitaryLattice, Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuOfCovolume, Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuUnconditional

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsBoundOrthonormalFrameMahler =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsBoundOrthonormalFrameMahler", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsContinuousGramSchmidt\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.UpperTriangularPreservesDiagonalIff\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS\n\n"}
section -- clump:auto
@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.OrthFrameMahler

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem continuousOn_rmul_self {Ψ : Finset (E →+* ℂ)} {r : ℕ} {β : Frame Ψ r → Frame Ψ r}
    {K : Set (Frame Ψ r)} (hβ : ContinuousOn β K) : ContinuousOn (fun y => rmul y (β y)) K := by
  refine continuousOn_pi.2 fun τ => continuousOn_pi.2 fun a => continuousOn_pi.2 fun c => ?_
  show ContinuousOn (fun y : Frame Ψ r => ∑ k, y τ a k * β y τ k c) K
  refine continuousOn_finsetSum _ fun k _ => ContinuousOn.mul (by fun_prop) ?_
  exact continuousOn_pi.1 (continuousOn_pi.1 (continuousOn_pi.1 hβ τ) k) c

theorem norm_apply_le_of_diagonal {Ψ : Finset (E →+* ℂ)} {r : ℕ} (z t : Frame Ψ r)
    (hdiag : ∀ τ a, ‖t τ a a‖ = 1 ∧ ∀ c, c ≠ a → t τ a c = 0) (τ : Ψ) (a c : Fin r) :
    ‖z τ a c‖ ≤ ‖rmul z t‖ := by
  have h1 : rmul z t τ a c = z τ a c * t τ c c := by
    show ∑ k, z τ a k * t τ k c = _
    refine Finset.sum_eq_single c (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ c) h)
    rw [(hdiag τ k).2 c (Ne.symm hk), mul_zero]
  calc ‖z τ a c‖ = ‖rmul z t τ a c‖ := by
        rw [h1, norm_mul, (hdiag τ c).1, mul_one]
    _ ≤ ‖rmul z t τ a‖ := norm_le_pi_norm _ c
    _ ≤ ‖rmul z t τ‖ := norm_le_pi_norm _ a
    _ ≤ ‖rmul z t‖ := norm_le_pi_norm _ τ

theorem exists_bound_orthonormal_frame :
    (∀ (r : ℕ) (X : Data E r) (ε : ℝ), 0 < ε → ∃ R : ℝ, ∀ x, IsOrth X x → ε ≤ X.la1 x →
      ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∀ τ a b, ‖lact γ x τ a b‖ ≤ R) := by
  intro r X ε hε
  obtain ⟨K, hKc, hKd, hK⟩ := GlobalTheory.FlagMahler.mahler_compactness (E := E) r X ε hε
  obtain ⟨β, hβc, hβ⟩ := GlobalTheory.GramSchmidtCont.exists_continuous_gramSchmidt (E := E) r X
  obtain ⟨R, hR⟩ := hKc.exists_bound_of_continuousOn (continuousOn_rmul_self (hβc.mono hKd))
  refine ⟨R, fun x hx hla => ?_⟩
  obtain ⟨γ, hγ, b, hb, hy⟩ := hK x (IW.orth_mem_dom X x hx) hla
  refine ⟨γ, X.Γ_stab γ hγ, fun τ a c => ?_⟩
  obtain ⟨hβb, hβo⟩ := hβ _ (hKd hy)
  have hRy : ‖rmul (lact γ (rmul x b)) (β (lact γ (rmul x b)))‖ ≤ R := hR _ hy
  generalize β (lact γ (rmul x b)) = s at hβb hβo hRy
  rw [FundSetPf.lact_rmul, ExtFPf.rmul_assoc] at hβo hRy
  have hγo : IsOrth X (lact γ x) := fun σ => by rw [OntoS.gram_lact X hγ]; exact hx σ
  have hdiag := (GlobalTheory.isOrth_rmul_iff_unitary_diagonal r X _ _ hγo (ExtFPf.mul_mem X hb hβb)).1 hβo
  exact (norm_apply_le_of_diagonal _ _ hdiag τ a c).trans hRy

end GlobalTheory.OrthFrameMahler
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsBoundOrthonormalFrameMahler =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsUnitaryElemOfIsUStab =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsUnitaryElemOfIsUStab", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuOfFiniteCovolume\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.FiniteCovolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_unitary_elem_of_isUStab :
    (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ → ∃ g : H, ∀ τ : X.Ψ, ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) :=
  fun _ X _ hH γ hγ =>
    ⟨⟨embGL X.Ψ γ, (hH _).mpr (isUnitaryC_of_isUStab X hγ)⟩, fun τ => embGL_val X.Ψ γ τ⟩

end GlobalTheory.FiniteCovolume
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsUnitaryElemOfIsUStab =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CompactModLatticeStabiliserOfLeFirstMinimum =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CompactModLatticeStabiliserOfLeFirstMinimum", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetNeZeroOfIsOrth\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsStabiliserImageSubgroup\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsUnitaryElemOfIsUStab\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IsCompactOrthBounded\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.FiniteCovolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_unitaryStab_mul_compact_of_le_firstMinimum :
    (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ x0, IsOrth X x0 → ∀ ε : ℝ, 0 < ε → ∃ K : Set H, IsCompact K ∧ ∀ g : H, ε ≤ X.la1 (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) → ∃ u : H, (∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∀ τ : X.Ψ, ((((u : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) ∧ ∃ k ∈ K, g = u * k) := by
  intro r X H hH x0 hx0 ε hε
  obtain ⟨-, -, hfr⟩ := GlobalTheory.UnitaryFrames.unitary_group_frames.2 r X H hH
  obtain ⟨horth, ι, hιc, -, hιg⟩ := hfr x0 hx0
  obtain ⟨R, hR⟩ := _root_.GlobalTheory.OrthFrameMahler.exists_bound_orthonormal_frame r X ε hε
  obtain ⟨Γ, hΓ⟩ := exists_stabiliser_image_subgroup r X H hH
  refine ⟨ι '' {x : Frame X.Ψ r | IsOrth X x ∧ ∀ τ a b, ‖x τ a b‖ ≤ R},
    (GlobalTheory.FinCovol.isCompact_orth_bounded r X R).image_of_continuousOn
      (hιc.mono fun x hx => hx.1), fun g hg => ?_⟩
  obtain ⟨γ, hγ, hb⟩ := hR _ (horth g) hg
  obtain ⟨u, hu⟩ := exists_unitary_elem_of_isUStab r X H hH γ hγ
  have huΓ : u ∈ Γ := (hΓ u).2 ⟨γ, hγ, hu⟩
  refine ⟨u⁻¹, (hΓ _).1 (Γ.inv_mem huΓ), u * g, ⟨_, ⟨horth (u * g), ?_⟩, hιg (u * g)⟩,
    (inv_mul_cancel_left u g).symm⟩
  have key : X.lmulC (fun τ => (((u * g : H) : X.Ψ → GL (Fin r) ℂ) τ :
      Matrix (Fin r) (Fin r) ℂ)) x0 = lact γ (X.lmulC (fun τ =>
        (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) := by
    funext τ
    change (((u : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) *
        ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) * mat x0 τ =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 *
        (((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) * mat x0 τ)
    rw [hu, Matrix.mul_assoc]
  rw [key]
  exact hb

end GlobalTheory.FiniteCovolume
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CompactModLatticeStabiliserOfLeFirstMinimum =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CompactSpaceRealUnitaryGroupOfDefinite =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CompactSpaceRealUnitaryGroupOfDefinite", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetNeZeroOfIsOrth\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IsCompactOrthBounded\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OrthonormalFramesBoundedOfDefinite\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.FinCovol

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem compactSpace_unitary_of_definite :
    (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)),
      (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) →
      (X.p0 = 0 ∨ X.p0 = r) → CompactSpace H) := by
  intro r X H hH hp
  obtain ⟨R, hR⟩ := GlobalTheory.orthonormal_frames_bounded_of_definite r X hp
  have hx0 : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2
  obtain ⟨-, -, h⟩ := GlobalTheory.UnitaryFrames.unitary_group_frames.2 r X H hH
  obtain ⟨horth, ι, hc, -, hι⟩ := h (x0F X) hx0
  have hK := (isCompact_orth_bounded r X R).image_of_continuousOn
    (hc.mono fun x hx => hx.1)
  refine ⟨hK.of_isClosed_subset isClosed_univ fun g _ => ?_⟩
  exact ⟨_, ⟨horth g, hR _ (horth g)⟩, hι g⟩

end GlobalTheory.FinCovol
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CompactSpaceRealUnitaryGroupOfDefinite =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GamDisc =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GamDisc", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIntMulIntegral\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom\nimport ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization\n\n"}
section -- clump:auto
@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.GamDisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem gamDisc : (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∃ U ∈ 𝓝 (1 : H), ∀ g : H, (∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∀ τ : X.Ψ, ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) → g ∈ U → g = 1) := by
  intro r X H _
  have hS := GlobalTheory.LatFin.latFin.2 r X 2
  set S := {γ : GL (Fin r) E | IsUStab X.Gm X.Λ γ ∧ ∀ (τ : X.Ψ) (a b : Fin r),
    ‖τ.1 ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ 2} with hSdef
  let F : GL (Fin r) E → Set H := fun γ => {g : H | ∀ τ : X.Ψ,
    ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1}
  have hF : ∀ γ, (F γ).Finite := by
    intro γ
    refine Set.Subsingleton.finite ?_
    intro g hg g' hg'
    refine Subtype.ext (funext fun τ => Units.ext ?_)
    exact (hg τ).trans (hg' τ).symm
  have hT : (⋃ γ ∈ S, F γ).Finite := hS.biUnion fun γ _ => hF γ
  have hC : ((⋃ γ ∈ S, F γ) \ {1})ᶜ ∈ 𝓝 (1 : H) :=
    (hT.subset Set.diff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
  have hV : ∀ᶠ g : H in 𝓝 1, ∀ (τ : X.Ψ) (a b : Fin r),
      ‖((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b‖ < 2 := by
    simp only [Filter.eventually_all]
    intro τ a b
    have hc : Continuous fun g : H =>
        ‖((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b‖ :=
      ((Units.continuous_val.comp
        ((continuous_apply τ).comp continuous_subtype_val)).matrix_elem a b).norm
    refine hc.continuousAt.eventually_lt continuousAt_const ?_
    by_cases h : a = b <;> simp [h]
  refine ⟨_, Filter.inter_mem hC hV, ?_⟩
  rintro g ⟨γ, hγ, hg⟩ ⟨h1, h2⟩
  by_contra hne
  refine h1 ⟨Set.mem_biUnion (x := γ) ⟨hγ, fun τ a b => ?_⟩ hg, hne⟩
  have := h2 τ a b
  rw [hg τ] at this
  exact this.le

end GlobalTheory.GamDisc
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GamDisc =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsFiniteMeasureCoverUnitaryLattice =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsFiniteMeasureCoverUnitaryLattice", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound\nimport Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetNeZeroOfIsOrth\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsFiniteMeasureCoverOfDriftFunction\nimport Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsStabiliserImageSubgroup\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GamDisc\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Algebra.Group.Units\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory.FiniteCovolume

theorem exists_finite_measure_cover : (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure], ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∃ w ∈ Ω, ∀ τ : X.Ψ, (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (((w : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) := by
  intro r X H hH _ _ ν _
  obtain ⟨Γ, hΓ⟩ := GlobalTheory.FiniteCovolume.exists_stabiliser_image_subgroup r X H hH
  suffices hS : ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ ∈ Γ, ∃ w ∈ Ω, g = γ * w by
    obtain ⟨Ω, h1, h2, h3⟩ := hS
    refine ⟨Ω, h1, h2, fun g => ?_⟩
    obtain ⟨u, hu, w, hw, rfl⟩ := h3 g
    obtain ⟨γ, hγ, hγu⟩ := (hΓ u).1 hu
    refine ⟨γ, hγ, w, hw, fun τ => ?_⟩
    rw [← hγu τ]
    simp
  by_cases hp : X.p0 = 0 ∨ X.p0 = r
  · haveI : CompactSpace H := _root_.GlobalTheory.FinCovol.compactSpace_unitary_of_definite r X H hH hp
    exact ⟨Set.univ, MeasurableSet.univ, isCompact_univ.measure_lt_top,
      fun g => ⟨1, Γ.one_mem, g, Set.mem_univ _, (one_mul g).symm⟩⟩
  · have hp0 : 0 < X.p0 := Nat.pos_of_ne_zero fun h => hp (Or.inl h)
    have hpr : X.p0 < r := lt_of_le_of_ne X.p0_le fun h => hp (Or.inr h)
    obtain ⟨hlc, hsc, -⟩ := (GlobalTheory.UnitaryFrames.unitary_group_frames (E := E)).2 r X H hH
    have hx0 : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2
    obtain ⟨σ, _, _, h, f, c, b, hk, hf, hf0, hinv, hc0, hc1, hb, hdrift, hsub⟩ :=
      _root_.GlobalTheory.DriftUnitary.exists_drift_function r X H hH hp0 hpr (x0F X) hx0
    obtain ⟨U, hU, hU1⟩ := GlobalTheory.GamDisc.gamDisc r X H hH
    refine GlobalTheory.exists_finite_measure_cover_of_drift_function H ν Γ σ h f c b
      ⟨U, hU, fun γ hγ => hU1 γ ((hΓ γ).1 hγ)⟩ hk hf hf0
      (fun γ hγ => hinv γ ((hΓ γ).1 hγ)) hc0 hc1 hb hdrift fun M => ?_
    obtain ⟨ε, hε, hM⟩ := hsub M
    obtain ⟨K, hK, hKc⟩ := _root_.GlobalTheory.FiniteCovolume.exists_unitaryStab_mul_compact_of_le_firstMinimum r X H hH (x0F X) hx0 ε hε
    refine ⟨K, hK, fun g hg => ?_⟩
    obtain ⟨u, hu, k, hk, e⟩ := hKc g (hM g hg)
    exact ⟨u, (hΓ u).2 hu, k, hk, e⟩

end GlobalTheory.FiniteCovolume
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsFiniteMeasureCoverUnitaryLattice =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuOfCovolume =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuOfCovolume", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContinuousOnRmul\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetNeZeroOfIsOrth\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsContinuousGramSchmidt\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuOfFiniteCovolume\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureStatements\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MuFLtTopOfIsCompact\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.UpperTriangularPreservesDiagonalIff\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.ClosedFiniteMeasure

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem finMu_of_covolume :
    (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure], ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∃ w ∈ Ω, ∀ τ : X.Ψ, (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (((w : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → (∀ (r : ℕ) (X : Data E r), FinMu X) := by
  intro hcov
  exact GlobalTheory.FiniteCovolume.finMu_of_finite_covolume hcov GlobalTheory.UnitaryFrames.unitary_group_frames
    (GlobalTheory.UnitaryInvMeasure.invMeas GlobalTheory.FrameMeasureClosed.measInv_holds
      GlobalTheory.GramSchmidtCont.exists_continuous_gramSchmidt GlobalTheory.isOrth_rmul_iff_unitary_diagonal
      (GlobalTheory.SatFin.muF_sat_lt_top GlobalTheory.FrameMeasureClosed.measInv_holds)
      GlobalTheory.UnitaryFrames.unitary_group_frames.2)
    GlobalTheory.ClosedDiscontinuity.propDisc_closed

end GlobalTheory.ClosedFiniteMeasure
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuOfCovolume =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuUnconditional =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuUnconditional", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames\npublic import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuOfCovolume\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.DriftCovolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem finMu_unconditional : ∀ (r : ℕ) (X : Data E r), FinMu X :=
  GlobalTheory.ClosedFiniteMeasure.finMu_of_covolume _root_.GlobalTheory.FiniteCovolume.exists_finite_measure_cover

end GlobalTheory.DriftCovolume
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuUnconditional =====
