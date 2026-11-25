module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlProps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.FinTwO
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.OmFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.PlKill
import all Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.PlKill
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

section Abs

variable {K R M : Type} [Group K] [CommRing R] [Ring M] [Module R M] (ρ z : K → M) (χ : K → R)
  (h1 : ρ 1 = 1) (hm : ∀ g h, ρ (g * h) = ρ g * ρ h) (c1 : χ 1 = 1) (cm : ∀ g h, χ (g * h) = χ g * χ h)
  (hz : ∀ g h, z (g * h) = z g + χ g • (ρ g * z h * ρ g⁻¹))

include h1 c1 hz in
private theorem twisted_cocycle_apply_one : z 1 = 0 := by
  have := hz 1 1
  rw [mul_one, inv_one, h1, c1, one_mul, mul_one, one_smul] at this
  exact left_eq_add.1 this

private theorem tw_inv {N : Type} [Monoid N] (ρ : K → N) (h1 : ρ 1 = 1) (hm : ∀ g h, ρ (g * h) = ρ g * ρ h)
    {g : K} (hg : ρ g = 1) : ρ g⁻¹ = 1 := by
  have := hm g g⁻¹
  rw [mul_inv_cancel, h1, hg, one_mul] at this
  exact this.symm

include h1 hm hz in
private theorem tw_add {g : K} (hg : ρ g = 1) (hc : χ g = 1) (h : K) : z (g * h) = z g + z h := by
  rw [hz, tw_inv ρ h1 hm hg, hg, hc, one_mul, mul_one, one_smul]

include h1 hm c1 cm hz in
private theorem tw_U [TopologicalSpace K] (cρ : IsLocallyConstant ρ) (cχ : IsLocallyConstant χ)
    (cz : IsLocallyConstant z) :
    ∃ U : OpenNormalSubgroup K, ∀ g, g ∈ U ↔ ρ g = 1 ∧ χ g = 1 ∧ z g = 0 := by
  apply _root_.tw_U <;> assumption

end Abs

private theorem tw_lc {Γ R : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g0
  have : ∀ᶠ g in nhds g0, ∀ i j, f g i j = f g0 i j :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => (h i j).eventually_eq g0
  filter_upwards [this] with g hg
  exact Matrix.ext hg

private theorem tw_core {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (K P : Subgroup Γ) [P.Normal] (hK : IsOpen (K : Set Γ)) (hP : P ≤ K) :
    ∃ U : OpenNormalSubgroup Γ, P ≤ U.toSubgroup ∧ U.toSubgroup ≤ K := by
  haveI : Finite (Γ ⧸ K) := Subgroup.quotient_finite_of_isOpen K hK
  haveI : K.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hc : IsClosed (K.normalCore : Set Γ) := Subgroup.normalCore_isClosed K (K.isClosed_of_isOpen hK)
  have ho : IsOpen (K.normalCore : Set Γ) := Subgroup.isOpen_of_isClosed_of_finiteIndex _ hc
  exact ⟨{ toSubgroup := K.normalCore, isOpen' := ho, isNormal' := inferInstance },
    Subgroup.normal_le_normalCore.2 hP, K.normalCore_le⟩

private theorem phEq_one (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n)
    (m : ℕ) (hPL : ∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1)
    (z : G0.G₀ → Mm O n m) (cz : IsLocallyConstant z)
    (hz : ∀ g h : G0.G₀, z (g * h) = z g + epsm O G0 m g • (y.ρ0 m g * z h * y.ρ0 m g⁻¹))
    (j : Fin T.q) : ∀ᶠ N in atTop, y.ρ0 m ((T.h N).p₀ (T.ph N j)) = y.ρ0 m (T.sg j) ∧
      epsm O G0 m ((T.h N).p (T.ph N j)) = 1 ∧ z ((T.h N).p₀ (T.ph N j)) = z (T.sg j) := by
  obtain ⟨-, -, -, f4, f5⟩ := (omFacts l O).2 m
  have r1 : y.ρ0 m 1 = 1 := by
    show (Ideal.Quotient.mk (maximalIdeal O ^ m)).mapMatrix (mat y.ρ 1) = 1
    rw [map_one, map_one]
  have r2 : ∀ g h, y.ρ0 m (g * h) = y.ρ0 m g * y.ρ0 m h := fun g h => by
    show (Ideal.Quotient.mk (maximalIdeal O ^ m)).mapMatrix (mat y.ρ (g * h)) = _
    rw [map_mul, map_mul]
    rfl
  have c1 : IsLocallyConstant fun g : G0.G₀ => y.ρ0 m g := tw_lc _ fun a b => y.cont a b m
  have e1 : epsm O G0 m ((1 : G0.G₀) : G0.Γ) = 1 := by simp [epsm]
  have em : ∀ g h : G0.G₀, epsm O G0 m ((g * h : G0.G₀) : G0.Γ) = epsm O G0 m g * epsm O G0 m h := by
    intro g h
    simp [epsm]
  have c2 : IsLocallyConstant fun g : G0.G₀ => epsm O G0 m g := by
    have hc : Continuous fun g : G0.G₀ => ((G0.ε g : ℤ_[l]ˣ) : ℤ_[l]) :=
      Units.continuous_val.comp (G0.ε_cont.comp continuous_subtype_val)
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g0
    have ho : IsOpen {a : ℤ_[l] | PadicInt.toZModPow m a = 1} := by
      have : {a : ℤ_[l] | PadicInt.toZModPow m a = 1} = Metric.closedBall 1 ((l : ℝ) ^ (-(m : ℤ))) := by
        ext a
        rw [Set.mem_setOf_eq, Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
          ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero]
      rw [this]
      exact IsUltrametricDist.isOpen_closedBall _ (zpow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))
    have h1 := (ho.preimage (hc.comp (continuous_mul_const g0⁻¹))).mem_nhds (x := g0) (by
      show PadicInt.toZModPow m ((G0.ε ((g0 * g0⁻¹ : G0.G₀) : G0.Γ) : ℤ_[l]ˣ) : ℤ_[l]) = 1
      rw [mul_inv_cancel, OneMemClass.coe_one, map_one, Units.val_one, map_one])
    filter_upwards [h1] with g hg
    have h2 : epsm O G0 m ((g * g0⁻¹ : G0.G₀) : G0.Γ) = 1 := f4 _ hg
    have h3 := em (g * g0⁻¹) g0
    rw [inv_mul_cancel_right, h2, one_mul] at h3
    exact h3
  obtain ⟨U, hU⟩ := tw_U (K := G0.G₀) (fun g => y.ρ0 m g) z (fun g => epsm O G0 m g) r1 r2 e1 em hz c1 c2 cz
  haveI := T.H.isNormal'
  obtain ⟨hn, -, hle, -⟩ := pl_props l G0.Γ T.H.toSubgroup T.H.toOpenSubgroup.isOpen
  have hsub : ∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → g ∈ U := fun g hg => by
    obtain ⟨a1, a2, a3⟩ := plKill l L G0 T O n y m G0 (Glob.Hom.refl G0) hPL z cz hz g hg
    exact (hU g).2 ⟨a2, a3, a1⟩
  obtain ⟨V, v1, v2⟩ := tw_core (U.toSubgroup.map G0.η.ker.subtype) (PL l T.H.toSubgroup)
    (G0.η_open.isOpenMap_subtype_val _ U.toOpenSubgroup.isOpen)
    fun a ha => ⟨⟨a, T.H_η a (hle ha)⟩, hsub _ ha, rfl⟩
  filter_upwards [T.ph_lim V j v1] with N hN
  obtain ⟨u, hu, e⟩ := v2 hN
  obtain ⟨u1, u2, u3⟩ := (hU u).1 hu
  have e' : (T.h N).p₀ (T.ph N j) = u * T.sg j := Subtype.ext (eq_mul_inv_iff_mul_eq.1 e).symm
  have hs : epsm O G0 m (T.sg j : G0.Γ) = 1 := by
    have : G0.ε (T.sg j) = 1 := T.sg_mem j
    simp [epsm, this]
  refine ⟨?_, ?_, ?_⟩
  · rw [e']
    exact (r2 _ _).trans (by rw [u1, one_mul])
  · show epsm O G0 m (((T.h N).p₀ (T.ph N j) : G0.G₀) : G0.Γ) = 1
    rw [e', em, u2, hs, one_mul]
  · rw [e', tw_add (K := G0.G₀) (fun g => y.ρ0 m g) z (fun g => epsm O G0 m g) r1 r2 hz u1 u2, u3, zero_add]

theorem UpperTheory.V.Th.phEqO :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (y : Pt G0.frame O n) (m : ℕ), PhiCond G0.Γ l → (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1) → ∀ᶠ N in atTop, ∀ j, y.ρ0 m ((T.h N).p₀ (T.ph N j)) = y.ρ0 m (T.sg j) ∧ epsm O G0 m ((T.h N).p (T.ph N j)) = 1 ∧ ∀ z ∈ Tw y m, z ((T.h N).p₀ (T.ph N j)) = z (T.sg j) := by
  intro l _ L G0 T O _ _ _ _ _ n y m hΦ hPL
  refine Filter.eventually_all.2 fun j => ?_
  have h0 := phEq_one l L G0 T O n y m hPL 0 (IsLocallyConstant.const 0) (fun g h => by simp) j
  have h1 : ∀ᶠ N in atTop, ∀ z ∈ Tw y m, z ((T.h N).p₀ (T.ph N j)) = z (T.sg j) := by
    refine (Filter.eventually_all_finite (finTwO l L G0 O n y m hΦ)).2 fun z hz => ?_
    exact (phEq_one l L G0 T O n y m hPL z hz.1 hz.2.1 j).mono fun N h => h.2.2
  filter_upwards [h0, h1] with N a b
  exact ⟨a.1, a.2.1, b⟩
