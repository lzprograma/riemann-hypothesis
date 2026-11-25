module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FinitePartPreservesFormDetNormOneStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralTmulOneMulMemAdelicCompletion
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem halfVec_mem_latHat {D : D7} (V : HSp D) (b : 𝓞 D.host.E)
    (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) (hz : z ∈ latHat V) :
    halfVec V b z ∈ latHat V := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨a, ha, b • x, V.L0.smul_mem b hx, ?_⟩
    funext i
    have e : b • x = (b : D.host.E) • x := (algebraMap_smul D.host.E b x).symm
    simp only [halfVec, Algebra.TensorProduct.tmul_mul_tmul, one_mul, e, map_smul,
      Finsupp.smul_apply, smul_eq_mul]
  | zero =>
    have : halfVec V b 0 = 0 := by funext i; simp [halfVec]
    rw [this]; exact zero_mem _
  | add w w' _ _ h h' =>
    have : halfVec V b (w + w') = halfVec V b w + halfVec V b w' := by
      funext i; simp only [halfVec, Pi.add_apply, mul_add]
    rw [this]; exact add_mem h h'
  | neg w _ h =>
    have : halfVec V b (-w) = - halfVec V b w := by
      funext i; simp only [halfVec, Pi.neg_apply, mul_neg]
    rw [this]; exact neg_mem h

theorem finCong_iff_half (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (V : HSp D)
    (k : GA D V) :
    FinCong V l.M k ↔ ∀ b ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E), ∀ z ∈ latHat V,
      ∃ y ∈ latHat V, (finHom V k).1.mulVec (halfVec V b z) - halfVec V b z = l.M • y := by
  refine ⟨fun h b _ z hz => h _ (halfVec_mem_latHat V b z hz), fun h => ?_⟩
  obtain ⟨h1, -, h3, h4, h5, h6, -, h8, h9, -, h11⟩ := latHat_eq_hat_and_gram D V
  unfold FinCong
  rw [h1] at h ⊢
  refine GlobalTheory.AdLat.trivial_level_of_half D.host.F D.host.E V.rank (latC V) (cF D) V.gramᵀ 1
    (finHom V k) l.M (l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) l.Mb h3 h4 h5 h8 h9
    one_ne_zero h11 (GlobalTheory.T.finitePart_preserves_form_det_norm_one D V k).1 (lt_of_lt_of_le (by norm_num) l.three_le)
    (by rw [sup_comm]; exact l.coprime) (by rw [mul_comm]; exact l.prod) ?_ h
  intro b hb
  refine ⟨H.bar b, Ideal.mem_map_of_mem _ hb, ?_⟩
  rw [h6]
  exact H.bar_eq b

theorem finCong_iff_half_and_kfHalf : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (V : HSp D), (∀ k : GA D V, FinCong V l.M k ↔ ∀ b ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E), ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec (halfVec V b z) - halfVec V b z = l.M • y) ∧ ∀ Kf : Subgroup (GA D V), IsLevelK V l.M Kf → KfHalf V Kf l.M (l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) := by
  intro D H l V
  refine ⟨finCong_iff_half D H l V, fun Kf hK k => ?_⟩
  rw [hK k]
  exact and_congr_right fun _ => finCong_iff_half D H l V k

end GlobalTheory.Member
