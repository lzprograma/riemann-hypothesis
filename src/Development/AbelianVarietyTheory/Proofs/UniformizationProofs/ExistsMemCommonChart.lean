module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU
variable {S : Scheme.{0}}

theorem isWt_of_gm {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G} {V : G.left.Opens}
    (u : Γ(G.left, V)ˣ) (χ : X)
    (h : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left), g.left z ∈ V →
      gm ((t ≫ i) * g).left z V u = gm t.left z ⊤ (charUnit S X χ) * gm g.left z V u) :
    IsWt i V u.val χ := by
  intro Z t g h₁ h₂
  apply TopCat.Presheaf.section_ext Z.left.sheaf ⊤
  intro z hz
  have hg : g.left z ∈ V := h₂ trivial
  have hf : ((t ≫ i) * g).left z ∈ V := h₁ trivial
  have ht : t.left z ∈ (⊤ : (splitTorus S X).left.Opens) := trivial
  have key := congrArg Units.val (h Z t g z hg)
  simp only [gm, dite_eq_left hg, dite_eq_left hf, dite_eq_left ht, pullU, MonoidHom.comp_apply, Units.coe_map,
    Units.val_mul] at key
  change Z.left.presheaf.germ ⊤ z hz _ = Z.left.presheaf.germ ⊤ z hz _
  simp only [Scheme.Hom.appLE, CommRingCat.comp_apply, map_mul, TopCat.Presheaf.germ_res_apply]
  exact key

attribute [local instance] SplitExt.free SplitExt.finite

variable {E : SplitExt S} {G : Over S} [GrpObj G]

theorem exists_mem_commonChart (E : SplitExt S) (x : E.B.left) : ∃ j, x ∈ E.chart j := by
  have hk : ∀ k, ∃ a, x ∈ (E.O (E.basis k)).L.U a := by
    intro k
    have hx : x ∈ (⊤ : E.B.left.Opens) := trivial
    rw [← (E.O (E.basis k)).isLB.cover] at hx
    simpa [TopologicalSpace.Opens.mem_iSup] using hx
  choose c hc using hk
  refine ⟨c, ?_⟩
  unfold SplitExt.chart
  rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf]
  exact Set.mem_iInter.2 hc

private theorem gm_res_pullU_eq_gm_comp {Z P Y : Scheme.{0}} (p : Z ⟶ P) (a : P ⟶ Y) {U : Y.Opens} {W : P.Opens}
    (h : W ≤ a ⁻¹ᵁ U) {z : Z} (hz : p z ∈ W) (w : Γ(Y, U)ˣ) :
    gm p z W (res h (pullU a U w)) = gm (p ≫ a) z U w := by
  have hz' : (p ≫ a) z ∈ U := h hz
  ext
  simp only [gm, dite_eq_left hz, dite_eq_left hz', pullU, res, MonoidHom.comp_apply, Units.coe_map]
  erw [← Scheme.Hom.germ_stalkMap_apply p W z hz, TopCat.Presheaf.germ_res_apply,
    Scheme.Hom.germ_stalkMap_apply]
  rfl

private theorem gm_id_pullU_eq_gm {Z P Y : Scheme.{0}} (p : Z ⟶ P) (a : P ⟶ Y) {U : Y.Opens} {z : Z}
    (hz : p z ∈ a ⁻¹ᵁ U) (w : Γ(Y, U)ˣ) :
    gm p z (a ⁻¹ᵁ U) (pullU a U w) = gm (p ≫ a) z U w := by
  have hz' : (p ≫ a) z ∈ U := hz
  ext
  simp only [gm, dite_eq_left hz, dite_eq_left hz', pullU, MonoidHom.comp_apply, Units.coe_map]
  rfl

theorem isWt_coordinate (d : E.GtDatum G) (j : E.ChartIdx) (k : Module.Free.ChooseBasisIndex ℤ E.X) :
    IsWt d.i _ (d.u j k).val (E.basis k) := by
  refine isWt_of_gm (d.u j k) (E.basis k) ?_
  intro Z t g z hz
  have hf : (t ≫ d.i) * g = lift t g ≫ (lift (fst (splitTorus S E.X) G ≫ d.i) (snd (splitTorus S E.X) G) ≫ μ) := by
    show lift (t ≫ d.i) g ≫ μ = _
    rw [← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]
  have hp : (lift t g).left z ∈ (snd (splitTorus S E.X) G).left ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart j) := by
    have e : ((lift t g).left ≫ (snd (splitTorus S E.X) G).left) = g.left := by
      rw [← Over.comp_left, lift_snd]
    show ((lift t g).left ≫ (snd (splitTorus S E.X) G).left) z ∈ d.q.left ⁻¹ᵁ E.chart j
    rw [e]
    exact hz
  have key := congrArg (gm (lift t g).left z _) (d.equiv j k)
  rw [map_mul] at key
  rw [gm_res_pullU_eq_gm_comp (a := (lift (fst (splitTorus S E.X) G ≫ d.i) (snd (splitTorus S E.X) G) ≫ μ).left) _ _ hp,
    gm_id_pullU_eq_gm (a := (snd (splitTorus S E.X) G).left) _ hp] at key
  rw [← Over.comp_left, ← Over.comp_left, lift_snd, ← hf] at key
  rw [key]
  congr 1
  erw [gm_res_pullU_eq_gm_comp (a := (fst (splitTorus S E.X) G).left) _ _ hp]
  rw [← Over.comp_left, lift_fst]

theorem exists_unit_isWt (d : E.GtDatum G) (j : E.ChartIdx) (χ : E.X) :
    ∃ u : Γ(G.left, d.q.left ⁻¹ᵁ E.chart j)ˣ, IsWt d.i _ u.val χ := by
  have hχ : χ ∈ AddSubgroup.closure (Set.range E.basis) := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup, E.basis.span_eq]
    exact Submodule.mem_top
  induction hχ using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact ⟨d.u j k, isWt_coordinate d j k⟩
  | zero => exact ⟨1, by simpa using (isWt_one : IsWt d.i (d.q.left ⁻¹ᵁ E.chart j) 1 0)⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a * b, by simpa using ha.mul hb⟩
  | neg x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨a⁻¹, ha.inv⟩

def TQ.ofGtDatum (d : E.GtDatum G) : TQ G E.X where
  B := E.B
  comm := E.isAbelian.comm
  isAb := E.isAbelian
  q := d.q
  i := d.i
  q_hom := d.q_hom
  i_hom := d.i_hom
  q_flat := d.q_flat
  q_surj := d.q_surjective
  q_affine := d.q_affine
  isKernel := d.isKernel
  loc b χ := by
    obtain ⟨j, hj⟩ := exists_mem_commonChart E b
    exact ⟨E.chart j, hj, exists_unit_isWt d j χ⟩

theorem exists_tq_of_gtDatum :
    ∀ (S : Scheme.{0}) (E : SplitExt S) (G : Over S) [GrpObj G] (Dat : E.GtDatum G), ∃ Q : TQ G E.X, Q.i = Dat.i := by
  intro S E G _ Dat
  exact ⟨TQ.ofGtDatum Dat, rfl⟩

end GlobalTheory.UU
end
