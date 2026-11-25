module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TransPtBase
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.LocalAnalyticSectionCoords
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsImg
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticEighth
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifth
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFourth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticSecond
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticSeventh
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsMultiHomogIdealMap
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionCompatiblePullback
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionMapLocallyAnalytic
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.BlockFnFieldCompLe
public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogOfPullWeight
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticThird
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SameOrbitRefl
import Mathlib.Tactic.Linter.Style

section
@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.BaseForm

variable {K : Type} {ι : K → Type}

def incl (S : K → Prop) : (Σ k : {k // S k}, ι k.1) → (Σ k, ι k) := fun q => ⟨q.1.1, q.2⟩

theorem incl_injective (S : K → Prop) : Function.Injective (incl (ι := ι) S) := by
  rintro ⟨⟨k, hk⟩, i⟩ ⟨⟨k', hk'⟩, i'⟩ h
  simp only [incl, Sigma.mk.inj_iff] at h
  obtain ⟨rfl, h2⟩ := h
  cases h2
  rfl

theorem isMultiHomog_rename_incl [Fintype K] [∀ k, Fintype (ι k)] (S : K → Prop)
    {D : MRing (fun k : {k // S k} => ι k.1)} {a : {k // S k} → ℕ} (hD : IsMultiHomog D a) :
    IsMultiHomog (rename (incl (ι := ι) S) D : MRing ι) (Function.extend Subtype.val a 0) := by
  classical
  intro m hm k
  rw [MvPolynomial.support_rename_of_injective (incl_injective S), Finset.mem_image] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := hm
  by_cases hk : S k
  · have he : Function.extend Subtype.val a 0 k = a ⟨k, hk⟩ := Subtype.val_injective.extend_apply a 0 ⟨k, hk⟩
    rw [he, ← hD m₀ hm₀ ⟨k, hk⟩]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finsupp.mapDomain_apply_of_injective (incl_injective S) m₀ ⟨⟨k, hk⟩, i⟩
  · rw [Function.extend_apply' _ _ _ (by rintro ⟨c, rfl⟩; exact hk c.2), Pi.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨q, hq⟩
    exact hk ((Sigma.mk.inj_iff.mp hq).1 ▸ q.1.2)

theorem mConeMap_rename_incl {Ω Φ : Type} [Field Ω] [Field Φ] [Algebra Ω Φ] (S : K → Prop)
    (x : (Σ k : {k // S k}, ι k.1) → Ω) (y : (Σ k, ι k) → Φ)
    (hy : ∀ q, y (incl S q) = algebraMap Ω Φ (x q)) (D : MRing (fun k : {k // S k} => ι k.1)) :
    mConeMap y (rename (incl (ι := ι) S) D) =
      map (algebraMap Ω Φ) (rename Subtype.val (mConeMap x D)) := by
  induction D using MvPolynomial.induction_on with
  | C r => simp [mConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p q hp =>
    rw [map_mul, map_mul, map_mul, map_mul, map_mul, hp]
    congr 1
    simp only [mConeMap, aeval_X, map_mul, rename_C, rename_X, map_C, map_X, hy] <;> rfl

theorem rename_incl_notMem {Ω Φ : Type} [Field Ω] [Field Φ] [Algebra Ω Φ] (S : K → Prop)
    (x : (Σ k : {k // S k}, ι k.1) → Ω) (y : (Σ k, ι k) → Φ)
    (hy : ∀ q, y (incl S q) = algebraMap Ω Φ (x q)) {D : MRing (fun k : {k // S k} => ι k.1)}
    (hD : D ∉ mCoordIdeal x) : (rename (incl (ι := ι) S) D : MRing ι) ∉ mCoordIdeal y := by
  intro hmem
  apply hD
  have e : mConeMap y (rename (incl (ι := ι) S) D) = 0 := hmem
  rw [mConeMap_rename_incl S x y hy D] at e
  have e2 : rename Subtype.val (mConeMap x D) = 0 :=
    MvPolynomial.map_injective _ (algebraMap Ω Φ).injective (e.trans (map_zero _).symm)
  show mConeMap x D = 0
  exact MvPolynomial.rename_injective _ Subtype.val_injective (e2.trans (map_zero _).symm)

theorem exists_form : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∀ (D : MRing (baseIdx ι M.blk)) (a : NonPluckerBlocks M.blk → ℕ), IsMultiHomog D a → D ∉ mCoordIdeal M.x → ∃ (G : MRing ι) (a' : K → ℕ), IsMultiHomog G a' ∧ G ∉ mCoordIdeal y ∧ ∀ w : (Σ k, ι k) → ℂ, eval w (map (Int.castRingHom ℂ) G) = eval (basePart M.blk w) (map (Int.castRingHom ℂ) D) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv d _ _ D a hD hDx
  refine ⟨rename (incl (ι := ι) fun k => ∀ p, M.blk p ≠ some k) D, Function.extend Subtype.val a 0,
    isMultiHomog_rename_incl _ hD, rename_incl_notMem _ M.x y (fun q => M.y_base q) hDx, fun w => ?_⟩
  rw [map_rename, eval_rename]
  rfl

end GlobalTheory.CompanionTheory.Ar.PB.BaseForm
end
end
end


@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.CovMap GlobalTheory.CompanionTheory.Ar.PB.CovGraph PositivityTheory.Xgp.c_algsq

noncomputable section
namespace PositivityTheory.Xgp.c_sqsys

theorem elim_gen {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type} [∀ k, Fintype (ι k)]
    [∀ k, Fintype (ι' k)] {P : Ideal (MRing ι)} {P' : Ideal (MRing ι')} {n : ℕ} (Pt : Ideal (MRing (Sum.elim ι ι')))
    (hPt : IsArithVar Pt (n + 1)) (hP : IsArithVar P (n + 1)) (h1 : imageZ inlV Pt = P) (h2 : imageZ inrV Pt = P')
    (J : Ideal (MRing ι')) (hJ : IsMultiHomogIdeal J) (hn : ¬ J ≤ P') :
    ∃ (g : MRing ι) (dg : K → ℕ), IsMultiHomog g dg ∧ g ∉ P ∧
      ∀ z w, z ∈ mcPts J → pairV w z ∈ mcPts Pt → eval w (map (Int.castRingHom ℂ) g) = 0 := by
  have hle : ¬ J.map (rename inrV : MRing ι' →ₐ[ℤ] MRing (Sum.elim ι ι')).toRingHom ≤ Pt := by
    rw [Ideal.map_le_iff_le_comap]
    intro h
    exact hn (h2 ▸ h)
  obtain ⟨g, a, hg, hgP, hv⟩ := GroundTheory.Heights₂.Heights.Inter.PullbackEliminationOfVariable.proof K ι (K ⊕ K') (Sum.elim ι ι') Sum.inl inlV Pt
    (J.map (rename inrV : MRing ι' →ₐ[ℤ] MRing (Sum.elim ι ι')).toRingHom) n isBlockMap_inl hPt
    (by rw [h1]; exact hP) (isMultiHomogIdeal_map isBlockMap_inr hJ) hle
  refine ⟨g, a, hg, h1 ▸ hgP, fun z w hzJ hzt => ?_⟩
  have := hv (pairV w z) hzt (mem_mcPts_map hzt.1 fun f hf => by
    have e : (fun p => pairV w z (inrV p)) = z := funext fun p => pairV_inr w z p
    rw [e]
    exact hzJ.2 f hf)
  have e : (fun p => pairV w z (inlV p)) = w := funext fun p => pairV_inl w z p
  rwa [e] at this

theorem pull_gen {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type} [∀ k, Fintype (ι k)]
    [∀ k, Fintype (ι' k)] {P : Ideal (MRing ι)} {P' : Ideal (MRing ι')} {n : ℕ} (Pt : Ideal (MRing (Sum.elim ι ι')))
    (hPt : IsArithVar Pt (n + 1)) (hP' : IsArithVar P' (n + 1)) (h1 : imageZ inlV Pt = P) (h2 : imageZ inrV Pt = P')
    (G : MRing ι) (a : K → ℕ) (hG : IsMultiHomog G a) (hn : G ∉ P) :
    ∃ (g : MRing ι') (dg : K' → ℕ), IsMultiHomog g dg ∧ g ∉ P' ∧
      ∀ z w, pairV w z ∈ mcPts Pt → eval w (map (Int.castRingHom ℂ) G) = 0 →
        eval z (map (Int.castRingHom ℂ) g) = 0 := by
  have hJ : IsMultiHomogIdeal (Ideal.span {G}) :=
    ⟨{G}, fun f hf => ⟨a, (Set.mem_singleton_iff.mp hf) ▸ hG⟩, rfl⟩
  have hle : ¬ (Ideal.span {G}).map (rename inlV : MRing ι →ₐ[ℤ] MRing (Sum.elim ι ι')).toRingHom ≤ Pt := by
    rw [Ideal.map_le_iff_le_comap]
    intro h
    exact hn (h1 ▸ h (Ideal.subset_span rfl))
  obtain ⟨g, a', hg, hgP, hv⟩ := GroundTheory.Heights₂.Heights.Inter.PullbackEliminationOfVariable.proof K' ι' (K ⊕ K') (Sum.elim ι ι') Sum.inr inrV Pt
    ((Ideal.span {G}).map (rename inlV : MRing ι →ₐ[ℤ] MRing (Sum.elim ι ι')).toRingHom) n isBlockMap_inr hPt
    (by rw [h2]; exact hP') (isMultiHomogIdeal_map isBlockMap_inl hJ) hle
  refine ⟨g, a', hg, h2 ▸ hgP, fun z w hzt h0 => ?_⟩
  have := hv (pairV w z) hzt (mem_mcPts_map hzt.1 fun f hf => by
    have e : (fun p => pairV w z (inlV p)) = w := funext fun p => pairV_inl w z p
    rw [e]
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    rw [map_mul, map_mul, h0, mul_zero])
  have e : (fun p => pairV w z (inrV p)) = z := funext fun p => pairV_inr w z p
  rwa [e] at this

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}
variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ'] {y' : (Σ k, ι' k) → Φ'}

variable {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} {τ : Ψ} {a b : Fin N} {k₀ : K} {k₀' : K'} {ca cb : Fin N}
  {d : ℕ}

theorem exists_homog_eval_eq_zero_of_relW (Cv : FlagCover M' M) (S : Sw M τ a b k₀ ca cb) (S' : Sw M' τ a b k₀' ca cb)
    (hy : IsArithVar (mCoordIdeal y) (d + 2)) (hy' : IsArithVar (mCoordIdeal y') (d + 2))
    (J : Ideal (MRing fun o : Option K' => ι' (o.getD k₀'))) (hJ : IsMultiHomogIdeal J)
    (hn : ¬ J ≤ mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X)) :
    ∃ (g : MRing fun o : Option K => ι (o.getD k₀)) (dg : Option K → ℕ), IsMultiHomog g dg ∧
      g ∉ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) ∧
      ∀ z ∈ mcPts (mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X)), z ∈ mcPts J →
        ∀ w ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)), RelW Cv k₀ k₀' z w →
        eval w (map (Int.castRingHom ℂ) g) = 0 := by
  obtain ⟨Pt, hPt, h1, h2, h3⟩ := graph_alt Cv S S' hy hy'
  obtain ⟨g, dg, hg, hgP, hv⟩ := elim_gen Pt hPt (S.arith hy) h1 h2 J hJ hn
  exact ⟨g, dg, hg, hgP, fun z hz hzJ w hw hi => hv z w hzJ (h3 z hz w hw hi)⟩

theorem pull_alt (Cv : FlagCover M' M) (S : Sw M τ a b k₀ ca cb) (S' : Sw M' τ a b k₀' ca cb)
    (hy : IsArithVar (mCoordIdeal y) (d + 2)) (hy' : IsArithVar (mCoordIdeal y') (d + 2))
    (G : MRing fun o : Option K => ι (o.getD k₀)) (dG : Option K → ℕ) (hG : IsMultiHomog G dG)
    (hn : G ∉ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) :
    ∃ (g : MRing fun o : Option K' => ι' (o.getD k₀')) (dg : Option K' → ℕ), IsMultiHomog g dg ∧
      g ∉ mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X) ∧
      ∀ z ∈ mcPts (mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X)),
        ∀ w ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)), RelW Cv k₀ k₀' z w →
        eval w (map (Int.castRingHom ℂ) G) = 0 → eval z (map (Int.castRingHom ℂ) g) = 0 := by
  obtain ⟨Pt, hPt, h1, h2, h3⟩ := graph_alt Cv S S' hy hy'
  obtain ⟨g, dg, hg, hgP, hv⟩ := pull_gen Pt hPt (S'.arith hy') h1 h2 G dG hG hn
  exact ⟨g, dg, hg, hgP, fun z hz w hw hi h0 => hv z w (h3 z hz w hw hi) h0⟩

theorem sameOrbit_of_relW_relW (Cv : FlagCover M' M) (S' : Sw M' τ a b k₀' ca cb)
    (hy : IsArithVar (mCoordIdeal y) (d + 2)) (hy' : IsArithVar (mCoordIdeal y') (d + 2))
    {z : (Σ o : Option K', ι' (o.getD k₀')) → ℂ} (hz : z ∈ mcPts (mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X)))
    {w w' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : RelW Cv k₀ k₀' z w) (h' : RelW Cv k₀ k₀' z w') :
    SameOrbit w w' :=
  sameOrbit_of_sameOrbit_fstPt_sndPt (_root_.GlobalTheory.CompanionTheory.Ar.PB.CovMap.isImg_unique K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' _ (fst_mem hz) _ _ h.1 h'.1)
    (_root_.GlobalTheory.CompanionTheory.Ar.PB.CovMap.isImg_unique K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' _ (S'.snd_mem hy' hz) _ _ h.2 h'.2)

theorem pull_form (S : Sw M τ a b k₀ ca cb) (hy : IsArithVar (mCoordIdeal y) (d + 2)) {G : MRing ι} {dG : K → ℕ}
    (hG : IsMultiHomog G dG) (hn : G ∉ mCoordIdeal y) :
    ∃ (g : MRing fun o : Option K => ι (o.getD k₀)) (dg : Option K → ℕ), IsMultiHomog g dg ∧
      g ∉ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) ∧
      ∀ w, eval w (map (Int.castRingHom ℂ) g) = eval (fstPt k₀ w) (map (Int.castRingHom ℂ) G) :=
  ⟨rename (v₀ k₀) G, _, CPts.isMultiHomog_rename_block (Pts.isBlockMap_v₀ k₀) hG,
    fun h => hn (by rw [← S.im₀ hy]; exact h), fun w => CPts.eval_rename_block _ w G⟩

theorem mapsTo_twoFlagFramesOrthogonal_of_isometry (hRes : ResExistsStatement) (Cv : FlagCover M' M) (S : Sw M τ a b k₀ ca cb) (S' : Sw M' τ a b k₀' ca cb)
    (hy : IsArithVar (mCoordIdeal y) (d + 2)) (hy' : IsArithVar (mCoordIdeal y') (d + 2))
    {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas (d + 2) X)
    (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (e : RW.X → X)
    (he : HoloMap RW.A A e) (hdeg : IsDegreeOff A RW.A e 1 ∅) :
    ∃ (J : Ideal (MRing fun o : Option K' => ι' (o.getD k₀')))
      (R' : AnLogRes (mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X)) J (d + 2)) (g : R'.X → RW.X) (br : Set X),
      HoloMap R'.A RW.A g ∧ IsDegreeOff A R'.A (e ∘ g) Cv.deg br ∧
        ∀ x, RelW Cv k₀ k₀' (R'.lift x x) (RW.lift (g x) (g x)) := by
  have hP := S.arith hy
  have hP' := S'.arith hy'
  have heinj : Function.Injective e := by
    intro u v huv
    obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 (hdeg.2.2.2.2.1 (e u) (by simp))
    have hu : u ∈ e ⁻¹' {e u} := rfl
    have hv : v ∈ e ⁻¹' {e u} := huv.symm
    rw [hc] at hu hv
    exact hu.trans hv.symm
  have hnot : ∀ z : (Σ o : Option K, ι (o.getD k₀)) → ℂ, z ∉ mcPts ⊤ := by
    intro z h
    have := h.2 1 trivial
    simp at this
  have htop : IsMultiHomogIdeal (⊤ : Ideal (MRing fun o : Option K' => ι' (o.getD k₀'))) := by
    refine ⟨{1}, fun f hf => ⟨0, ?_⟩, by simp⟩
    rw [Set.mem_singleton_iff.mp hf]
    intro m hm k
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    simp [hm]
  obtain ⟨J', -, hJ'h, hJ'n, ⟨R'⟩⟩ := hRes _ _ _ ⊤ (d + 2) hP' htop fun h => hP'.2.1.1.ne_top (top_le_iff.mp h)
  have hmem' : ∀ x, R'.lift x x ∈ mcPts _ := fun x => R'.mem x x (R'.mem_U x)
  have hmem : ∀ x, RW.lift x x ∈ mcPts _ := fun x => RW.mem x x (RW.mem_U x)
  have himg : ∀ x, ∃ x₀, RelW Cv k₀ k₀' (R'.lift x x) (RW.lift x₀ x₀) := by
    intro x
    obtain ⟨V, f, -, hzV, -, hf⟩ := local_analytic_section_coords Cv S S' hy' (hmem' x)
    obtain ⟨h1, h2⟩ := hf _ ⟨hzV, hmem' x⟩
    obtain ⟨x₀, hx⟩ := RW.surj _ h1 (hnot _)
    exact ⟨x₀, h2.orbit (Cj.sameOrbit_refl _) hx⟩
  choose g hg using himg
  have hgholo : HoloMap R'.A RW.A g := by
    refine _root_.GlobalTheory.CompanionTheory.Ar.PB.CovMap.holoMap_of_local_analytic _ _ _ _ _ ⊤ _ J' (d + 2) (d + 2) RW R' g rfl fun x => ?_
    obtain ⟨V, f, hV, hzV, hf, hff⟩ := local_analytic_section_coords Cv S S' hy' (hmem' x)
    refine ⟨V, f, hV, hzV, hf, fun z' hz' x' hx' => ?_⟩
    exact sameOrbit_of_relW_relW Cv S' hy hy' hz'.2 (hff z' hz').2 ((hg x').orbit hx' (Cj.sameOrbit_refl _))
  have hholo : HoloMap R'.A A (e ∘ g) := holoMap_comp hgholo he
  have hbase := _root_.GlobalTheory.CompanionTheory.Ar.PB.CovMap.ImgBase.img_lies_over K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy'
  obtain ⟨D₁, a₁, hD₁, hD₁n, hcount⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.BaseCount.base_count K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy'
  obtain ⟨E₁, b₁, hE₁, hE₁n, hE₁e⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.BaseForm.exists_form K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' D₁ a₁ hD₁ hD₁n
  obtain ⟨G₁, c₁, hG₁, hG₁n, hG₁e⟩ := pull_form S hy hE₁ hE₁n
  obtain ⟨D₂, a₂, hD₂, hD₂n, het⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.BaseEtale.main K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy'
  obtain ⟨E₂, b₂, hE₂, hE₂n, hE₂e⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.BaseForm.exists_form K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' D₂ a₂ hD₂ hD₂n
  obtain ⟨G₂, c₂, hG₂, hG₂n, hG₂e⟩ := pull_form S hy hE₂ hE₂n
  obtain ⟨G₃, c₃, hG₃, hG₃n, hG₃e⟩ := exists_homog_eval_eq_zero_of_relW Cv S S' hy hy' J' hJ'h hJ'n
  have hprime := hP.2.1.1
  have hGn : G₁ * G₂ * G₃ ∉ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) := fun h => by
    rcases hprime.mem_or_mem h with h | h
    · rcases hprime.mem_or_mem h with h | h
      · exact hG₁n h
      · exact hG₂n h
    · exact hG₃n h
  have hGh : IsMultiHomog (G₁ * G₂ * G₃) (c₁ + c₂ + c₃) :=
    CovMap.isMultiHomog_mul (CovMap.isMultiHomog_mul hG₁ hG₂) hG₃
  obtain ⟨G₄, c₄, hG₄, hG₄n, hG₄e⟩ := pull_alt Cv S S' hy hy' _ _ hGh hGn
  have hev : ∀ w : (Σ o : Option K, ι (o.getD k₀)) → ℂ, eval w (map (Int.castRingHom ℂ) (G₁ * G₂ * G₃)) ≠ 0 →
      eval w (map (Int.castRingHom ℂ) G₁) ≠ 0 ∧ eval w (map (Int.castRingHom ℂ) G₂) ≠ 0 := by
    intro w hw
    simp only [map_mul] at hw
    exact ⟨fun h => hw (by rw [h]; simp), fun h => hw (by rw [h]; simp)⟩
  refine ⟨J', R', g, _, hgholo, _root_.GlobalTheory.CompanionTheory.Ar.PB.CovMap.Deg.isDegreeOff_of_correspondence _ _ _ _ _ ⊤ _ J' (d + 2) X A RW e R' _ (RelW Cv k₀ k₀')
    (G₁ * G₂ * G₃) G₄ _ c₄ Cv.deg rfl hP hP' he hdeg hholo hGh hGn hG₄ hG₄n
    (fun z z₁ w w₁ h h1 h2 => h.orbit h1 h2) ?_ ?_ ?_ ?_ (fun z hz w hw hi h0 => hG₄e z hz w hw hi h0) ?_, hg⟩
  · intro x x₀ h
    rw [heinj h]
    exact hg x
  · intro x x₀ h
    rw [RW.inj x₀ (g x) (hnot _) (sameOrbit_of_relW_relW Cv S' hy hy' (hmem' x) h (hg x))]
    rfl
  · intro w hw h0
    rw [ncard_orbits_relW_eq_ncard_orbits_isImg Cv S S' hy hy' hw, _root_.GlobalTheory.CompanionTheory.Ar.PB.FibreCount.fibre_count K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' _ (fst_mem hw)]
    refine hcount _ (CPts.base_mem M (fst_mem hw)) ?_
    rw [← hE₁e, ← hG₁e]
    exact (hev w h0).1
  · intro z hz hzJ w hw hi
    have := hG₃e z hz hzJ w hw hi
    simp only [map_mul, this, mul_zero]
  · intro z hz w₀ hw₀ hi h0
    have hs := hbase _ (fst_mem hz) _ hi.1
    have h2 : eval (basePart M.blk (fstPt k₀ w₀)) (map (Int.castRingHom ℂ) D₂) ≠ 0 := by
      rw [← hE₂e, ← hG₂e]
      exact (hev w₀ h0).2
    obtain ⟨V, V', s, hV, hwV, hV', hbV, hs1, hs2⟩ := het _ (CPts.base_mem M' (fst_mem hz)) _ hs h2
    obtain ⟨U₀, U₀', f₀, hU₀, hw0, hU₀', hz0, hf₀, r₀⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.CovLift.lift_inverse K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' _
      (fst_mem hz) _ (fst_mem hw₀) hi.1 V V' s hV hwV hV' hbV hs1 hs2
    obtain ⟨U₁, U₁', f₁, hU₁, hw1, hU₁', hz1, hf₁, r₁⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.CovLift.lift_inverse K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' _
      (S'.snd_mem hy' hz) _ (S.snd_mem hy hw₀) hi.2 V V' s hV (by rw [Pts.basePart_snd M S.hk]; exact hwV) hV'
      (by rw [Pts.basePart_snd M' S'.hk]; exact hbV) hs1 hs2
    refine ⟨fstPt k₀ ⁻¹' U₀ ∩ sndPt k₀ ⁻¹' U₁, fstPt k₀' ⁻¹' U₀' ∩ sndPt k₀' ⁻¹' U₁',
      fun u => joinPt k₀' (f₀ (fstPt k₀ u)) (f₁ (sndPt k₀ u)),
      (hU₀.preimage (continuous_comp_idx _)).inter (hU₁.preimage (continuous_comp_idx _)), ⟨hw0, hw1⟩,
      (hU₀'.preimage (continuous_comp_idx _)).inter (hU₁'.preimage (continuous_comp_idx _)), ⟨hz0, hz1⟩,
      fun u hu => analytic_join k₀' ((hf₀ _ hu.1).comp (analytic_comp_idx _ u))
        ((hf₁ _ hu.2).comp (analytic_comp_idx _ u)), fun z'' hz'' w hw hr => ?_⟩
    exact join_orbit (r₀ _ ⟨hz''.1.1, fst_mem hz''.2⟩ _ ⟨hw.1.1, fst_mem hw.2⟩ hr.1)
      (r₁ _ ⟨hz''.1.2, S'.snd_mem hy' hz''.2⟩ _ ⟨hw.1.2, S.snd_mem hy hw.2⟩ hr.2)

end PositivityTheory.Xgp.c_sqsys
