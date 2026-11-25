module

public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Algebra.Order.Archimedean.Real.Hom

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.AdelicRealLine

theorem norm_eq_abs_ringEquiv {F : Type} [Field F] {w : InfinitePlace F} (hw : w.IsReal)
    (x : w.Completion) :
    ‖x‖ = |InfinitePlace.Completion.ringEquivRealOfIsReal hw x| := by
  rw [← Real.norm_eq_abs, InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
  exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
    (map_zero _) x).symm

theorem exists_continuous_real_embedding :
    ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
      (∃ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ) ∧
        ∀ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ →
          ∀ (t : ℝ) (w : InfinitePlace F), ‖θ t w‖ = |t| := by
  intro F _ _ hF
  have hr : ∀ w : InfinitePlace F, w.IsReal := fun w => @IsTotallyReal.isReal F _ hF w
  refine ⟨⟨Pi.ringHom fun w =>
    (InfinitePlace.Completion.ringEquivRealOfIsReal (hr w)).symm.toRingHom, ?_⟩, ?_⟩
  · refine continuous_pi fun w => ?_
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal (hr w)).symm.continuous
  · intro θ _ t w
    have hφ := DFunLike.congr_fun (Subsingleton.elim
      (((InfinitePlace.Completion.ringEquivRealOfIsReal (hr w)).toRingHom.comp
        ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp θ)) : ℝ →+* ℝ)
      (RingHom.id ℝ)) t
    change InfinitePlace.Completion.ringEquivRealOfIsReal (hr w) (θ t w) = t at hφ
    rw [GlobalTheory.CompanionTheory.AdelicRealLine.norm_eq_abs_ringEquiv (hr w), hφ]

end GlobalTheory.CompanionTheory.AdelicRealLine
