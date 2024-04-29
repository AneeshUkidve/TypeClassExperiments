import Mathlib
import DefGroups.MyGroups

class MyMetricSpace (α : Type*) where
  d : α → α → ℝ
  pos_def : ∀ x y : α, (d x y) = 0 ↔ x = y
  symm : ∀ x y : α, (d x y) = (d y x)
  triangle : ∀ x y z : α, (d x z) ≤ (d x y) + (d y z)

namespace MyMetricSpace
@[simp]
theorem d_nonneg {α : Type*} [MyMetricSpace α] : ∀ x y : α, 0 ≤ (d x y) := by
  intro x y
  rename_i inst
  have h1 : d x x = 0 := by
    simp [inst.pos_def]
  suffices h : d x x ≤ 2 * (d x y)
  rw [h1] at h
  simp at h
  exact h
  have h2 : d x x ≤ d x y + d y x := by
    exact inst.triangle x y x
  simp [inst.symm] at h2
  ring_nf at h2
  ring_nf
  exact h2

end MyMetricSpace

@[ext]
structure MyIsometry {α : Type*} (inst : MyMetricSpace α) where
  func : α → α
  d_preserve : ∀ x y : α, inst.d x y = inst.d (func x) (func y)

namespace MyIsometry

@[simp]
theorem comp_eq_isometry {α : Type*} (M : MyMetricSpace α) (f g : α → α) (hf : ∀ x y : α, M.d x y = M.d (f x) (f y)) (hg : ∀ x y : α, M.d x y = M.d (g x) (g y)) :
  ∀ x y : α, M.d x y = M.d ((f ∘ g) x) ((f ∘ g) y) := by
  intro x y
  simp [Function.comp]
  calc M.d x y
    _ = M.d (g x) (g y) := by apply hg
    _ = M.d (f (g x)) (f (g y)) := by apply hf

def comp {α : Type*} (M : MyMetricSpace α) : MyIsometry M → MyIsometry M → MyIsometry M
  | MyIsometry.mk f hf, MyIsometry.mk g hg => MyIsometry.mk (f ∘ g) (comp_eq_isometry M f g hf hg)

end MyIsometry
