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

@[simp]
theorem eq_imp_d_zero {α : Type*} [MyMetricSpace α] (x y : α) (h : x = y) : d x y = 0 := by
  simp [pos_def]
  exact h

end MyMetricSpace


@[ext]
structure MyIsometry {α : Type*} (inst : MyMetricSpace α) where
  func : α → α
  d_preserve : ∀ x y : α, inst.d x y = inst.d (func x) (func y)
--Add line for surjective


namespace MyIsometry


@[simp]
theorem comp_eq_isometry {α : Type*} [M : MyMetricSpace α] (f g : α → α) (hdf : ∀ x y : α, M.d x y = M.d (f x) (f y)) (hdg : ∀ x y : α, M.d x y = M.d (g x) (g y)) :
  ∀ x y : α, M.d x y = M.d ((f ∘ g) x) ((f ∘ g) y) := by
  intro x y
  simp [Function.comp]
  calc M.d x y
    _ = M.d (g x) (g y) := by apply hdg
    _ = M.d (f (g x)) (f (g y)) := by apply hdf

@[simp]
theorem func_inj {α : Type*} [M : MyMetricSpace α] (f : MyIsometry M) (x y : α) (h : f.func x = f.func y) : x = y := by
  apply M.eq_imp_d_zero at h
  rw [←f.d_preserve] at h
  rw [M.pos_def] at h
  exact h

--define inverse function

--define identity function, show it is isometry

def comp {α : Type*} (M : MyMetricSpace α) : MyIsometry M → MyIsometry M → MyIsometry M
  | mk f hdf, mk g hdg => mk (f ∘ g) (comp_eq_isometry f g hdf hdg)
--Modify proof when surjective condition is added

end MyIsometry

--Show isometries form a group
