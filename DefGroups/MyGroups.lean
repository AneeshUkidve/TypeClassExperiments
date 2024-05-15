import Mathlib

class MyGroup (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α

  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ g : α, mul g one = g
  one_mul : ∀ g : α, mul one g = g
  inv_left_mul : ∀ g : α, mul (inv g) g = one

instance hasMulMyGroup {α : Type*} [MyGroup α] : Mul α where
  mul := MyGroup.mul

instance hasOneMyGroup {α : Type*} [MyGroup α] : One α where
  one := MyGroup.one

instance hasInvMyGroup {α : Type*} [MyGroup α] : Inv α where
  inv := MyGroup.inv

namespace MyGroup

/-
theorem inv_inv_one {α : Type*} [G : MyGroup α] : ∀ g : α, (g⁻¹)⁻¹ = g := by
  intro g
  have h : g⁻¹⁻¹ * g⁻¹ = 1 := by exact inv_left_mul g⁻¹
  calc g⁻¹⁻¹
    _ = mul g⁻¹⁻¹ one := by simp [mul_one g⁻¹⁻¹]
    _ = mul g⁻¹⁻¹ (mul g⁻¹ g) := by rw [inv_left_mul g]
    _ = g⁻¹⁻¹ * g⁻¹ * g := by rw [mul_assoc]
    _ = 1 * g := by rw [h]
    _ = g := by rw [one_mul]
-/

end MyGroup
