import Mathlib

class MyGroup (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α

  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ g : α, mul g one = g
  one_mul : ∀ g : α, mul one g = g
  inv_right_mul : ∀ g : α, mul g (inv g) = one

instance hasMulMyGroup {α : Type*} [MyGroup α] : Mul α where
  mul := MyGroup.mul

instance hasOneMyGroup {α : Type*} [MyGroup α] : One α where
  one := MyGroup.one

instance hasInvMyGroup {α : Type*} [MyGroup α] : Inv α where
  inv := MyGroup.inv
