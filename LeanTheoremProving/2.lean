def α : Type := Nat
def β : Type := Nat
def G : Type → Type → Type := Prod
#check G α β
#check Type
#check Type 2
#check Type 3

#check List
#check Prod -- Type (max u v) max type level of u and v

universe u
def F (α: Type u): Type u := Prod α α
#check F

section useful
  variable (α β γ : Type)
  variable (g : β → γ) (f : α → β) (h : α → α)
  variable (x : α)

  def compose := g (f x)
  def doTwice := h (h x)
  def doThrice := h (h (h x))
end useful

namespace Foo
  def a : Nat := 5
  def f (x : Nat) : Nat := x + 7

  def fa : Nat := f a
  def ffa : Nat := f (f a)

  #check a
  #check f
  #check fa
  #check ffa
  #check Foo.fa
end Foo

-- #check a  -- error
-- #check f  -- error
#check Foo.a
#check Foo.f
#check Foo.fa
#check Foo.ffa

open Foo

#check a
#check f
#check fa
#check Foo.fa

-----

def cons (α: Type) (a: α) (as: List α) : List α :=
  List.cons a as
#check cons
#check List.cons
