inductive T where
| Leaf : Int → T
| Branch : T → T → T
| Branch2 : T → T → T

open T

def t: T → T → Option (List Int)
| T.Leaf a, T.Leaf b => if a == b then some [a] else none
| T.Branch b11 b12, T.Branch b21 b22 => do
  let a <- t b11 b21
  let b <- t b12 b22
  a ++ b
| T.Branch2 b11 b12, T.Branch2 b21 b22 => do
  let a <- t b11 b21
  let b <- t b12 b22
  a ++ b
| _, _ => none


def a: T := Branch (Leaf 2) (Leaf 3)
def b: T := Branch (Leaf 2) (Leaf 4)

