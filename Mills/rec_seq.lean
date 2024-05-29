-- 途中から数列を作る練習。

def a : Nat → Nat
  | 0 => 1
  | n + 1 => a n + 1

-- p n = p' (n + m)となるようにしたい。
-- p' m = p 0として作る
-- p' n がP nを満たすことは、p (n - m)がP nを満たすことで保証される。
-- ただ、相対的な関係しか出てこないならあまり気にしないでいい？生のnが出てくることは？
def p : Nat → Nat
  | 0 => 1
  | n + 1 => p n + 2

-- 各項がある性質を満たすように撮りたい。
-- p n が n に依存した条件 P n を満たすことを保証したい。

def p' (m : Nat) : Nat → Nat := λ n => if n ≤ m then a n else p (n - m)

#eval a 2
#eval p 2
#eval p' 2 2
#eval p' 2 3
