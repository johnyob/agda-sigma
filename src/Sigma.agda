
data Term (V : Set) : Set where
  App : Term V -> Term V -> Term V
  Abs : (V -> Term V) -> Term V -- ouch, posititity.