
debug let rec test (f,(x,ll)) =
  (f x, test (f,ll))

